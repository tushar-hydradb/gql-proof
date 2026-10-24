//! One probe per checker rule string the other suites do not reach: each red on a violating
//! input and, where the shape allows, green on a valid one. `tools/inventory/audit.py` requires
//! every rule string the audit relies on to have a probe in `tests/`.

use gql_proof::bnf;
use gql_proof::cfg::Cfg;
use gql_proof::parse::Parser;
use gql_proof::tokens::Grammar;
use gql_proof::verify::{Plain, Verifier, scope, types};
use gql_proof::{ISO_BNF_XML, MatchModeDefault};
use std::cell::RefCell;
use std::sync::LazyLock;

static ISO_BNF: LazyLock<bnf::Bnf> = LazyLock::new(|| bnf::parse(ISO_BNF_XML).unwrap());
static ISO: LazyLock<Cfg> = LazyLock::new(|| Cfg::from_bnf(&ISO_BNF));

fn verifier() -> Verifier<'static> {
    Verifier::new(Grammar::new(&ISO_BNF)).with_syntax_rules(MatchModeDefault::Portable)
}

/// The rules the verifier reports on a hand-built tree, the ISO BNF left aside.
fn tree_rules(tree: &Plain) -> Vec<&'static str> {
    let v = verifier();
    v.verify(tree, &v.render(tree))
        .into_iter()
        .map(|x| x.rule)
        .filter(|r| *r != "ISO BNF" && *r != "21.3 SR 13, 14")
        .collect()
}

fn leaf(def: &str, text: &str) -> Plain {
    Plain::Def {
        name: "leaf holder".into(),
        synthetic: false,
        children: vec![Plain::Leaf { def: def.into(), text: text.into() }],
    }
}

fn token(def: &str, text: &str) -> Plain {
    Plain::Def {
        name: def.into(),
        synthetic: false,
        children: vec![Plain::Term(text.into())],
    }
}

#[track_caller]
fn red(tree: Plain, rule: &str) {
    let r = tree_rules(&tree);
    assert!(r.contains(&rule), "{}: expected {rule}, got {r:?}", tree.text());
}

#[track_caller]
fn green(tree: Plain, rule: &str) {
    let r = tree_rules(&tree);
    assert!(!r.contains(&rule), "{}: {rule} reported: {r:?}", tree.text());
}

#[test]
fn leaves() {
    red(leaf("identifier extend", "-"), "21.3 SR 2");
    green(leaf("identifier extend", "b"), "21.3 SR 2");
    red(leaf("whitespace", "x"), "21.3 SR 6");
    green(leaf("whitespace", " "), "21.3 SR 6");
    red(leaf("simple comment character", "\n"), "21.3 SR 9");
    green(leaf("simple comment character", "x"), "21.3 SR 9");
    red(leaf("bracketed comment contents", "a*/b"), "21.3 SR 10");
    green(leaf("bracketed comment contents", "ab"), "21.3 SR 10");
    red(leaf("other digit", "3"), "21.4 SR 2");
    green(leaf("other digit", "\u{0663}"), "21.4 SR 2");
    red(leaf("character representation", "'"), "21.2 SR 31-33, 41");
    red(leaf("character representation", "\u{0378}"), "21.2 SR 31-33, 41");
    green(leaf("character representation", "x"), "21.2 SR 31-33, 41");
    red(leaf("external object reference", "http://x"), "17.8 SR 2, 3");
    green(leaf("external object reference", "urn:x"), "17.8 SR 2, 3");
    red(leaf("SQL-datetime literal", "DATE '2024-13-01'"), "21.2 SR 69");
    green(leaf("SQL-datetime literal", "DATE '2024-01-01'"), "21.2 SR 69");
    red(leaf("SQL-interval literal", "INTERVAL 'x' DAY"), "21.2 SR 70");
    green(leaf("SQL-interval literal", "INTERVAL '1' DAY"), "21.2 SR 70");
}

#[test]
fn identifier_characters() {
    // 21.3 SR 5 c, d: no format character, no space separator but the space.
    red(token("regular identifier", "a\u{2003}b"), "21.3 SR 5");
    red(token("regular identifier", "a\u{200B}b"), "21.3 SR 5");
    green(token("regular identifier", "ab"), "21.3 SR 5");
}

#[test]
fn unreachable_leaves_are_checked() {
    // 21.3 SR 8, 21.4 SR 1: no production reaches them, the leaf rules still say what they are.
    red(leaf("bidirectional control character", "x"), "21.3 SR 8");
    green(leaf("bidirectional control character", "\u{2068}"), "21.3 SR 8");
    red(leaf("other language character", "a"), "21.4 SR 1");
    green(leaf("other language character", "\u{00E9}"), "21.4 SR 1");
}

/// 21.2 SR 42: no production of the ISO grammar references <escaped character>, so no tree
/// holds one (its rule is vacuous for every tree).
#[test]
fn escaped_character_is_unreachable() {
    for p in &ISO.prods {
        for sym in &p.rhs {
            if let gql_proof::cfg::Sym::Nt(nt) = sym {
                assert_ne!(ISO.base(*nt), "escaped character", "{}", gql_proof::describe(&ISO, 0));
            }
        }
    }
}

#[test]
fn literal_elements() {
    // A list text derives as a <list literal> and as a <list value constructor>; the literal's
    // tree is the one SR 73 judges.
    let some = |text: &str, rule: &str| verdicts(text).iter().any(|r| r.contains(&rule));
    assert!(some("LET y = 1 RETURN [y] AS x", "21.2 SR 73"));
    assert!(!some("RETURN [1, -2, 'a', NULL, [TRUE]] AS x", "21.2 SR 73"));
    assert!(some("LET y = 1 RETURN {a: y} AS x", "21.2 SR 75"));
    assert!(!some("RETURN {a: 1, b: 'x'} AS x", "21.2 SR 75"));
}

#[test]
fn temporal_tokens() {
    red(token("time zone string", "'+25:00'"), "21.2 SR 61");
    green(token("time zone string", "'+01:00'"), "21.2 SR 61");
    red(token("datetime string", "'2024-01-01'"), "21.2 SR 64");
    green(token("datetime string", "'2024-01-01T12:00:00'"), "21.2 SR 64");
}

/// The rules every parse of `text` breaks under the syntax rules, scope and types.
fn verdicts(text: &str) -> Vec<Vec<&'static str>> {
    let tokens = Grammar::new(&ISO_BNF);
    let v = verifier();
    let mut parser = Parser::new(&ISO, &tokens, "GQL-program").unwrap();
    parser.limit = 2048;
    let out = RefCell::new(Vec::new());
    parser
        .parse(text, |n| {
            let plain = n.export(&ISO);
            let mut rules: Vec<&'static str> =
                v.verify(&plain, &n.render(&ISO)).into_iter().map(|x| x.rule).collect();
            if !rules.contains(&"ISO BNF") {
                rules.extend(scope::check(&plain).into_iter().map(|x| x.rule));
                rules.extend(types::check(&plain).into_iter().map(|x| x.rule));
                out.borrow_mut().push(rules);
            }
            false
        })
        .unwrap_or_else(|e| panic!("{text:?}: {e}"));
    let out = out.into_inner();
    assert!(!out.is_empty(), "{text:?} has no parse");
    out
}

#[track_caller]
fn bad(text: &str, rule: &str) {
    let v = verdicts(text);
    assert!(v.iter().all(|r| r.contains(&rule)), "{text:?}: some parse does not report {rule}: {v:?}");
}

#[track_caller]
fn fine(text: &str, rule: &str) {
    let v = verdicts(text);
    assert!(v.iter().any(|r| !r.contains(&rule)), "{text:?}: every parse reports {rule}");
}

#[test]
fn definitions_twice() {
    bad("GRAPH g = CURRENT_PROPERTY_GRAPH GRAPH g = CURRENT_PROPERTY_GRAPH FINISH", "10.1 SR 7");
    fine("GRAPH g = CURRENT_PROPERTY_GRAPH GRAPH h = CURRENT_PROPERTY_GRAPH FINISH", "10.1 SR 7");
    bad("TABLE t = a TABLE t = a FINISH", "10.2 SR 7");
    fine("TABLE t = a TABLE u = a FINISH", "10.2 SR 7");
}

#[test]
fn table_expressions() {
    bad("TABLE t = { FINISH } FINISH", "11.2 SR 2");
    bad("TABLE t = VARIABLE 1 FINISH", "11.2 SR 4");
}

#[test]
fn modification_targets() {
    bad("LET x = 1 REMOVE x.a", "13.4 SR 3");
    bad("LET x = 1 SET x.a = 2", "13.3 SR 3");
    fine("MATCH (x) REMOVE x.a", "13.4 SR 3");
    bad("LET x = 1 DELETE x", "13.5 SR 5");
    fine("MATCH (x) DELETE x", "13.5 SR 5");
}

#[test]
fn element_predicates_take_singletons() {
    bad("MATCH (a)-[e]->{1,2}(b) FILTER a IS SOURCE OF e RETURN a", "19.10 SR 2-3");
    bad("MATCH (a)-[e]->{1,2}(b) FILTER ALL_DIFFERENT(e, e) RETURN a", "19.11 SR 2");
    bad("MATCH (a)-[e]->{1,2}(b) FILTER SAME(e, e) RETURN a", "19.12 SR 2");
    bad("MATCH (a)-[e]->{1,2}(b) FILTER PROPERTY_EXISTS(e, k) RETURN a", "19.13 SR 2");
    fine("MATCH (a)-[e]->(b) FILTER SAME(e, e) RETURN a", "19.12 SR 2");
}

#[test]
fn aggregates() {
    bad("RETURN COUNT(COUNT(*)) AS x", "20.9 SR 4");
    // Simply contained through a subquery: no aggregate intervenes.
    bad("RETURN MAX(VALUE { RETURN count(*) AS y }) AS x", "20.9 SR 4");
    fine("RETURN COUNT(*) AS x", "20.9 SR 4");
    bad("MATCH (a) FILTER COUNT(*) > 0 RETURN a", "20.9 SR 7");
    fine("RETURN COUNT(*) AS x", "20.9 SR 7");
}

#[test]
fn confusable_names_under_h2() {
    bad("LET rn = 1 LET m = 2 RETURN rn + m AS x", "6 SR 4");
    fine("LET y = 1 LET z = 2 RETURN y + z AS x", "6 SR 4");
}

#[test]
fn result_statements_agree_in_a_block() {
    bad(
        "SELECT * FROM { USE CURRENT_PROPERTY_GRAPH RETURN 1 AS a } NEXT SELECT a AS b",
        "9.2 SR 7",
    );
}

#[test]
fn nothing_is_known_not_nullable() {
    // 18.9 SR 4 b, SR 88: NOTHING beside a possibly nullable component.
    bad("FILTER SESSION_USER IS TYPED NOTHING | PATH FINISH", "18.9 SR 88");
    fine("FILTER SESSION_USER IS TYPED NOTHING | PATH NOT NULL FINISH", "18.9 SR 88");
}
