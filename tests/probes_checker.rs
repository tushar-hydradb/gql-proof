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
    // 21.2 SR 42: an escape reached through the prose leaf (SR 40) starts with a reverse solidus.
    red(leaf("character representation", "\\"), "21.2 SR 31-33, 41");
    red(leaf("string literal character", "\\"), "21.2 SR 31-33, 41");
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
fn nothing_is_known_not_nullable() {
    // 18.9 SR 4 b, SR 88: NOTHING beside a possibly nullable component.
    bad("FILTER SESSION_USER IS TYPED NOTHING | PATH FINISH", "18.9 SR 88");
    fine("FILTER SESSION_USER IS TYPED NOTHING | PATH NOT NULL FINISH", "18.9 SR 88");
}

#[test]
fn red_team_findings() {
    // 4.17.4.2 (reading): nothing but NOTHING is known not nullable, so a NOT NULL site takes
    // no computed value.
    bad("RETURN CURRENT_DATE AS x NEXT LET VALUE y NODE NOT NULL = LET z = x IN CAST ( NULL AS NODE ) END FINISH", "10.3 SR 8");
    // 16.5 SR 6 c: an inserted property of the null type.
    bad("INSERT ( { a : NULL } )", "16.5 SR 6");
    fine("INSERT ( { a : 1 } )", "16.5 SR 6");
    // 6 SR 4: a delimited identifier's representative form is compared too.
    bad("MATCH (m) RETURN m.`rn` AS x", "6 SR 4");
}

#[test]
fn second_review_findings() {
    // 14.12 SR 27 b: a HAVING needs an aggregating select item.
    bad("SELECT * FROM CURRENT_PROPERTY_GRAPH { FINISH } HAVING TRUE", "14.12 SR 27");
    // 14.12 SR 27 a then 9.2 SR 5: a SELECT is ambient, so beside a USE statement it breaks
    // the block.
    bad("SELECT CURRENT_DATE AS x NEXT USE CURRENT_PROPERTY_GRAPH INSERT ( )", "9.2 SR 5");
    // 4.17.4.2: a NOT NULL declared graph type takes no computed value.
    bad("SESSION SET GRAPH $b GRAPH NOT NULL = CURRENT_PROPERTY_GRAPH", "10.1 SR 8");
    // 14.10 SR 4: an EXISTS in a sort key is a nested query after 19.4 SR 2.
    bad("MATCH (a) RETURN a ORDER BY EXISTS { (a) }", "14.10 SR 4");
}

#[test]
fn nested_graph_patterns() {
    // 16.4 SR 14: an enclosing REPEATABLE ELEMENTS pattern does not guard a nested unbounded
    // quantifier, though the nested pattern's own default would.
    bad(
        "MATCH REPEATABLE ELEMENTS ( x WHERE EXISTS { DIFFERENT EDGES <- + } ) RETURN x",
        "16.4 SR 14 nested",
    );
    fine(
        "MATCH DIFFERENT EDGES ( x WHERE EXISTS { DIFFERENT EDGES <- + } ) RETURN x",
        "16.4 SR 14 nested",
    );
    // 16.4 SR 6: KEEP reaches a nested path pattern's search prefix.
    bad("MATCH ( x WHERE EXISTS { ANY SHORTEST <- } ) KEEP TRAIL RETURN x", "16.4 SR 6 nested");
}

#[test]
fn outside_the_claim() {
    // 22.1 SR 3: no `$$`.
    bad("CALL $$b ( )", "22.1 SR 3");
    // 14.12 SR 22: `*` over a FROM that declares nothing.
    bad("SELECT * FROM CURRENT_PROPERTY_GRAPH { FINISH }", "14.12 SR 22");
    fine("SELECT * FROM { USE CURRENT_PROPERTY_GRAPH MATCH (a) RETURN a }", "14.12 SR 22");
}

#[test]
fn rewrite_findings() {
    // 21.2 SR 67 then 20.8 SR 4: a NULL to a declared null type is a cast to an immaterial type.
    bad("LET VALUE x :: NULL = NULL RETURN x", "20.8 SR 4");
    // 20.7 SR 1 b then 22.19 SR 2: NULLIF's result is its first operand, combined.
    bad("MATCH ( x ) RETURN NULLIF ( x . p , 1 ) AS y", "22.19 SR 2");
}

#[test]
fn rewrite_findings_paths() {
    // 16.7 SR 10 then 20: a multiset alternation operand is a named subpath.
    bad("MATCH ( <- ? |+| <- ? ) <- RETURN 1 AS x", "16.7 SR 20");
    fine("MATCH ( <- |+| <- ) <- RETURN 1 AS x", "16.7 SR 20");
    // 16.4 SR 12 under the portable default: a missing mode may be DIFFERENT EDGES.
    bad("MATCH ANY ( a ) , ( b ) RETURN a , b", "16.4 SR 12");
}

#[test]
fn third_review_findings() {
    // 20.7 SR 2 g: an element predicate as a when operand (reading: none).
    bad("RETURN COUNT ( * ) AS x NEXT ORDER BY CASE CAST ( NULL AS EDGE ) WHEN IS DIRECTED THEN NULL ELSE x END FINISH", "20.7 SR 2");
    // 11.1 SR 3: SESSION SET GRAPH's expression is typed.
    bad("SESSION SET GRAPH ( 1 + 2 )", "11.1 SR 3");
}

#[test]
fn fourth_review_findings() {
    // 12.5 SR 2: a DROP parent with an object name identifies no schema.
    bad("DROP GRAPH / a . a", "12.5 SR 2");
    fine("DROP GRAPH / a", "12.5 SR 2");
    // 17.6 SR 1 b, held literally.
    bad("DROP GRAPH HOME_SCHEMA a", "17.6 SR 1");
    bad("DROP GRAPH a . a", "17.6 SR 1");
    fine("DROP GRAPH HOME_SCHEMA / a", "17.6 SR 1");
    // 12.6 SR 5 with H1: created and referenced.
    bad("CREATE GRAPH TYPE a COPY OF a", "12.6 SR 5");
    fine("CREATE GRAPH TYPE b COPY OF a", "12.6 SR 5");
    bad("CREATE SCHEMA / a CREATE GRAPH / a / b ANY", "12.2 SR 5");
    bad("CREATE GRAPH / a LIKE / a", "12.4 SR 6");
    fine("CREATE GRAPH / b LIKE / a", "12.4 SR 6");
    fine("CREATE GRAPH IF NOT EXISTS / a LIKE / a", "12.4 SR 6");
    // 20.8 SR 11 a: a list casts to a list only.
    bad("RETURN CAST ( [1] AS ANY ) AS x", "20.8 SR 11");
    // 20.8 SR 11 d: the element types cast too.
    bad("RETURN CAST ( [TRUE] AS LIST < DATE > ) AS x", "20.8 SR 11 d");
    fine("RETURN CAST ( [1] AS LIST < INT > ) AS x", "20.8 SR 11 d");
    // 10.3 SR 8 (reading): a length-bounded string type, also nested, is not declared.
    bad("VALUE x CHAR = SESSION_USER RETURN x AS y", "10.3 SR 8");
    bad("VALUE x ANY < BYTES | CHAR > = NULL RETURN x AS y", "10.3 SR 8");
    bad("VALUE x RECORD { a :: STRING ( 3 ) } = NULL RETURN x AS y", "10.3 SR 8");
    fine("VALUE x STRING = SESSION_USER RETURN x AS y", "10.3 SR 8");
}

/// Red on a violating tree: some parse of `text` reports `rule`. For rules stated on a choice
/// the ISO grammar leaves open (a statement kind), where every parse breaks one of several.
#[track_caller]
fn bad_on_some_parse(text: &str, rule: &str) {
    let v = verdicts(text);
    assert!(v.iter().any(|r| r.contains(&rule)), "{text:?}: no parse reports {rule}: {v:?}");
}

#[test]
fn statement_kind_trees() {
    // 9.1 SR 5, 6: a procedure of one kind holding statements of another.
    bad_on_some_parse("CREATE SCHEMA / a NEXT FILTER TRUE FINISH", "9.1 SR 5");
    bad_on_some_parse("CREATE SCHEMA / a", "9.1 SR 6");
    // 12.8 SR 2, 13.6 SR 2, 14.5 SR 2: an inline call's procedure of another kind.
    bad_on_some_parse("CALL { CREATE SCHEMA / a }", "12.8 SR 2");
    bad_on_some_parse("CALL { CREATE SCHEMA / a }", "13.6 SR 2");
    bad_on_some_parse("CALL { CREATE SCHEMA / a }", "14.5 SR 2");
    // 12.7 SR 2: a DROP GRAPH TYPE parent holding an object name.
    bad("DROP GRAPH TYPE / a . a", "12.7 SR 2");
    fine("DROP GRAPH TYPE / a", "12.7 SR 2");
    // 16.9 SR 3: a yielded path variable that is a node.
    bad_on_some_parse("MATCH ( x ) YIELD x RETURN x", "16.9 SR 3");
}

#[test]
fn catalog_root_is_one_thing() {
    // 17.1 SR 2 a i against SR 5 (the fifth review): the root as a schema and as a directory.
    bad("CREATE SCHEMA / a NEXT DROP GRAPH / b", "17.1 SR 2");
    fine("CREATE SCHEMA / a NEXT DROP GRAPH / a / b", "17.1 SR 2");
    fine("DROP GRAPH / b", "17.1 SR 2");
}

#[test]
fn sixth_review_findings() {
    // 17.6 SR 5 (reading): a parent with an object name, in any reference.
    bad("CALL / a . a ( )", "17.6 SR 5");
    bad("SESSION SET GRAPH / a . a . a", "17.6 SR 5");
    fine("CALL / a ( )", "17.6 SR 5");
    // H3: the object expression primary tree of `GRAPH x . a` and `VARIABLE "x"` is typed.
    bad_on_some_parse("VALUE x ( ) = NULL RETURN COUNT ( ( GRAPH x . a ) IS NULL ) AS y", "20.11 SR 3");
    bad_on_some_parse("SESSION SET GRAPH VARIABLE \"x\"", "11.1 SR 3");
    // 16.8 SR 4 a ii (reading): no value given a closed graph type.
    bad("USE CAST ( $b AS GRAPH { ( ) } NOT NULL ) MATCH ( IS a ) FINISH", "16.8 SR 4");
    bad("VALUE x GRAPH { ( ) } = NULL FINISH", "16.8 SR 4");
    fine("RETURN COUNT ( CAST ( NULL AS GRAPH { ( ) } LIST ) ) AS x", "16.8 SR 4");
    fine("USE CAST ( $b AS ANY GRAPH ) MATCH ( IS a ) FINISH", "16.8 SR 4");
    // 12.6 SR 5: a delimited name is its representative form.
    bad("CREATE GRAPH TYPE \"a\" COPY OF / a", "12.6 SR 5");
    // 17.2 SR 2 with H1: one name, one kind of object.
    bad("CREATE GRAPH / a TYPED / a", "17.2 SR 2");
    fine("CREATE GRAPH / a TYPED / b", "17.2 SR 2");
}

#[test]
fn category_sites_on_the_printed_tree() {
    // The seventh review: an opaque value under a category, on some tree of the text.
    let g = "RETURN COUNT ( ( ( GRAPH CURRENT_PROPERTY_GRAPH ) ) IS NULL ) AS x";
    bad_on_some_parse(g, "20.21 SR 3 primary");
    bad_on_some_parse(g, "20.23 SR 2 primary");
    bad_on_some_parse(g, "20.23 SR 4 primary");
    bad_on_some_parse("FILTER 1 FINISH", "20.20 SR 3 primary");
    bad_on_some_parse("RETURN COUNT ( ( 1 ) IS NULL ) AS x", "20.15 SR 1 primary");
    bad_on_some_parse("RETURN COUNT ( ( 1 ) IS NULL ) AS x", "20.13 SR 2 primary");
    // a numeric term or factor over a duration, on its numeric tree
    bad_on_some_parse("RETURN 2 * DURATION 'P1Y' AS x", "20.21 SR 3 primary");
    bad_on_some_parse("RETURN - DURATION 'P1Y' AS x", "20.21 SR 3 primary");
    bad_on_some_parse("RETURN COUNT ( ( 1 ) IS NULL ) AS x", "20.1 SR 4-6 primary");
    // a literal of the category passes on its own tree
    fine("RETURN 1 + 1 AS x", "20.21 SR 3 primary");
}

#[test]
fn eighth_review_findings() {
    // 11.1 SR 3 a ii: `$b * + NULL` as a duration term has the null type, no material graph type.
    bad_on_some_parse("SESSION SET GRAPH ( $b * + NULL )", "11.1 SR 3 primary");
    bad_on_some_parse("RETURN GRAPH MAX ( $b ) AS x", "11.1 SR 3 primary");
    bad_on_some_parse("RETURN TABLE ( 1 + 1 ) AS x", "11.2 SR 4 primary");
    // ID076: no category takes ELEMENT_ID.
    bad_on_some_parse("MATCH ( x ) WHERE ELEMENT_ID ( x ) RETURN x", "20.20 SR 3 primary");
    // 20.28 SR 1 a on the duration addition tree.
    bad_on_some_parse("RETURN 1 + 1 AS x", "20.28 SR 1 primary");
    fine("RETURN DURATION 'P1Y' + DURATION 'P1Y' AS x", "20.28 SR 1 primary");
}

#[test]
fn ninth_review_findings() {
    // a dynamic or null operand's type kept through a sign and a string function (22.19 SR 2)
    bad("MATCH ( x ) RETURN [ - x . a , 1 ] AS y", "22.19 SR 2");
    bad("MATCH ( x ) RETURN [ UPPER ( x . a ) , 'a' ] AS y", "22.19 SR 2");
    // the null type at a property site
    bad("INSERT ( { a : - NULL } )", "16.5 SR 6");
    // nested NOT NULL
    bad("VALUE x INT NOT NULL LIST = [ NULL ] FINISH", "10.3 SR 8");
    bad("RETURN CAST ( [ 1 ] AS ANY NOT NULL LIST ) AS x", "20.8 SR 11 d");
    // ELEMENT_ID only as an item
    bad("MATCH ( x ) RETURN COALESCE ( ELEMENT_ID ( x ) , 1 ) AS y", "20.10 SR 3");
    fine("MATCH ( x ) RETURN ELEMENT_ID ( x ) AS y", "20.10 SR 3");
    // ID004: no cast of [ ], and no [ ] in a combination
    bad("RETURN CAST ( [ ] AS INT LIST ) AS x", "20.8 SR 11 d");
    bad("FILTER [ [ ] ] IS NULL FINISH", "22.19 SR 2");
    // 22.1 SR 5 d i: a parameter an earlier SESSION SET set has that type
    bad_on_some_parse("SESSION SET VALUE $b = TRUE SESSION SET GRAPH $c = VARIABLE $b", "11.1 SR 3");
}

#[test]
fn tenth_review_findings() {
    // 9.2 SR 5: a SELECT is focused as written, ambient as replaced: beside neither.
    bad("INSERT ( ) NEXT SELECT CURRENT_DATE AS x", "9.2 SR 5");
    bad("SELECT CURRENT_DATE AS x NEXT INSERT ( )", "9.2 SR 5");
    fine("SELECT CURRENT_DATE AS x NEXT SELECT x AS y", "9.2 SR 5");
}

#[test]
fn eleventh_review_findings() {
    // 17.1: a root schema and a `..` step
    bad("SESSION SET SCHEMA / SESSION SET SCHEMA .. / a", "17.1 SR 2");
    // one object per name: bare names and directories
    bad_on_some_parse("CREATE GRAPH / ab TYPED / a AS COPY OF a", "17.2 SR 2");
    bad("SESSION SET SCHEMA / a SESSION SET SCHEMA / a / b", "17.2 SR 2");
    // 12.6 SR 7 b iv: a LIKE source with a constraining graph type
    bad("CREATE GRAPH TYPE / ab LIKE CAST ( NULL AS PROPERTY GRAPH )", "12.6 SR 7");
    fine("CREATE GRAPH TYPE / ab LIKE CURRENT_PROPERTY_GRAPH", "12.6 SR 7");
    // 20.8 SR 5: an operand holding NULL
    bad("RETURN CAST ( NULL AS BOOL NOT NULL ) AS x", "20.8 SR 5");
    bad_on_some_parse("RETURN CAST ( 1 IS NULL AS BOOL NOT NULL ) AS x", "20.8 SR 5 contains");
    fine("RETURN CAST ( CAST ( CURRENT_DATE AS DATE NOT NULL ) AS DATE NOT NULL ) AS x", "20.8 SR 5 contains");
    // 16.6 SR 8 (reading): no subquery in a selective path pattern
    bad("MATCH ANY ( { a : EXISTS { <- } } ) FINISH", "16.6 SR 8 nested");
    fine("MATCH ( { a : EXISTS { <- } } ) FINISH", "16.6 SR 8 nested");
}

#[test]
fn twelfth_review_findings() {
    // 21.2 SR 73: a sign only on an unsigned numeric literal in a list literal.
    bad_on_some_parse("FILTER [ - NULL ] IS NULL FINISH", "21.2 SR 73");
    // delimited names as variables, fields, properties
    bad_on_some_parse("RETURN { \"a\" : 1 } AS x", "21.3 SR 4 names");
    bad_on_some_parse("VALUE x = EXISTS { <- } DROP GRAPH / a", "9.1 SR 5 nested");
    bad_on_some_parse("RETURN 1 AS \"x\" NEXT YIELD \"x\" RETURN 1 AS y", "16.14 SR 4");
    bad("MATCH ( x ) SET x . \"a\" = 1", "21.3 SR 4 names");
    // a delimited graph name meets a bare one
    bad_on_some_parse("CREATE GRAPH / x ANY AS COPY OF \"x\"", "12.4 SR 6");
    // a GROUP LIST of ANY
    bad_on_some_parse("FILTER SESSION_USER IS TYPED GROUP LIST FINISH", "18.9 SR 68");
    // temporal shapes, durations of no field, URI schemes
    bad_on_some_parse("RETURN DATE '2024-01- 1' AS x", "21.2 SR 59");
    bad_on_some_parse("RETURN DURATION 'P' AS x", "21.2 SR 68");
    // a combination past an unknown input
    bad_on_some_parse("RETURN COALESCE ( $b , 8 , TRUE ) AS x", "22.19 SR 4");
    // ELEMENT_ID in a set operation
    bad_on_some_parse("MATCH ( x ) RETURN ELEMENT_ID ( x ) AS y UNION RETURN TRUE AS y", "20.10 SR 3");
    // a closed union cast target
    bad_on_some_parse("RETURN CAST ( 1 AS INT8 | BOOL ) AS x", "20.8 SR 9");
    // a selective pattern references an outer variable
    bad_on_some_parse("MATCH ( x ) WHERE EXISTS { MATCH ANY ( y WHERE y . a = x . a ) RETURN y } FINISH", "16.6 SR 8");
    // a value variable as a bound INSERT node
    bad("LET x = 1 INSERT ( x )", "16.5 SR 10");
    // a nested TRIM's outer source
    bad_on_some_parse("RETURN TRIM ( LTRIM ( SESSION_USER ) FROM X'00' ) AS x", "20.23 SR 2, 4");
    // a temporal function's record argument
    bad_on_some_parse("RETURN DATE ( { x : 1 , x : 2 } ) AS y", "20.19 SR 2");
}

#[test]
fn thirteenth_review_findings() {
    // 20.5 SR 5: a LET .. IN name has its initializer's type
    bad("RETURN LET VALUE x ANY = CURRENT_DATE IN CEIL ( x ) END AS z", "20.21 SR 3");
    bad("RETURN LET VALUE x ANY = CURRENT_DATE IN 1 END AS z", "20.5 SR 5");
    fine("RETURN LET x = CURRENT_DATE IN 1 END AS z", "20.5 SR 5");
}

#[test]
fn fourteenth_review_findings() {
    bad_on_some_parse("AT / a DROP SCHEMA / a", "12.3 SR 7");
    bad_on_some_parse("DROP GRAPH / a / b DROP SCHEMA / a", "12.3 SR 7");
    fine("DROP SCHEMA / a", "12.3 SR 7");
    bad_on_some_parse("MATCH ( x ) -> ( y ) RETURN x AS x , PERCENTILE_CONT ( y . a , y . b ) AS z GROUP BY x", "20.12 SR 8");
    bad_on_some_parse("MATCH ( y ) MATCH ANY SHORTEST ( x ) -> ( y ) -> ( z ) RETURN x", "16.6 SR 7");
    bad_on_some_parse("MATCH ( x ) RETURN x ORDER BY LET z = x IN z END", "14.10 SR 4 let");
}

#[test]
fn fifteenth_review_findings() {
    bad_on_some_parse("RETURN INTERVAL '1' DAY AS x", "21.2 SR 72");
    fine("RETURN DURATION 'P1D' AS x", "21.2 SR 72");
    bad_on_some_parse("RETURN CURRENT_DATE + DURATION 'P1DT' AS x", "20.26 SR 1 moved");
    fine("RETURN LOCAL_TIMESTAMP + DURATION 'P1DT' AS x", "20.26 SR 1 moved");
    // H2's limits on the tree
    bad_on_some_parse("MATCH <- { 256 } FINISH", "16.11 SR 1");
    fine("MATCH <- { 255 } FINISH", "16.11 SR 1");
    bad_on_some_parse("FILTER SESSION_USER IS TYPED VARCHAR ( 99999999999999999999 ) FINISH", "18.9 SR 17");
    bad_on_some_parse("FILTER SESSION_USER IS TYPED BYTES ( 70000 ) FINISH", "18.9 SR 25");
    bad_on_some_parse("FILTER SESSION_USER IS TYPED DECIMAL ( 40 ) FINISH", "18.9 SR 32");
    bad_on_some_parse("FILTER SESSION_USER IS TYPED FLOAT ( 8 , 88 ) FINISH", "18.9 SR 42");
}

#[test]
fn sixteenth_review_findings() {
    bad_on_some_parse("FILTER EXISTS { CALL a ( ) RETURN 1 AS y } FINISH NEXT CALL { CALL a ( ) }", "14.5 SR 3 kinds");
    // an inline call holding a named one is not the named one's kind
    fine("CALL { CALL a ( ) }", "14.5 SR 3 kinds");
}

#[test]
fn seventeenth_review_findings() {
    bad_on_some_parse("ORDER BY NULL - DURATION ( { } ) FINISH", "20.28 SR 1 record");
    fine("RETURN DURATION ( 'P1Y' ) AS x", "20.28 SR 1 record");
}

#[test]
fn key_label_sets_without_gg22() {
    // 18.2 SR 9 a ii, 18.3 SR 10 a ii: a claim without GG22 omits no key label set.
    let tokens = Grammar::new(&ISO_BNF);
    let v = Verifier::new(Grammar::new(&ISO_BNF))
        .with_syntax_rules(MatchModeDefault::Portable)
        .with_key_label_sets_required(true);
    let parser = Parser::new(&ISO, &tokens, "GQL-program").unwrap();
    for (text, rule) in [
        ("CREATE GRAPH TYPE / ab { ( ) }", "18.2 SR 9"),
        ("CREATE GRAPH TYPE / ab { ( ) -[ { } ]-> ( ) }", "18.3 SR 10"),
    ] {
        let found = std::cell::RefCell::new(false);
        let _ = parser.parse(text, |n| {
            let plain = n.export(&ISO);
            if v.verify(&plain, &n.render(&ISO)).iter().any(|x| x.rule == rule) {
                *found.borrow_mut() = true;
            }
            false
        });
        assert!(found.into_inner(), "{text}: {rule} not reported");
    }
}

#[test]
fn eighteenth_review_findings() {
    // 20.8 SR 5 contains: the NULL of NULLIF's rewrite and of a CASE's implicit ELSE NULL
    bad_on_some_parse("RETURN CAST ( NULLIF ( 8 , 8 ) AS INT NOT NULL ) AS x", "20.8 SR 5 contains");
    bad_on_some_parse("RETURN CAST ( CASE WHEN TRUE THEN 8 END AS INT NOT NULL ) AS x", "20.8 SR 5 contains");
    fine("RETURN CAST ( CASE WHEN TRUE THEN 8 ELSE 9 END AS INT NOT NULL ) AS x", "20.8 SR 5 contains");
    // 20.28 SR 1 record: every record argument, mixed or upper-case fields too
    bad("RETURN DURATION ( { years : 1 , days : 1 } ) + DURATION ( 'PT1S' ) AS x", "20.28 SR 1 record");
    bad("RETURN DURATION ( { YEARS : 1 } ) + DURATION ( 'P1Y' ) AS x", "20.28 SR 1 record");
}

#[test]
fn unknowns_audit_element_id() {
    // ID076: ELEMENT_ID's value through a column or a VALUE is read as the function is
    bad("MATCH ( x ) RETURN ELEMENT_ID ( x ) AS e ORDER BY e || 'x'", "20.10 SR 3");
    bad("RETURN VALUE { MATCH ( x ) RETURN ELEMENT_ID ( x ) AS e LIMIT 1 } || 'x' AS a", "20.10 SR 3");
    bad("MATCH ( x ) RETURN ELEMENT_ID ( x ) AS e NEXT RETURN e < e AS a", "20.10 SR 3");
    bad("MATCH ( x ) RETURN ELEMENT_ID ( x ) AS e NEXT RETURN COALESCE ( e , 1 ) AS a , e || 'x' AS b", "20.10 SR 3");
    bad("MATCH ( x ) RETURN ELEMENT_ID ( x ) AS e NEXT INSERT ( :L { p : e } )", "20.10 SR 3");
    fine("MATCH ( x ) RETURN ELEMENT_ID ( x ) AS e NEXT RETURN e AS f", "20.10 SR 3");
    fine("MATCH ( x ) RETURN ELEMENT_ID ( x ) AS e NEXT RETURN e IS NULL AS f", "20.10 SR 3");
    fine("MATCH ( x ) RETURN ELEMENT_ID ( x ) AS e NEXT RETURN e = e AS f", "20.10 SR 3");
    fine("MATCH ( x ) , ( y ) RETURN ELEMENT_ID ( x ) = ELEMENT_ID ( y ) AS f", "20.10 SR 3");
}

#[test]
fn unknowns_audit_rows_and_elements() {
    // a table variable's row keeps its columns (10.2 SR 8, 9; 14.8 SR 10 a; 20.11 SR 2 a)
    bad("TABLE t = { RETURN 1 AS a } FOR r IN t RETURN r . b AS c", "20.11 SR 2");
    bad("TABLE t = { RETURN 'a' AS a } FOR r IN t RETURN r . a + 1 AS c", "20.21 SR 3");
    // a value variable holding a table: every parse is flagged (the category sites)
    let v = verdicts("VALUE t = TABLE { RETURN 1 AS a } FOR r IN t RETURN r . a || 'x' AS c");
    assert!(!v.is_empty() && v.iter().all(|p| !p.is_empty()), "{v:?}");
    fine("TABLE t = { RETURN 1 AS a } FOR r IN t RETURN r . a + 1 AS c", "20.21 SR 3");
    fine("TABLE t = { RETURN 1 AS a } FOR r IN t RETURN r . a + 1 AS c", "20.11 SR 2");
    // a dynamic source's elements stay dynamic; a null source has none
    bad("FOR x IN CAST ( NULL AS ANY ) RETURN COALESCE ( x , 1 ) AS a", "22.19 SR 2");
    bad("FOR x IN NULL RETURN x + 1 AS a", "14.8 SR 10 null");
    bad("FOR x IN NULL || NULL RETURN x + 1 AS a", "20.15 SR 2 null");
}

#[test]
#[ignore]
fn dump_clean_parses() {
    let text = std::env::var("PROBE").unwrap();
    let tokens = Grammar::new(&ISO_BNF);
    let v = verifier();
    let mut parser = Parser::new(&ISO, &tokens, "GQL-program").unwrap();
    parser.limit = 2048;
    parser
        .parse(&text, |n| {
            let plain = n.export(&ISO);
            let mut rules: Vec<&'static str> =
                v.verify(&plain, &n.render(&ISO)).into_iter().map(|x| x.rule).collect();
            if !rules.contains(&"ISO BNF") {
                rules.extend(scope::check(&plain).into_iter().map(|x| x.rule));
                rules.extend(types::check(&plain).into_iter().map(|x| x.rule));
                if rules.is_empty() {
                    println!("{plain:#?}");
                    return true;
                }
            }
            false
        })
        .unwrap();
}
