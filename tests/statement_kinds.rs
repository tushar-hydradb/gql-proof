//! The statement-kind rules (9.1 SR 5-7, 9.2 SR 4-7, 12.8 SR 2, 13.6 SR 2, 14.5 SR 2, 14.2 SR
//! 3-4, 14.12 SR 26, 20.6 SR 5-6) as the checker reports them, on every parse of a sentence: a
//! sentence is valid when some parse passes every check, broken when every parse breaks one.

use gql_proof::bnf;
use gql_proof::cfg::Cfg;
use gql_proof::parse::Parser;
use gql_proof::tokens::Grammar;
use gql_proof::verify::{Verifier, scope};
use gql_proof::{ISO_BNF_XML, MatchModeDefault};
use std::cell::RefCell;
use std::sync::LazyLock;

static ISO_BNF: LazyLock<bnf::Bnf> = LazyLock::new(|| bnf::parse(ISO_BNF_XML).unwrap());
static ISO: LazyLock<Cfg> = LazyLock::new(|| Cfg::from_bnf(&ISO_BNF));

/// The rules each parse of `text` breaks (syntax rules and scope), parses the ISO BNF
/// itself refuses left out.
fn verdicts(text: &str) -> Vec<Vec<&'static str>> {
    let tokens = Grammar::new(&ISO_BNF);
    let verifier =
        Verifier::new(Grammar::new(&ISO_BNF)).with_syntax_rules(MatchModeDefault::Portable);
    let mut parser = Parser::new(&ISO, &tokens, "GQL-program").unwrap();
    parser.limit = 4096;
    let out = RefCell::new(Vec::new());
    parser
        .parse(text, |n| {
            let plain = n.export(&ISO);
            let mut rules: Vec<&'static str> = verifier
                .verify(&plain, &n.render(&ISO))
                .into_iter()
                .map(|v| v.rule)
                .collect();
            if !rules.contains(&"ISO BNF") {
                rules.extend(scope::check(&plain).into_iter().map(|v| v.rule));
                rules.sort();
                rules.dedup();
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
fn ok(text: &str) {
    let v = verdicts(text);
    assert!(v.iter().any(Vec::is_empty), "{text:?}: every parse breaks a rule: {v:?}");
}

#[track_caller]
fn bad(text: &str, rule: &str) {
    let v = verdicts(text);
    assert!(
        v.iter().all(|r| r.contains(&rule)),
        "{text:?}: some parse does not report {rule}: {v:?}"
    );
}

#[test]
fn procedure_kinds() {
    ok("MATCH (x) RETURN x");
    ok("INSERT (x)");
    ok("CREATE SCHEMA /s");
    // 9.1 SR 5 or 7 (by the parse), 9.2 SR 4: a catalog statement beside a query.
    bad("FINISH NEXT DROP GRAPH a", "9.2 SR 4");
    // 9.1 SR 6, 12.8, 13.6, 14.5: no parse of a body of FINISH alone as a statement call
    // passes.
    let v = verdicts("CALL { FINISH }");
    assert!(v.iter().all(|r| !r.is_empty()), "{v:?}");
    ok("CALL { INSERT (x) }");
    ok("MATCH (x) CALL (x) { RETURN x AS y } RETURN y");
    // 9.1 SR 7: a query specification holds only composite query statements.
    bad("RETURN EXISTS { INSERT (y) } AS x", "9.1 SR 7");
    bad("RETURN EXISTS { CREATE SCHEMA /s } AS x", "9.1 SR 7");
}

#[test]
fn block_rules() {
    // 9.2 SR 5: focused and ambient in one block.
    bad("MATCH (x) RETURN x NEXT USE CURRENT_PROPERTY_GRAPH RETURN x", "9.2 SR 5");
    ok("USE CURRENT_PROPERTY_GRAPH MATCH (x) RETURN x NEXT USE CURRENT_PROPERTY_GRAPH RETURN x");
    // 9.2 SR 6, 7: a SELECT beside a RETURN.
    bad("SELECT 1 AS x NEXT RETURN x", "9.2 SR 6");
    ok("RETURN 1 AS x NEXT RETURN x");
}

#[test]
fn composite_rules() {
    // 14.2 SR 3: one conjunction; UNION is UNION DISTINCT (SR 1).
    bad("RETURN 1 AS x UNION RETURN 1 AS x OTHERWISE RETURN 1 AS x", "14.2 SR 3");
    bad("RETURN 1 AS x UNION ALL RETURN 1 AS x UNION RETURN 1 AS x", "14.2 SR 3");
    ok("RETURN 1 AS x UNION RETURN 1 AS x UNION DISTINCT RETURN 1 AS x");
    // 14.2 SR 4: focused and ambient operands.
    bad(
        "RETURN 1 AS x OTHERWISE USE CURRENT_PROPERTY_GRAPH RETURN 1 AS x",
        "14.2 SR 4",
    );
}

#[test]
fn select_from_rules() {
    // 14.12 SR 26 b ii 2: a bare FROM holds a focused statement.
    bad("SELECT * FROM { RETURN 1 AS x }", "14.12 SR 26");
    ok("SELECT * FROM { USE CURRENT_PROPERTY_GRAPH RETURN 1 AS x }");
    // b ii 1: after a graph expression, an ambient one.
    ok("SELECT * FROM CURRENT_PROPERTY_GRAPH { RETURN 1 AS x }");
    bad(
        "SELECT * FROM CURRENT_PROPERTY_GRAPH { USE CURRENT_PROPERTY_GRAPH RETURN 1 AS x }",
        "14.12 SR 26",
    );
}

#[test]
fn value_body_emits_a_query() {
    // 20.6 SR 5 a: the last statement is a linear query statement, which 9.1 SR 7 already says.
    bad("RETURN VALUE { INSERT (y) RETURN COUNT(*) AS z } AS x", "9.1 SR 7");
    ok("RETURN VALUE { MATCH (y) RETURN COUNT(*) AS z } AS x");
}

#[test]
fn parent_reference_solidus() {
    // 17.6 SR 1: `//` is no parent reference; a named schema needs its solidus.
    bad("CALL / / a ( )", "17.6 SR 1");
    ok("CALL / a ( )");
}

#[test]
fn literal_limits_under_h2() {
    ok("RETURN 8E8M AS x");
    bad("RETURN 1E40M AS x", "21.2 SR 18");
    bad("RETURN 123456789012345678901 AS x", "21.2 SR 18");
    ok("RETURN 8E8 AS x");
    bad("RETURN 1E300 AS x", "21.2 SR 20");
}

#[test]
fn field_names_distinct() {
    bad("RETURN CAST(NULL AS RECORD { a INT, a INT }) AS x", "18.10 SR 2");
    ok("RETURN CAST(NULL AS RECORD { a INT, b INT }) AS x");
}

#[test]
fn keep_makes_every_pattern_selective() {
    // 16.4 SR 6 then SR 12: under DIFFERENT EDGES, KEEP ANY makes both patterns selective.
    bad("MATCH DIFFERENT EDGES (x), (y) KEEP ANY RETURN x", "16.4 SR 12");
    ok("MATCH DIFFERENT EDGES (x) KEEP ANY RETURN x");
}

#[test]
fn select_sort_keys_under_grouping() {
    // 14.12 SR 19: with an aggregate, a sort key names an alias or a grouping element.
    ok("SELECT COUNT(*) AS c FROM CURRENT_PROPERTY_GRAPH MATCH (a) ORDER BY c");
    bad("SELECT COUNT(*) AS c FROM CURRENT_PROPERTY_GRAPH MATCH (a) ORDER BY a", "14.12 SR 19");
}

#[test]
#[ignore]
fn explain() {
    let text = std::env::var("GQL_TEXT").unwrap();
    let all = verdicts(&text);
    let mut counts: std::collections::BTreeMap<Vec<&str>, usize> = Default::default();
    for v in &all {
        *counts.entry(v.clone()).or_default() += 1;
    }
    eprintln!("{} parses", all.len());
    for (v, n) in counts {
        eprintln!("{n:>5} {v:?}");
    }
}
