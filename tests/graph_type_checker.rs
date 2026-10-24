//! Probes for `verify::graph_type`: each rule red on a violating sentence, green on a valid one.

use gql_proof::bnf;
use gql_proof::cfg::Cfg;
use gql_proof::parse::Parser;
use gql_proof::tokens::Grammar;
use gql_proof::verify::{Verifier, Violation};
use gql_proof::{ISO_BNF_XML, MatchModeDefault};
use std::cell::RefCell;
use std::sync::LazyLock;

static ISO_BNF: LazyLock<bnf::Bnf> = LazyLock::new(|| bnf::parse(ISO_BNF_XML).unwrap());
static ISO: LazyLock<Cfg> = LazyLock::new(|| Cfg::from_bnf(&ISO_BNF));

/// The violations of `text` with the syntax rules on, the same for every tree of it the ISO
/// BNF accepts.
fn violations(text: &str) -> Vec<Violation> {
    let tokens = Grammar::new(&ISO_BNF);
    let verifier =
        Verifier::new(Grammar::new(&ISO_BNF)).with_syntax_rules(MatchModeDefault::Portable);
    let parser = Parser::new(&ISO, &tokens, "GQL-program").unwrap();
    let verdicts = RefCell::new(Vec::new());
    // Accept no tree, so the parser offers every one up to its limit.
    let parsed = parser
        .parse(text, |n| {
            let plain = n.export(&ISO);
            let found = verifier.verify(&plain, &n.render(&ISO));
            if !found.iter().any(|v| v.rule == "ISO BNF") {
                let mut rules: Vec<_> = found.iter().map(|v| v.rule).collect();
                rules.sort();
                rules.dedup();
                verdicts.borrow_mut().push((rules, found));
            }
            false
        })
        .unwrap_or_else(|e| panic!("{text:?}: {e}"));
    let verdicts = verdicts.into_inner();
    assert!(
        !verdicts.is_empty(),
        "{text:?}: no tree passes the ISO BNF ({} trees)",
        parsed.trees
    );
    for (rules, _) in &verdicts[1..] {
        assert_eq!(
            rules, &verdicts[0].0,
            "{text:?}: the verdict depends on the tree"
        );
    }
    verdicts.into_iter().next().unwrap().1
}

#[track_caller]
fn ok(text: &str) {
    let found = violations(text);
    assert!(found.is_empty(), "{text:?}: {found:#?}");
}

#[track_caller]
fn bad(text: &str, rule: &str) {
    let found = violations(text);
    assert!(
        found.iter().any(|v| v.rule == rule),
        "{text:?}: expected {rule}, got {found:#?}"
    );
}

fn gt(body: &str) -> String {
    format!("CREATE GRAPH TYPE g {{ {body} }}")
}

#[test]
fn property_names_are_distinct() {
    // 18.5 SR 1
    bad(
        "VALUE x NODE { a PATH , a PATH } = NULL FINISH",
        "18.5 SR 1",
    );
    ok("VALUE x NODE { a PATH , b PATH } = NULL FINISH");
    bad(&gt("( { a INT , a STRING } )"), "18.5 SR 1");
    bad(&gt("( ) -[ { a INT , a INT } ]-> ( ), ( )"), "18.5 SR 1");
    // a delimited name is its representative form
    bad(&gt("( { a INT , \"a\" INT } )"), "18.5 SR 1");
    // a nested property types specification is its own scope
    ok("VALUE x NODE { a NODE { a PATH } } = NULL FINISH");
}

#[test]
fn key_and_implied_label_sets_are_disjoint() {
    // 18.2 SR 7
    bad(&gt("( :a => :a )"), "18.2 SR 7");
    bad(&gt("NODE TYPE a LABEL a"), "18.2 SR 7");
    ok(&gt("( :a => :b )"));
    ok(&gt("NODE TYPE a LABEL b"));
    // 18.3 SR 8
    bad(&gt("( b ), ( b ) -[ :E => :E ]-> ( b )"), "18.3 SR 8");
    ok(&gt("( b ), ( b ) -[ :E => :F ]-> ( b )"));
}

#[test]
fn node_type_keys_and_aliases_are_distinct() {
    // 18.1 SR 8
    bad(&gt("( :K => :L ), ( :K => :M )"), "18.1 SR 8");
    ok(&gt("( :K => :L ), ( :J => :M )"));
    // inferred keys never take another's labels
    ok(&gt("( :L ), ( :L )"));
    // 18.1 SR 10, a node type name being the alias too (Cor 1, 18.2 SR 4 b)
    bad(&gt("( b :K => ), ( b :L => )"), "18.1 SR 10");
    bad(&gt("NODE TYPE b, ( b )"), "18.1 SR 10");
    ok(&gt("( b :K => ), ( c :L => )"));
}

#[test]
fn implied_node_types_are_consistent() {
    // 18.1 SR 9
    bad(&gt("( :K => { a INT } ), ( :J => :K )"), "18.1 SR 9");
    ok(&gt("( :K => { a INT } ), ( :J => :K { a INT } )"));
    // reading: value types identical in form
    bad(
        &gt("( :K => { a INT } ), ( :J => :K { a STRING } )"),
        "18.1 SR 9",
    );
}

#[test]
fn edge_endpoints_resolve() {
    // 18.1 SR 11, 18.3 SR 17 c: ( ) is the empty node type
    bad(&gt("( ) ~[ IMPLIES ]~ ( )"), "18.1 SR 11");
    ok(&gt("( ), ( ) ~[ IMPLIES ]~ ( )"));
    ok(&gt("( b :L ), ( b ) -[ :E ]-> ( b )"));
    ok(&gt("( :L ), ( :L ) -[ :E ]-> ( :L )"));
    bad(
        &gt("( :L { a INT } ), ( :L ) -[ :E ]-> ( :L )"),
        "18.1 SR 11",
    );
    // 18.3 SR 17 a ii, 18 a ii
    bad(&gt("( b ), ( c ) -[ :E ]-> ( b )"), "18.3 SR 17");
    bad(&gt("( b ), ( b ) -[ :E ]-> ( c )"), "18.3 SR 18");
    ok(&gt("( b ), ( c ), DIRECTED EDGE :E CONNECTING ( b -> c )"));
    bad(
        &gt("( b ), DIRECTED EDGE :E CONNECTING ( b -> c )"),
        "18.3 SR 18",
    );
    bad(
        &gt("( b ), DIRECTED EDGE :E CONNECTING ( c <- b )"),
        "18.3 SR 18",
    );
    // 18.3 SR 17 b ii and v
    bad(&gt("( :L ), ( :K => ) -[ :E ]-> ( :L )"), "18.3 SR 17");
    ok(&gt("( :K => ), ( :K => ) -[ :E ]-> ( :K => )"));
    bad(
        &gt("( :K => { a INT } ), ( :K => ) -[ :E ]-> ( :K => { a INT } )"),
        "18.3 SR 17",
    );
    // reading: a key label set with no label set phrase names nothing to look up
    bad(&gt("( => ), ( => ) -[ :E ]-> ( )"), "18.3 SR 17");
}

#[test]
fn edge_types_sharing_a_key_agree() {
    // 18.1 SR 14
    bad(
        &gt("( ), ( ) -[ :K => ]-> ( ), ( ) ~[ :K => ]~ ( )"),
        "18.1 SR 14",
    );
    bad(
        &gt("( ), ( ) -[ :K => ]-> ( ), ( ) -[ :K => :L ]-> ( )"),
        "18.1 SR 14",
    );
    bad(
        &gt("( ), ( ) -[ :K => ]-> ( ), ( ) -[ :K => { a INT } ]-> ( )"),
        "18.1 SR 14",
    );
    ok(&gt("( ), ( ) -[ :K => ]-> ( ), ( ) -[ :K => ]-> ( )"));
}

#[test]
fn implied_edge_types_are_consistent() {
    // 18.1 SR 16 a
    bad(
        &gt("( ), ( ) -[ :K => { a INT } ]-> ( ), ( ) -[ :J => :K ]-> ( )"),
        "18.1 SR 16",
    );
    ok(&gt(
        "( ), ( ) -[ :K => { a INT } ]-> ( ), ( ) -[ :J => :K { a INT } ]-> ( )",
    ));
    // 18.1 SR 16 b
    bad(
        &gt("( ), ( ) -[ :K => ]-> ( ), ( ) ~[ :J => :K ]~ ( )"),
        "18.1 SR 16",
    );
    bad(
        &gt("( :A ), ( ), ( ) -[ :K => ]-> ( :A ), ( ) -[ :J => :K ]-> ( )"),
        "18.1 SR 16",
    );
    ok(&gt(
        "( :A ), ( ), ( ) -[ :K => ]-> ( ), ( ) -[ :J => :K ]-> ( :A )",
    ));
    ok(&gt("( ), ( ) -[ :K => ]-> ( ), ( ) -[ :J => :K ]-> ( )"));
}
