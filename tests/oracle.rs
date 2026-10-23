//! The witness oracle on sentences: the graph a pattern freezes into, the record, and the
//! verdicts the construction gives (`research/oracle-witness-2026-10-23.md`).

use gql_proof::cfg::Cfg;
use gql_proof::oracle::{Bound, Oracle, Tier, oracle};
use gql_proof::parse::Parser;
use gql_proof::tokens::Grammar;
use gql_proof::verify::Verifier;
use gql_proof::{ISO_BNF_XML, MatchModeDefault, bnf};
use std::sync::LazyLock;

static ISO_BNF: LazyLock<bnf::Bnf> = LazyLock::new(|| bnf::parse(ISO_BNF_XML).unwrap());
static ISO: LazyLock<Cfg> = LazyLock::new(|| Cfg::from_bnf(&ISO_BNF));

fn record(text: &str, mode: MatchModeDefault) -> Oracle {
    let tokens = Grammar::new(&ISO_BNF);
    let verifier = Verifier::new(Grammar::new(&ISO_BNF));
    let parser = Parser::new(&ISO, &tokens, "GQL-program").unwrap();
    let parsed = parser
        .parse(text, |n| {
            verifier.verify(&n.export(&ISO), &n.render(&ISO)).is_empty()
        })
        .unwrap_or_else(|e| panic!("{text}: {e}"));
    oracle(text, &parsed.tree.export(&ISO), None, None, mode)
}

fn witness(text: &str) -> Oracle {
    let r = record(text, MatchModeDefault::DifferentEdges);
    assert_eq!(r.expect.tier, Tier::Witness, "{text}: {:?}", r.why);
    r
}

#[test]
fn a_pattern_with_labels_properties_and_a_where_clause() {
    let r = witness("MATCH ( x : a { b : 1 } ) -[ y : T ]-> ( ) WHERE x . c = 2 RETURN x , y");
    assert_eq!(r.graph.nodes.len(), 2);
    assert_eq!(r.graph.edges.len(), 1);
    let x = &r.graph.nodes[0];
    assert!(x.labels.contains("a"));
    assert_eq!(x.properties["b"], gql_proof::oracle::Value::Int(1));
    assert_eq!(x.properties["c"], gql_proof::oracle::Value::Int(2));
    let e = &r.graph.edges[0];
    assert!(e.directed && e.labels.contains("T"));
    assert_eq!((e.source, e.target), (0, 1));
    let row = r.expect.row.unwrap();
    assert_eq!(row["x"], Bound::Node(0));
    assert_eq!(row["y"], Bound::Edge(2));
    assert_eq!(r.setup.gql.unwrap()[0], "INSERT ( n0 :a { _id : 0 , b : 1 , c : 2 } ) , ( n1 :L1 { _id : 1 } ) , ( n0 ) -[ :T { _id : 2 } ]-> ( n1 )");
}

#[test]
fn juxtaposed_node_patterns_are_one_node() {
    // 22.2 GR 16 b: two node bindings with no edge between them bind the same node.
    let r = witness("MATCH ( x ) ( y ) RETURN x , y");
    assert_eq!(r.graph.nodes.len(), 1);
    let row = r.expect.row.unwrap();
    assert_eq!(row["x"], row["y"]);
}

#[test]
fn a_repeated_node_variable_is_a_self_loop() {
    let r = witness("MATCH ( x ) -> ( x ) FINISH");
    assert_eq!(r.graph.nodes.len(), 1);
    assert_eq!((r.graph.edges[0].source, r.graph.edges[0].target), (0, 0));
    assert!(!r.expect.result);
    assert_eq!(r.observe.unwrap().query, "MATCH ( x ) -> ( x ) RETURN x");
}

#[test]
fn a_forced_repeat_under_acyclic_never_matches() {
    // 16.4 NOTE 224.
    let r = witness("MATCH ACYCLIC ( x ) -> ( x ) FINISH");
    assert_eq!(r.expect.rows, Some(0));
    assert_eq!(r.observe.unwrap().rows, Some(0));
}

#[test]
fn label_expressions_without_a_model_never_match() {
    for text in [
        "MATCH ( x : ! % ) RETURN x",
        "MATCH <-/ a & ! a /- FINISH",
        "MATCH ( x { a : NULL } ) RETURN x",
    ] {
        let r = witness(text);
        assert_eq!(r.expect.rows, Some(0), "{text}");
    }
}

#[test]
fn edge_directions_follow_the_kind() {
    // Pointing left: the right node is the source. Any direction: right is chosen.
    let r = witness("MATCH ( x ) <-[ y ]- ( z ) RETURN x , y , z");
    let e = &r.graph.edges[0];
    assert_eq!((e.source, e.target), (1, 0));
    let r = witness("MATCH ( x ) ~[ y ]~ ( z ) RETURN y");
    assert!(!r.graph.edges[0].directed);
    assert!(r.setup.cypher.is_none() && r.setup.unloadable.contains_key("cypher"));
    let r = witness("MATCH ( x ) -[ y ]- ( z ) RETURN y");
    assert_eq!((r.graph.edges[0].source, r.graph.edges[0].target), (0, 1));
}

#[test]
fn a_direction_predicate_that_contradicts_the_pattern_never_matches() {
    let r = witness("MATCH ( x ) <-[ y ]- RETURN x , y NEXT FILTER x IS SOURCE OF y FINISH");
    assert_eq!(r.expect.rows, Some(0));
    let r = witness("MATCH ( x ) <-[ y ]- RETURN x , y NEXT FILTER x IS DESTINATION OF y FINISH");
    assert_eq!(r.expect.rows, None);
}

#[test]
fn quantifiers_unroll_to_the_lower_bound() {
    let r = witness("MATCH ( ( x ) -[ y ]-> ( ) ) { 2 } RETURN x , y");
    assert_eq!(r.graph.nodes.len(), 3);
    assert_eq!(r.graph.edges.len(), 2);
    let row = r.expect.row.unwrap();
    assert_eq!(row["x"], Bound::List(vec![Bound::Node(0), Bound::Node(1)]));
    assert_eq!(row["y"], Bound::List(vec![Bound::Edge(3), Bound::Edge(4)]));
    // `*` and `?` iterate zero times and the nodes around them merge.
    let r = witness("MATCH ( x ) ( -> ) * ( y ) RETURN x , y");
    assert_eq!(r.graph.nodes.len(), 1);
    assert_eq!(r.graph.edges.len(), 0);
    let r = witness("MATCH <- { 0o22 } FINISH");
    assert_eq!(r.graph.edges.len(), 18);
}

#[test]
fn a_union_takes_its_first_operand_and_nulls_the_rest() {
    let r = witness("MATCH ( x ) -[ y ]-> ( ) | ( x ) <-[ z ]- ( ) RETURN x , y , z");
    let row = r.expect.row.unwrap();
    assert_eq!(row["y"], Bound::Edge(2));
    assert_eq!(row["z"], Bound::Null);
}

#[test]
fn simplified_path_patterns_are_edge_patterns() {
    // 16.12 table 3 and SR 6: `<-/ a /-` is `<-[ IS a ]-`, a label name an edge label.
    let r = witness("MATCH <-/ a /- FINISH");
    assert_eq!(r.graph.nodes.len(), 2);
    let e = &r.graph.edges[0];
    assert!(e.labels.contains("a") && e.directed);
    assert_eq!((e.source, e.target), (1, 0));
    // A concatenation is two edges with an implicit node between; an override turns one.
    let r = witness("MATCH -/ a b > /-> FINISH");
    assert_eq!(r.graph.edges.len(), 2);
    assert_eq!(r.graph.nodes.len(), 3);
    // A negation inside is a label expression.
    let r = witness("MATCH -/ ! a /-> FINISH");
    assert!(!r.graph.edges[0].labels.contains("a"));
}

#[test]
fn paths_and_subpaths_are_the_compressed_binding() {
    let r = witness("MATCH p = ( x ) -> ( ) -> ( ) RETURN p");
    assert_eq!(r.expect.row.unwrap()["p"], Bound::Path(vec![0, 3, 1, 4, 2]));
}

#[test]
fn an_edge_variable_declared_twice_depends_on_the_match_mode() {
    let r = record("MATCH ( x ) -[ y ]-> ( ) -[ y ]-> ( ) FINISH", MatchModeDefault::Portable);
    assert_eq!(r.expect.tier, Tier::Status);
    let r = witness("MATCH DIFFERENT EDGES ( x ) -[ y ]-> ( ) -[ y ]-> ( ) FINISH");
    assert_eq!(r.expect.rows, Some(0));
}

#[test]
fn chains_keep_the_record_and_paging_leaves_the_core() {
    let r = witness("MATCH ( x ) RETURN x NEXT RETURN x AS y LIMIT 8");
    assert_eq!(r.expect.row.unwrap()["y"], Bound::Node(0));
    let r = record("MATCH ( x ) RETURN x NEXT RETURN x OFFSET 8", MatchModeDefault::DifferentEdges);
    assert_eq!(r.expect.tier, Tier::Status);
    let r = record("MATCH ( x ) RETURN x NEXT FILTER x : ! % FINISH", MatchModeDefault::DifferentEdges);
    assert_eq!(r.expect.rows, Some(0));
}

#[test]
fn what_is_out_of_the_core_still_gets_a_graph() {
    let r = record("MATCH ALL SHORTEST ( x ) -> ( y ) RETURN x", MatchModeDefault::DifferentEdges);
    assert_eq!(r.expect.tier, Tier::Status);
    assert_eq!(r.graph.edges.len(), 1);
    let r = record("RETURN TRUE AS x NEXT FILTER x OR TRUE FINISH", MatchModeDefault::DifferentEdges);
    assert_eq!(r.expect.tier, Tier::Status);
    assert!(r.graph.nodes.is_empty());
}

#[test]
fn parameters_get_a_value_of_an_admitted_class() {
    let tokens = Grammar::new(&ISO_BNF);
    let verifier = Verifier::new(Grammar::new(&ISO_BNF));
    let parser = Parser::new(&ISO, &tokens, "GQL-program").unwrap();
    let text = "MATCH ( x ) RETURN x NEXT RETURN x LIMIT $b";
    let parsed = parser
        .parse(text, |n| verifier.verify(&n.export(&ISO), &n.render(&ISO)).is_empty())
        .unwrap();
    let params = serde_json::json!([{ "name": "$b", "classes": ["exact"] }]);
    let r = oracle(text, &parsed.tree.export(&ISO), None, Some(&params), MatchModeDefault::DifferentEdges);
    assert_eq!(r.parameters["b"], gql_proof::oracle::Value::Int(1));
    assert_eq!(r.expect.tier, Tier::Witness, "{:?}", r.why);
    let r = oracle(text, &parsed.tree.export(&ISO), None, None, MatchModeDefault::DifferentEdges);
    assert_eq!(r.expect.tier, Tier::Status);
    let params = serde_json::json!([{ "name": "$b", "classes": ["list"] }]);
    let r = oracle(text, &parsed.tree.export(&ISO), None, Some(&params), MatchModeDefault::DifferentEdges);
    assert_eq!(r.expect.tier, Tier::Status);
}

#[test]
fn the_generation_record_is_checked_against_the_witness() {
    let tokens = Grammar::new(&ISO_BNF);
    let verifier = Verifier::new(Grammar::new(&ISO_BNF));
    let parser = Parser::new(&ISO, &tokens, "GQL-program").unwrap();
    let text = "MATCH ( x ) RETURN x";
    let parsed = parser
        .parse(text, |n| verifier.verify(&n.export(&ISO), &n.render(&ISO)).is_empty())
        .unwrap();
    let agree = serde_json::json!([{ "name": "x", "decl": ["node"], "out": ["node"] }]);
    let r = oracle(text, &parsed.tree.export(&ISO), Some(&agree), None, MatchModeDefault::DifferentEdges);
    assert_eq!(r.expect.tier, Tier::Witness);
    let disagree = serde_json::json!([{ "name": "x", "decl": ["edge"] }]);
    let r = oracle(text, &parsed.tree.export(&ISO), Some(&disagree), None, MatchModeDefault::DifferentEdges);
    assert!(r.why.iter().any(|w| w.contains("generation record")), "{:?}", r.why);
}
