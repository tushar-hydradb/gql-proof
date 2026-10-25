//! The witness oracle on sentences: the graph a pattern freezes into, the record, and the
//! verdicts the construction gives (`research/oracle-witness-2026-10-23.md`).

use gql_proof::cfg::Cfg;
use gql_proof::oracle::{Oracle, Tier, oracle};
use gql_proof::parse::Parser;
use gql_proof::tokens::Grammar;
use gql_proof::verify::Verifier;
use gql_proof::{ISO_BNF_XML, MatchModeDefault, bnf};
use std::sync::LazyLock;

static ISO_BNF: LazyLock<bnf::Bnf> = LazyLock::new(|| bnf::parse(ISO_BNF_XML).unwrap());
static ISO: LazyLock<Cfg> = LazyLock::new(|| Cfg::from_bnf(&ISO_BNF));

/// The record of a sentence, parsed as the oracle command parses it: the derivation the
/// typed rules accept when there is one.
fn record(text: &str, mode: MatchModeDefault) -> Oracle {
    let tokens = Grammar::new(&ISO_BNF);
    let verifier = Verifier::new(Grammar::new(&ISO_BNF));
    let parser = Parser::new(&ISO, &tokens, "GQL-program").unwrap();
    let scope = gql_proof::context::scope::Scope {
        caps: gql_proof::context::scope::Caps { slots: 4, references: 4 },
    };
    let types = gql_proof::context::types::Types::with_typed(&ISO, 4);
    let typed = gql_proof::context::pair::Typed::new(scope, types);
    let syntax = |n: &gql_proof::tree::Node| verifier.verify(&n.export(&ISO), &n.render(&ISO)).is_empty();
    let parsed = parser
        .parse(text, |n| syntax(n) && gql_proof::context::accepts(&typed, &n.export(&ISO)).is_ok())
        .or_else(|_| parser.parse(text, syntax))
        .unwrap_or_else(|e| panic!("{text}: {e}"));
    oracle(text, &parsed.tree.export(&ISO), None, None, mode, &Default::default())
}

/// A record whose expectation is backed by a theorem: the bag (theorem 2) or the witness
/// (theorem 1), never the status alone.
fn witness(text: &str) -> Oracle {
    let r = record(text, MatchModeDefault::DifferentEdges);
    assert_ne!(r.expect.tier, Tier::Status, "{text}: {:?} {:?}", r.why, r.expect.evaluator);
    r
}

/// The one row the record claims, as json: the bag's only row, or the witness row.
fn row(r: &Oracle) -> serde_json::Value {
    if let Some(bag) = &r.expect.bag {
        assert_eq!(bag.len(), 1, "{}: {bag:?}", r.sentence);
        return serde_json::to_value(&bag[0]).unwrap();
    }
    serde_json::to_value(r.expect.row.as_ref().expect("a row")).unwrap()
}

fn node(id: usize) -> serde_json::Value {
    serde_json::json!({ "kind": "Node", "value": id })
}

fn edge(id: usize) -> serde_json::Value {
    serde_json::json!({ "kind": "Edge", "value": id })
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
    let row = row(&r);
    assert_eq!(row["x"], node(0));
    assert_eq!(row["y"], edge(2));
    assert_eq!(r.setup.gql.unwrap()[0], "INSERT ( n0 :a { _id : 0 , b : 1 , c : 2 } ) , ( n1 :L1 { _id : 1 } ) , ( n0 ) -[ :T { _id : 2 } ]-> ( n1 )");
}

#[test]
fn juxtaposed_node_patterns_are_one_node() {
    // 22.2 GR 16 b: two node bindings with no edge between them bind the same node.
    let r = witness("MATCH ( x ) ( y ) RETURN x , y");
    assert_eq!(r.graph.nodes.len(), 1);
    let row = row(&r);
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
    assert_eq!(r.expect.rows, Some(1));
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
    assert_eq!(r.expect.rows, Some(1));
}

#[test]
fn quantifiers_unroll_to_the_lower_bound() {
    let r = witness("MATCH ( ( x ) -[ y ]-> ( ) ) { 2 } RETURN x , y");
    assert_eq!(r.graph.nodes.len(), 3);
    assert_eq!(r.graph.edges.len(), 2);
    let row = row(&r);
    assert_eq!(row["x"], serde_json::json!({ "kind": "List", "value": [node(0), node(1)] }));
    assert_eq!(row["y"], serde_json::json!({ "kind": "List", "value": [edge(3), edge(4)] }));
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
    // The evaluator finds both operands' matches on the witness graph: the first operand's
    // edge, and the second operand's reading of the same edge where `<-` reverses it.
    let bag = r.expect.bag.as_ref().expect("a bag");
    assert!(bag.iter().any(|row| serde_json::to_value(&row["y"]).unwrap() == edge(2) && serde_json::to_value(&row["z"]).unwrap() == serde_json::json!({ "kind": "Null" })), "{bag:?}");
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
    assert_eq!(row(&r)["p"], serde_json::json!({ "kind": "Path", "value": [0, 3, 1, 4, 2] }));
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
    assert_eq!(row(&r)["y"], node(0));
    // The evaluator knows OFFSET drops the one row.
    let r = record("MATCH ( x ) RETURN x NEXT RETURN x OFFSET 8", MatchModeDefault::DifferentEdges);
    assert_eq!(r.expect.tier, Tier::Bag);
    assert_eq!(r.expect.rows, Some(0));
    let r = record("MATCH ( x ) RETURN x NEXT FILTER x : ! % FINISH", MatchModeDefault::DifferentEdges);
    assert_eq!(r.expect.rows, Some(0));
}

#[test]
fn the_evaluator_reaches_past_the_witness_core() {
    // A selective prefix: the one match is the shortest.
    let r = record("MATCH ALL SHORTEST ( x ) -> ( y ) RETURN x", MatchModeDefault::DifferentEdges);
    assert_eq!(r.expect.tier, Tier::Bag, "{:?}", r.expect.evaluator);
    assert_eq!(r.expect.rows, Some(1));
    assert_eq!(r.graph.edges.len(), 1);
    // No graph at all: expressions on the unit table.
    let r = record("RETURN TRUE AS x NEXT FILTER x OR TRUE FINISH", MatchModeDefault::DifferentEdges);
    assert_eq!(r.expect.tier, Tier::Bag, "{:?}", r.expect.evaluator);
    assert!(!r.expect.result);
    assert!(r.graph.nodes.is_empty());
    let r = record("RETURN 1 + 2 * 3 AS x , 'a' || 'b' AS y , NULL = NULL AS z", MatchModeDefault::DifferentEdges);
    assert_eq!(r.expect.tier, Tier::Bag, "{:?}", r.expect.evaluator);
    let row = row(&r);
    assert_eq!(row["x"], serde_json::json!({ "kind": "Int", "value": 7 }));
    assert_eq!(row["y"], serde_json::json!({ "kind": "Str", "value": "ab" }));
    assert_eq!(row["z"], serde_json::json!({ "kind": "Null" }));
    // An exception the rules raise is the expected outcome.
    let r = record("RETURN 1 / 0 AS x", MatchModeDefault::DifferentEdges);
    assert_eq!(r.expect.outcome, "exception");
    assert_eq!(r.expect.status.as_deref(), Some("22012"));
    // What the implementation decides stays out: which rows LIMIT keeps without an order.
    let r = record("MATCH ( x ) , ( y ) RETURN x LIMIT 1", MatchModeDefault::DifferentEdges);
    assert_ne!(r.expect.tier, Tier::Bag);
}

#[test]
fn three_variables_bind_and_join_alike() {
    // The construction and the evaluator are not bound to two variables: three nodes in a
    // path, joined across two path patterns, with a shared variable.
    let r = witness("MATCH ( x ) -[ y ]-> ( z ) , ( z ) -[ w ]-> ( x ) RETURN x , y , z , w");
    assert_eq!(r.graph.nodes.len(), 2);
    assert_eq!(r.graph.edges.len(), 2);
    // The two-cycle matches twice: once from each node.
    let bag = r.expect.bag.as_ref().expect("a bag");
    assert_eq!(bag.len(), 2);
    let first = serde_json::to_value(&bag[0]).unwrap();
    let both = [node(0), node(1)];
    assert!(both.contains(&first["x"]) && both.contains(&first["z"]) && first["x"] != first["z"]);
    let r2 = witness("MATCH ( x : a ) -[ y ]-> ( z : b ) -[ w ]-> ( v : c ) WHERE x . k = 1 AND v . k = 2 RETURN x , z , v NEXT FILTER x : a AND v : c RETURN z");
    assert_eq!(row(&r2)["z"], node(1));
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
    let r = oracle(text, &parsed.tree.export(&ISO), None, Some(&params), MatchModeDefault::DifferentEdges, &Default::default());
    assert_eq!(r.parameters["b"], gql_proof::oracle::Value::Int(1));
    assert_ne!(r.expect.tier, Tier::Status, "{:?} {:?}", r.why, r.expect.evaluator);
    let r = oracle(text, &parsed.tree.export(&ISO), None, None, MatchModeDefault::DifferentEdges, &Default::default());
    assert_eq!(r.expect.tier, Tier::Status);
    let params = serde_json::json!([{ "name": "$b", "classes": ["list"] }]);
    let r = oracle(text, &parsed.tree.export(&ISO), None, Some(&params), MatchModeDefault::DifferentEdges, &Default::default());
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
    let r = oracle(text, &parsed.tree.export(&ISO), Some(&agree), None, MatchModeDefault::DifferentEdges, &Default::default());
    assert_ne!(r.expect.tier, Tier::Status);
    let disagree = serde_json::json!([{ "name": "x", "decl": ["edge"] }]);
    let r = oracle(text, &parsed.tree.export(&ISO), Some(&disagree), None, MatchModeDefault::DifferentEdges, &Default::default());
    assert!(r.why.iter().any(|w| w.contains("generation record")), "{:?}", r.why);
}

#[test]
fn data_modification_runs_on_the_evaluators_graph() {
    // 13.2: the inserted node is in the record and in the graph.
    let r = record("INSERT ( x : a { k : 1 } ) RETURN x . k AS k", MatchModeDefault::DifferentEdges);
    assert_eq!(r.expect.tier, Tier::Bag, "{:?}", r.expect.evaluator);
    assert_eq!(row(&r)["k"], serde_json::json!({ "kind": "Int", "value": 1 }));
    let r = record("INSERT ( : a ) NEXT MATCH ( x : a ) RETURN COUNT ( * ) AS n", MatchModeDefault::DifferentEdges);
    assert_eq!(row(&r)["n"], serde_json::json!({ "kind": "Int", "value": 1 }));
    // 13.3, 13.4: a property set and removed.
    let r = record("MATCH ( x ) SET x . k = 2 RETURN x . k AS k", MatchModeDefault::DifferentEdges);
    assert_eq!(row(&r)["k"], serde_json::json!({ "kind": "Int", "value": 2 }));
    let r = record("MATCH ( x : a { k : 1 } ) REMOVE x . k RETURN x . k IS NULL AS gone", MatchModeDefault::DifferentEdges);
    assert_eq!(row(&r)["gone"], serde_json::json!({ "kind": "Bool", "value": true }));
    // 13.5: a reference after DELETE is 22G11; an edge left on a deleted node is G1001;
    // DETACH takes the edge along.
    let r = record("MATCH ( x ) DELETE x RETURN x . k AS k", MatchModeDefault::DifferentEdges);
    assert_eq!(r.expect.status.as_deref(), Some("22G11"));
    let r = record("MATCH ( x : a ) -[ y ]-> ( z : b ) DELETE x RETURN 1 AS n", MatchModeDefault::DifferentEdges);
    assert_eq!(r.expect.status.as_deref(), Some("G1001"));
    let r = record("MATCH ( x : a ) -[ y ]-> ( z : b ) DETACH DELETE x NEXT MATCH ( v ) RETURN COUNT ( * ) AS n", MatchModeDefault::DifferentEdges);
    assert_eq!(row(&r)["n"], serde_json::json!({ "kind": "Int", "value": 1 }));
}

#[test]
fn inline_calls_and_statements_after_finish() {
    // 15.2: the body runs on the record restricted to the scope; its rows join the record.
    let r = record("RETURN 2 AS a NEXT CALL ( a ) { RETURN a + 1 AS b } RETURN a , b", MatchModeDefault::DifferentEdges);
    assert_eq!(row(&r)["b"], serde_json::json!({ "kind": "Int", "value": 3 }));
    // An omitted result leaves the record; OPTIONAL keeps a record with no rows.
    let r = record("CALL { FINISH } NEXT RETURN 1 AS n", MatchModeDefault::DifferentEdges);
    assert_eq!(row(&r)["n"], serde_json::json!({ "kind": "Int", "value": 1 }));
    // 9.2 GR 3 a ii: after an omitted result the next statement starts on the unit table.
    let r = record("FINISH NEXT RETURN 1 AS n", MatchModeDefault::DifferentEdges);
    assert_eq!(r.expect.rows, Some(1));
    // 22007 for a date string that is not a date (20.x), 22G05 for a record with no
    // admitted field names (20.27 SR 2).
    let r = record("ORDER BY DATE ( '2024-13-01' ) FINISH", MatchModeDefault::DifferentEdges);
    assert_eq!(r.expect.status.as_deref(), Some("22007"));
    let r = record("ORDER BY DATE ( { } ) FINISH", MatchModeDefault::DifferentEdges);
    assert_eq!(r.expect.status.as_deref(), Some("22G05"));
}
