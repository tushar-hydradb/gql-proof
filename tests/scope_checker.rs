use gql_proof::bnf;
use gql_proof::cfg::Cfg;
use gql_proof::parse::Parser;
use gql_proof::tokens::Grammar;
use gql_proof::verify::{Verifier, Violation, scope};
use gql_proof::{ISO_BNF_XML, MatchModeDefault};
use std::cell::RefCell;
use std::sync::LazyLock;

static ISO_BNF: LazyLock<bnf::Bnf> = LazyLock::new(|| bnf::parse(ISO_BNF_XML).unwrap());
static ISO: LazyLock<Cfg> = LazyLock::new(|| Cfg::from_bnf(&ISO_BNF));

/// The scoping violations of `text`, the same for every tree of it the verifier accepts (with
/// the syntax rules on: a tree that breaks 13.1 SR 5 is not one the generator makes).
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
            if verifier.verify(&plain, &n.render(&ISO)).is_empty() {
                let mut rules: Vec<_> = scope::check(&plain).iter().map(|v| v.rule).collect();
                rules.sort();
                verdicts.borrow_mut().push((rules, plain));
            }
            false
        })
        .unwrap_or_else(|e| panic!("{text:?}: {e}"));
    let verdicts = verdicts.into_inner();
    assert!(
        !verdicts.is_empty(),
        "{text:?}: no tree passes the verifier ({} trees)",
        parsed.trees
    );
    for (rules, _) in &verdicts[1..] {
        assert_eq!(
            rules, &verdicts[0].0,
            "{text:?}: the verdict depends on the tree"
        );
    }
    scope::check(&verdicts[0].1)
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

#[test]
fn matches_bind_and_join() {
    ok("MATCH (a) RETURN a");
    ok("MATCH (a)-[e]->(b) RETURN a, e, b");
    ok("MATCH (a) MATCH (a)-[e]->(b) RETURN b");
    ok("MATCH (a), (a)-[e]->(b) RETURN e");
    ok("MATCH (a)-[e]->(b)<-[f]-(a) RETURN f");
    ok("OPTIONAL MATCH (a) RETURN a");
    ok("MATCH (a) OPTIONAL MATCH (a)-[e]->(b) RETURN a, b");
    ok("OPTIONAL { MATCH (a) MATCH (a)-[e]->(b) } RETURN e");
    ok("MATCH (a) WHERE a.k = 1 RETURN a");
    ok("MATCH (a)-[e]->(b) WHERE a.k = b.k RETURN e");
    ok("MATCH (a WHERE a.k = 1) RETURN a");
    ok("MATCH (a {k: 1})-[e {k: a.k}]->(b) RETURN e");
    ok("MATCH (a)-[e]->(b WHERE b.k = a.k) RETURN e");
    ok("MATCH p = (a)-[e]->(b) RETURN p");
    ok("MATCH p = (a)-[e]->(b) WHERE p IS NOT NULL RETURN p");
    ok("MATCH (a)-[e]->(b) YIELD a, b RETURN a, b");
    ok("MATCH (a) MATCH (a)-[e]->(b) YIELD b RETURN a, b");
    // 20.12 SR 8: names come from the record or the table
    bad("RETURN a", "20.12 SR 8");
    bad("MATCH (a) RETURN b", "20.12 SR 8");
    bad("MATCH (a) WHERE b.k = 1 RETURN a", "20.12 SR 8");
    // 16.3 SR 12: YIELD names distinct variables of the pattern
    bad("MATCH (a)-[e]->(b) YIELD a, a RETURN a", "16.3 SR 12");
    bad("MATCH (a)-[e]->(b) YIELD c RETURN a", "16.3 SR 12");
    bad("MATCH (a)-[e]->(b) YIELD a RETURN b", "20.12 SR 8");
    // 16.3 SR 20: a join compares like with like
    bad("MATCH (a)-[e]->(b) MATCH (e) RETURN a", "16.3 SR 20");
    bad("MATCH p = (a) MATCH (p) RETURN a", "16.3 SR 20");
}

#[test]
fn pattern_variables_are_one_thing_each() {
    // 16.4 SR 5
    bad("MATCH (a)-[a]->(b) RETURN a", "16.4 SR 5");
    bad("MATCH (a), ()-[a]->() RETURN a", "16.4 SR 5");
    // 4.11.4, 16.3 SR 4
    bad("MATCH p = (a), p = (b) RETURN p", "4.11.4");
    bad("MATCH a = (a)-[e]->(b) RETURN a", "16.3 SR 4");
    bad("MATCH (s = (a)-[e]->(b)) (s) RETURN a", "16.3 SR 4");
    // 16.3 SR 7: a subpath variable is no incoming name
    bad("MATCH (s) MATCH (s = (a)-[e]->(b)) RETURN a", "16.3 SR 9");
    ok("MATCH (s = (a)-[e]->(b)) RETURN a");
    // subpath variables are not referenceable (4.11.5, NOTE 79)
    bad("MATCH (s = (a)-[e]->(b)) RETURN s", "20.12 SR 8");
}

#[test]
fn degrees_of_exposure() {
    // 16.7 SR 22 e: a quantified variable is a group
    ok("MATCH ((a)-[e]->(b)){2} RETURN COUNT(e) AS n");
    ok("MATCH (x) ((a)-[e]->(b)){1,3} (y) WHERE SUM(e.k) > 1 RETURN x, y");
    // reading: a group variable is a group list, which a RETURN may return as is
    ok("MATCH ((a)-[e]->(b)){2} RETURN a");
    // 20.1 SR 4-6: but it has no properties
    bad("MATCH ((a)-[e]->(b)){2} RETURN a.k AS k", "20.1 SR 4-6");
    bad(
        "MATCH ((a)-[e]->(b)){2} WHERE e.k = 1 RETURN a",
        "20.1 SR 4-6",
    );
    bad(
        "MATCH ((a)-[e]->(b)){2} RETURN ELEMENT_ID(a) AS i",
        "20.10 SR 2",
    );
    // 20.1 SR 7: a horizontal aggregate aggregates exactly one group variable
    bad(
        "MATCH (a)-[e]->(b) WHERE SUM(e.k) > 1 RETURN a",
        "20.1 SR 7",
    );
    bad("MATCH (a) FILTER COUNT(*) > 1 RETURN a", "20.1 SR 7");
    bad(
        "MATCH ((a)-[e]->(b)){2} WHERE SUM(a.k + e.k) > 1 RETURN a",
        "20.1 SR 7",
    );
    // 16.7 SR 22 c: a concatenation joins only unconditional singletons
    bad("MATCH (a) ((a)-[e]->(b)){2} RETURN e", "16.7 SR 22");
    bad("MATCH (a) ((a)-[e]->(b))? RETURN e", "16.7 SR 22");
    ok("MATCH (a) ((a)-[e]->(b)) RETURN e");
    // 16.4 SR 3: so does a comma
    bad("MATCH (a), ((a)-[e]->(b)){2} RETURN e", "16.4 SR 3");
    bad("MATCH ((a)-[e]->(b))?, (a) RETURN e", "16.4 SR 3");
    // 16.7 SR 22 d: a union exposes a variable as unconditional only from every operand
    ok("MATCH (a) ((a)-[e]->(b) | (a)-[f]->(b)) RETURN a, b");
    bad(
        "MATCH (b) ((a)-[e]->(b) | (a)-[f]->(c)) RETURN a",
        "16.7 SR 22",
    );
    // 16.3 SR 16: a join keeps groups apart from singletons
    bad("MATCH ((a)-[e]->(b)){2} MATCH (e) RETURN b", "16.3 SR 16");
    // 20.12 SR 11: a non-local reference in a parenthesized WHERE is a singleton
    bad(
        "MATCH ((a)-[e]->(b)){2} (c WHERE c.k = SUM(e.k)) RETURN c",
        "20.12 SR 11",
    );
    ok("MATCH (c) ((a)-[e]->(b) WHERE a.k = c.k){2} RETURN c");
    ok("MATCH (((a)-[e]->(b)){2} WHERE SUM(e.k) > 1) RETURN a");
    // 20.12 SR 12: never an unbounded group
    bad(
        "MATCH ANY SHORTEST (a) (((b)-[e]->(c))* WHERE COUNT(e.k) > 1) RETURN a",
        "20.12 SR 12",
    );
    ok("MATCH ANY SHORTEST (a) (TRAIL ((b)-[e]->(c))* WHERE COUNT(e.k) > 1) RETURN a");
    ok("MATCH TRAIL (a) (((b)-[e]->(c))* WHERE COUNT(e.k) > 1) RETURN a");
}

#[test]
fn where_clauses_in_patterns() {
    // 16.7 SR 21: an element WHERE needs a variable
    bad("MATCH (WHERE 1 = 1) RETURN 1 AS x", "16.7 SR 21");
    // 16.7 SR 24: a parenthesized WHERE references no path variable
    bad(
        "MATCH p = ((a)-[e]->(b) WHERE p IS NOT NULL) RETURN a",
        "16.7 SR 24",
    );
    bad("MATCH p = (a WHERE p IS NOT NULL) RETURN a", "16.7 SR 24");
    // 16.7 SR 11: a union operand sees its own variables and those outside the union
    bad(
        "MATCH ((a)-[e]->(b) | (c)-[f]->(d WHERE d.k = a.k)) RETURN 1 AS x",
        "16.7 SR 11",
    );
    ok("MATCH (x) ((a)-[e]->(b WHERE b.k = x.k) | (c)-[f]->(d WHERE d.k = x.k)) RETURN x");
    // 16.6 SR 8: a selective path pattern references only its own variables
    bad(
        "MATCH (x), ANY SHORTEST (a)-[e]->(b WHERE b.k = x.k) RETURN a",
        "16.6 SR 8",
    );
    ok("MATCH ANY SHORTEST (a)-[e]->(b WHERE b.k = a.k) RETURN a");
    // 16.6 SR 7: its strict interior variables are its own
    bad(
        "MATCH ANY SHORTEST (a)-[e]->(b), (c)-[e]->(d) RETURN a",
        "16.6 SR 7",
    );
    ok("MATCH ANY SHORTEST (a)-[e]->(b), (b)-[f]->(c) RETURN a");
    // 16.3 SR 25: a pattern expression sees the incoming names too
    ok("MATCH (a) MATCH (b WHERE b.k = a.k) RETURN b");
    ok("LET x = 1 MATCH (a WHERE a.k = x) RETURN a");
}

#[test]
fn subqueries_are_correlated() {
    ok("MATCH (a) WHERE EXISTS { (a)-[e]->(b) } RETURN a");
    ok("MATCH (a) WHERE EXISTS { MATCH (a)-[e]->(b) RETURN b } RETURN a");
    ok("MATCH (a) WHERE EXISTS { MATCH (a)-[e]->(b) MATCH (b)-[f]->(c) } RETURN a");
    ok("MATCH (a) RETURN VALUE { MATCH (a)-[e]->(b) RETURN COUNT(*) AS n } AS n");
    bad(
        "MATCH (a) WHERE EXISTS { (b)-[e]->(c) WHERE c.k = d.k } RETURN a",
        "20.12 SR 8",
    );
    bad(
        "MATCH (a) WHERE EXISTS { MATCH (a)-[e]->(b) RETURN b } RETURN b",
        "20.12 SR 8",
    );
    // 20.5: LET ... IN ... END
    ok("MATCH (a) RETURN LET x = a.k, y = 2 IN x + y END AS z");
    bad("MATCH (a) RETURN LET a = 1 IN a END AS z", "20.5 SR 3");
    bad("RETURN LET x = 1, x = 2 IN x END AS z", "20.5 SR 4");
    bad("RETURN LET x = 1, y = x IN y END AS z", "20.12 SR 8");
    bad("RETURN LET x = 1 IN x END + x AS z", "20.12 SR 8");
}

#[test]
fn let_for_filter() {
    ok("MATCH (a) LET x = 1 RETURN a, x");
    ok("MATCH (a) LET x = a.k LET y = x RETURN y");
    ok("LET x = 1, y = 2 RETURN x, y");
    ok("FOR x IN [1] RETURN x");
    ok("FOR x IN [1, 2] WITH ORDINALITY i RETURN x, i");
    ok("MATCH (a) FILTER a.k > 1 RETURN a");
    ok("MATCH (a) FILTER WHERE a.k > 1 RETURN a");
    // 10.3 SR 7, and 14.7 as Cor 1 rewrites it
    bad("MATCH (a) LET a = 1 RETURN a", "10.3 SR 7");
    bad("LET x = 1, x = 2 RETURN x", "15.1 SR 9");
    bad("LET x = 1, y = x RETURN y", "20.12 SR 8");
    // 14.8 SR 10-11
    bad("FOR x IN [1] FOR x IN [2] RETURN x", "14.8 SR 11");
    bad("FOR x IN [1] WITH OFFSET x RETURN x", "14.8 SR 10");
    bad("FOR x IN y RETURN x", "20.12 SR 8");
    bad("FILTER a = 1 RETURN 1 AS x", "20.12 SR 8");
}

#[test]
fn return_projects() {
    ok("RETURN 1 AS x");
    ok("MATCH (a) RETURN a AS b");
    ok("MATCH (a) RETURN a.k AS k ORDER BY a.k");
    ok("MATCH (a) RETURN a.k AS k ORDER BY k");
    ok("MATCH (a) RETURN *");
    ok("MATCH (a) RETURN DISTINCT a.k AS k ORDER BY k");
    ok("MATCH (a)-[e]->(b) RETURN a, COUNT(e) AS n GROUP BY a");
    ok("MATCH (a)-[e]->(b) RETURN a.k AS k, COUNT(e) AS n GROUP BY k ORDER BY k");
    ok("MATCH (a)-[e]->(b) RETURN COUNT(e) AS n ORDER BY n");
    ok("MATCH (a) ORDER BY a.k LIMIT 1 RETURN a");
    // 14.11 SR 8: an expression needs an alias
    bad("MATCH (a) RETURN a.k", "14.11 SR 8");
    bad("RETURN 1", "14.11 SR 8");
    // SR 11: column names are distinct
    bad("MATCH (a) RETURN a, a.k AS a", "14.11 SR 11");
    // SR 6: RETURN * needs columns
    bad("RETURN *", "14.11 SR 6");
    // SR 10: with GROUP BY an item groups or aggregates, and sees no ungrouped name
    bad(
        "MATCH (a)-[e]->(b) RETURN a, b.k AS k GROUP BY a",
        "14.11 SR 10",
    );
    bad(
        "MATCH (a)-[e]->(b) RETURN a, b.k + COUNT(e) AS k GROUP BY a",
        "20.12 SR 8",
    );
    bad("MATCH (a) RETURN a GROUP BY c", "20.12 SR 8");
    // 14.10 SR 4
    bad(
        "MATCH (a) RETURN DISTINCT a.k AS k ORDER BY a.j",
        "14.10 SR 4",
    );
    bad(
        "MATCH (a)-[e]->(b) RETURN a, COUNT(e) AS n GROUP BY a ORDER BY b",
        "14.10 SR 4",
    );
    bad("MATCH (a) RETURN COUNT(a) AS n ORDER BY a.k", "14.10 SR 4");
    bad("MATCH (a) RETURN a ORDER BY COUNT(a)", "14.10 SR 4");
    // the projection ends the statement
    bad("MATCH (a) RETURN a.k AS k NEXT RETURN a", "20.12 SR 8");
}

#[test]
fn next_and_composites() {
    ok("MATCH (a) RETURN a AS b NEXT RETURN b");
    ok("MATCH (a) RETURN a NEXT MATCH (a)-[e]->(b) RETURN b");
    ok("MATCH (a) RETURN a.k AS k, a NEXT YIELD k AS j RETURN j");
    ok("MATCH (a) RETURN a UNION MATCH (a) RETURN a");
    ok("MATCH (a) RETURN a AS x UNION ALL MATCH (b) RETURN b AS x");
    ok("MATCH (a) RETURN a OTHERWISE RETURN 1 AS a");
    bad("MATCH (a) RETURN a NEXT RETURN b", "20.12 SR 8");
    bad("MATCH (a) FINISH NEXT RETURN a", "20.12 SR 8");
    bad("MATCH (a) RETURN a NEXT YIELD b RETURN b", "16.14 SR 7");
    bad(
        "MATCH (a) RETURN a, a.k AS k NEXT YIELD a AS x, k AS x RETURN x",
        "16.14 SR 6",
    );
    // 14.2 SR 10
    bad("MATCH (a) RETURN a UNION MATCH (b) RETURN b", "14.2 SR 10");
    bad(
        "RETURN 1 AS x INTERSECT RETURN 1 AS x, 2 AS y",
        "14.2 SR 10",
    );
    // 14.2 SR 8-9: each operand starts from the same scope
    bad("MATCH (a) RETURN a UNION RETURN a", "20.12 SR 8");
}

#[test]
fn calls() {
    ok("MATCH (a) CALL (a) { MATCH (a)-[e]->(b) RETURN b } RETURN a, b");
    ok("MATCH (a) CALL { MATCH (a)-[e]->(b) RETURN b } RETURN a, b");
    ok("MATCH (a) OPTIONAL CALL (a) { MATCH (a)-[e]->(b) RETURN b } RETURN b");
    ok("CALL { RETURN 1 AS x } RETURN x");
    ok("MATCH (a) CALL () { RETURN 1 AS x } RETURN a, x");
    // 15.2 SR 5-7
    bad(
        "MATCH (a) CALL (b) { RETURN 1 AS x } RETURN x",
        "20.12 SR 8",
    );
    bad("MATCH (a) CALL () { RETURN a } RETURN a", "20.12 SR 8");
    bad(
        "MATCH (a) CALL (a, a) { RETURN 1 AS x } RETURN x",
        "15.2 SR 6",
    );
    // 15.1 SR 9 as Cor 1 corrects it
    bad("MATCH (a) CALL { RETURN 1 AS a } RETURN a", "15.1 SR 9");
    // named calls: arguments are correlated, YIELD names new columns
    ok("MATCH (a) CALL p(a.k) YIELD x RETURN a, x");
    bad("MATCH (a) CALL p(b) YIELD x RETURN x", "20.12 SR 8");
    bad("MATCH (a) CALL p() YIELD a RETURN a", "15.1 SR 9");
}

#[test]
fn definitions_and_data_modification() {
    ok("VALUE x = 1 RETURN x");
    ok("VALUE x = 1 VALUE y = x RETURN y");
    ok("GRAPH g = CURRENT_GRAPH TABLE t = { RETURN 1 AS x } RETURN 1 AS z");
    bad("VALUE x = 1 VALUE x = 2 RETURN x", "10.3 SR 7");
    bad("VALUE x = y RETURN x", "20.12 SR 8");
    // 9.2 SR 12 c
    bad("VALUE x = 1 RETURN x NEXT RETURN x", "9.2 SR 12");
    ok("INSERT (a:L)-[e:R]->(b) RETURN a, e, b");
    ok("MATCH (a) INSERT (a)-[e:R]->(b {k: a.k})");
    ok("MATCH (a) SET a.k = 1 REMOVE a:L");
    ok("MATCH (a) SET a = {k: 1}");
    ok("MATCH (a)-[e]->(b) DETACH DELETE a, e");
    bad("SET a.k = 1", "20.12 SR 8");
    bad("MATCH (a) DELETE b", "20.12 SR 8");
    bad("INSERT (a {k: 1})-[:R]->(b {k: a.k})", "20.12 SR 8");
    // 16.5 SR 10-11
    bad("MATCH (a) INSERT (a:L)", "16.5 SR 10");
    bad("MATCH (a)-[e]->(b) INSERT (a)-[e:R]->(b)", "16.5 SR 10");
    bad("INSERT (a)-[e:R]->(b), (c)-[e:R]->(d)", "16.5 SR 11");
    bad("INSERT (a:L), (a:M)", "16.5 SR 10");
    // 13.3 SR 3-5
    bad("MATCH p = (a) SET p.k = 1", "13.3 SR 3");
    bad("MATCH (a) SET a.k = 1, a.k = 2", "13.3 SR 4");
    bad("MATCH (a) SET a = {k: 1}, a.j = 2", "13.3 SR 5");
}

#[test]
fn select_without_from_is_a_return() {
    ok("SELECT 1 AS x");
    ok("MATCH (a) RETURN a NEXT SELECT a");
    bad("SELECT 1", "14.12 SR 8");
    bad("SELECT b", "20.12 SR 8");
}

#[test]
fn subpath_variables() {
    // 16.3 SR 7, 9
    bad("VALUE s = 1 MATCH (s = (a)-[e]->(b)) RETURN a", "16.3 SR 7");
    // 16.7 SR 22 b-c, 16.4 SR 4, 16.7 SR 10
    bad("MATCH (s = (s = (a)-[e]->(b))) RETURN a", "16.7 SR 22");
    bad(
        "MATCH (s = (a)-[e]->(b)) (s = (c)-[f]->(d)) RETURN a",
        "16.7 SR 22",
    );
    bad(
        "MATCH (s = (a)-[e]->(b)), (s = (c)-[f]->(d)) RETURN a",
        "16.4 SR 4",
    );
    bad(
        "MATCH ((s = (a)-[e]->(b)) |+| (s = (c)-[f]->(d))) RETURN 1 AS x",
        "16.7 SR 10",
    );
    // 4.11.4: union operands may share one
    ok("MATCH ((s = (a)-[e]->(b)) | (s = (a)-[f]->(b))) RETURN a");
}

#[test]
fn kinds_and_degrees_travel() {
    ok("MATCH (a) LET x = a RETURN x NEXT MATCH (x)-[e]->(b) RETURN b");
    ok("MATCH ((a)-[e]->(b)){2} FOR x IN e RETURN x.k AS k");
    ok("LET VALUE x = 1 RETURN x");
    // reading: a value of unknown type may join a pattern variable
    ok("MATCH (a) LET x = a.k MATCH (x) RETURN x");
    bad(
        "MATCH ((a)-[e]->(b)){2} RETURN a AS x NEXT RETURN x.k AS k",
        "20.1 SR 4-6",
    );
    bad(
        "MATCH ((a)-[e]->(b)){2} WHERE e IS DIRECTED RETURN a",
        "19.8 SR 2",
    );
    bad("MATCH ((a)-[e]->(b)){2} WHERE a:L RETURN b", "19.9 SR 2");
    bad(
        "GRAPH g = CURRENT_GRAPH MATCH (g) RETURN 1 AS x",
        "16.3 SR 20",
    );
    ok("MATCH (a)-[e]->(b) WHERE e IS DIRECTED AND a:L RETURN a");
    ok("MATCH (a) WHERE EXISTS ((a)-[e]->(b)) RETURN a");
    ok("MATCH (a)-[e]->(b) RETURN COUNT(e) AS n GROUP BY a ORDER BY a");
}

#[test]
fn focused_statements() {
    ok("USE g MATCH (a) RETURN a");
    ok("USE g { MATCH (a) RETURN a }");
    // 16.2 SR 3-4: the graph expression sees the record, not the table
    bad(
        "USE g MATCH (a) RETURN a NEXT USE VARIABLE a MATCH (b) RETURN b",
        "20.12 SR 8",
    );
    // 14.2 SR 5
    bad("MATCH (a) FINISH UNION MATCH (a) FINISH", "14.2 SR 5");
    bad("{ FINISH } UNION RETURN 1 AS x", "14.2 SR 5");
    // 16.14 SR 4: an unaliased yield item is a binding variable
    bad(
        "RETURN 1 AS \"x\" NEXT YIELD \"x\" RETURN 1 AS y",
        "16.14 SR 4",
    );
}

#[test]
fn a_subquery_body_yields_a_table() {
    ok("RETURN EXISTS { RETURN 1 AS y } AS x");
    ok("RETURN EXISTS { MATCH (y) RETURN y } AS x");
    ok("RETURN EXISTS { FINISH NEXT RETURN 1 AS y } AS x");
    ok("RETURN VALUE { RETURN count(*) AS y } AS x");
    ok("RETURN VALUE { RETURN 1 AS y LIMIT 1 } AS x");
    ok("RETURN VALUE { RETURN 1 AS y LIMIT 0x1 } AS x");
    ok("RETURN VALUE { { RETURN count(*) AS y } } AS x");
    ok("{ FINISH } NEXT RETURN 1 AS x");
    bad("RETURN EXISTS { FINISH } AS x", "19.4 SR 5");
    bad("RETURN EXISTS { { FINISH } } AS x", "19.4 SR 5");
    bad(
        "RETURN EXISTS { RETURN 1 AS y NEXT FINISH } AS x",
        "19.4 SR 5",
    );
    bad("RETURN EXISTS { MATCH (y) FINISH } AS x", "19.4 SR 5");
    bad("RETURN VALUE { FINISH } AS x", "20.6 SR 8");
    // 13.1 SR 3: a data-modifying body without a result statement finishes implicitly.
    bad("RETURN EXISTS { INSERT (y) } AS x", "19.4 SR 5");
    bad("RETURN EXISTS { CALL { FINISH } } AS x", "19.4 SR 5");
    // 12.1 SR 4: a catalog-modifying statement has the empty type.
    bad("RETURN EXISTS { CREATE SCHEMA /s } AS x", "19.4 SR 5");
    // 20.6 SR 10: at most one row.
    bad("RETURN VALUE { RETURN 1 AS y } AS x", "20.6 SR 10");
    bad("RETURN VALUE { RETURN 1 AS y LIMIT 2 } AS x", "20.6 SR 10");
    bad(
        "RETURN VALUE { MATCH (z) RETURN count(*) AS y GROUP BY z } AS x",
        "20.6 SR 10",
    );
    bad(
        "RETURN VALUE { RETURN count(*) AS y UNION RETURN count(*) AS y } AS x",
        "20.6 SR 5",
    );
    bad("RETURN VALUE { { RETURN 1 AS y } } AS x", "20.6 SR 10");
}
