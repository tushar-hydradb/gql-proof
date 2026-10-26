use gql_proof::ISO_BNF_XML;
use gql_proof::MatchModeDefault;
use gql_proof::bnf;
use gql_proof::cfg::Cfg;
use gql_proof::parse::Parser;
use gql_proof::tokens::Grammar;
use gql_proof::verify::{Verifier, Violation, types};
use std::cell::RefCell;
use std::sync::LazyLock;

static ISO_BNF: LazyLock<bnf::Bnf> = LazyLock::new(|| bnf::parse(ISO_BNF_XML).unwrap());
static ISO: LazyLock<Cfg> = LazyLock::new(|| Cfg::from_bnf(&ISO_BNF));

/// The grammar sentences are parsed with: the ISO grammar refined by the syntax rules, so a
/// parse of the wrong statement kind (9.1 SR 4-7) is no tree the parser spends its limit on.
static PARSE: LazyLock<Cfg> = LazyLock::new(|| {
    let start = ISO.require("GQL-program").unwrap();
    gql_proof::refine::refine(
        &ISO,
        &gql_proof::refine::all_rules(MatchModeDefault::Portable),
        start,
    )
    .unwrap()
    .cfg
});

/// Rules stated on one derivation a bare primary can take among others, so they hold on some
/// trees of a sentence and fail on others (H3): 20.1 SR 2, 3; 11.1 SR 3 and 11.2 SR 4, whose
/// object expression primary (`"g"`, `x . a`) is also a catalog reference on another tree.
const PER_TREE: &[&str] = &[
    "20.1 SR 2",
    "20.1 SR 3",
    "11.1 SR 3",
    "11.2 SR 4",
    // the category over a bare primary, which another tree puts elsewhere
    "20.21 SR 3 primary",
    "20.23 SR 2 primary",
    "20.23 SR 4 primary",
    "20.15 SR 1 primary",
    "20.13 SR 2 primary",
    "20.20 SR 3 primary",
    "20.1 SR 4-6 primary",
    "20.28 SR 1 primary",
    "11.1 SR 3 primary",
    "11.2 SR 4 primary",
    "20.26 SR 1 moved",
];

/// The typing violations of every tree of `text` the verifier accepts.
fn verdicts(text: &str, verifier: &Verifier) -> Vec<Vec<Violation>> {
    // The refined grammar settles what the syntax rules disambiguate; a sentence it does not
    // derive (one a generator reading keeps out, a probe of a rule only the checker keeps) is
    // read with the ISO grammar.
    match try_verdicts_in(&PARSE, text, verifier) {
        Some(v) => v,
        None => verdicts_in(&ISO, text, verifier),
    }
}

fn try_verdicts_in(grammar: &Cfg, text: &str, verifier: &Verifier) -> Option<Vec<Vec<Violation>>> {
    let tokens = Grammar::new(&ISO_BNF);
    let parser = Parser::new(grammar, &tokens, "GQL-program").unwrap();
    let verdicts = RefCell::new(Vec::new());
    parser
        .parse(text, |n| {
            let plain = n.export(grammar);
            if verifier.verify(&plain, &n.render(grammar)).is_empty() {
                verdicts.borrow_mut().push(types::check(&plain));
            }
            false
        })
        .ok()?;
    let verdicts = verdicts.into_inner();
    (!verdicts.is_empty()).then_some(verdicts)
}

fn verifier() -> Verifier<'static> {
    Verifier::new(Grammar::new(&ISO_BNF)).with_scope()
}

fn verdicts_in(grammar: &Cfg, text: &str, verifier: &Verifier) -> Vec<Vec<Violation>> {
    let tokens = Grammar::new(&ISO_BNF);
    let parser = Parser::new(grammar, &tokens, "GQL-program").unwrap();
    let verdicts = RefCell::new(Vec::new());
    // Accept no tree, so the parser offers every one up to its limit.
    let parsed = parser
        .parse(text, |n| {
            let plain = n.export(grammar);
            if verifier.verify(&plain, &n.render(grammar)).is_empty() {
                verdicts.borrow_mut().push(types::check(&plain));
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
    verdicts
}

/// The typing violations of `text` but the `PER_TREE` rules, the same for every tree of it the
/// verifier accepts (the parser offers trees up to a limit, so a tree avoiding a `PER_TREE` rule
/// need not be among them). Types are only read on trees whose names are in scope: `TABLE / a`
/// also derives as a division of two unbound variables.
fn violations(text: &str) -> Vec<Violation> {
    violations_in(text, Verifier::new(Grammar::new(&ISO_BNF)).with_scope())
}

fn violations_in(text: &str, verifier: Verifier) -> Vec<Violation> {
    let all = verdicts(text, &verifier);
    let rules = |v: &Vec<Violation>| {
        let mut r: Vec<&str> = v
            .iter()
            .map(|v| v.rule)
            .filter(|r| !PER_TREE.contains(r))
            .collect();
        r.sort();
        r
    };
    for v in &all[1..] {
        assert_eq!(
            rules(v),
            rules(&all[0]),
            "{text:?}: the verdict depends on the tree"
        );
    }
    let mut first = all.into_iter().next().unwrap();
    first.retain(|v| !PER_TREE.contains(&v.rule));
    first
}

/// `rule` is reported on some tree of `text` (a `PER_TREE` rule).
#[track_caller]
fn bad_on_a_tree(text: &str, rule: &str) {
    let all = verdicts(text, &Verifier::new(Grammar::new(&ISO_BNF)).with_scope());
    assert!(
        all.iter().any(|v| v.iter().any(|v| v.rule == rule)),
        "{text:?}: expected {rule} on some tree, got {all:#?}"
    );
}

/// Valid on some tree: a string function derives as a character and as a byte string form,
/// and the tree of the operand's own kind is valid (H3).
#[track_caller]
fn ok_some_tree(text: &str) {
    let trees = verdicts(text, &verifier());
    assert!(trees.iter().any(Vec::is_empty), "{text:?}: {trees:#?}");
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
fn literals() {
    // 21.2 SR 18-19, 21, 53, 58, 60, 63, 66, 71
    ok("RETURN 1 AS a, 1.5 AS b, 1E3 AS c, 1.5F AS d, 0x1F AS e, 2M AS f, .5 AS g");
    ok("RETURN 'a' AS a, X'0F' AS b, TRUE AS c, UNKNOWN AS d, NULL AS e");
    ok("RETURN DATE '2020-01-01' AS a, TIME '10:00:00' AS b");
    ok("RETURN DATETIME '2020-01-01T10:00:00' AS a, DURATION 'P1Y' AS b");
    ok("RETURN INTERVAL '1' YEAR AS a, DURATION 'P1DT1H' AS b");
    ok("RETURN [1, 2] AS a, [] AS b, {k: 1, l: 'a'} AS c, RECORD {} AS d");
    // 22.19 SR 4 d: numbers combine, exact with approximate
    ok("RETURN [1, 1.5, 1E3] AS x");
    // 20.17 SR 3 a, 22.19 SR 4 b, without GV65
    bad("RETURN [1, 'a'] AS x", "22.19 SR 4");
    bad(
        "RETURN [DATE '2020-01-01', TIME '10:00:00'] AS x",
        "22.19 SR 4",
    );
    // a null element combines with anything
    ok("RETURN [1, NULL] AS x");
    // 20.19 SR 2
    bad("RETURN {k: 1, k: 2} AS x", "20.19 SR 2");
}

#[test]
fn numeric_expressions() {
    // 20.21 SR 3
    ok("RETURN 1 + 2 AS x");
    ok("RETURN 1 - 2 * 3 / 4 AS x");
    ok("RETURN -1 AS x, +1.5 AS y, -(2 * 3) AS z");
    ok("RETURN 1 + NULL AS x");
    bad("RETURN SESSION_USER / SESSION_USER AS x", "20.21 SR 3");
    bad("RETURN +'a' AS x", "20.21 SR 3");
    bad("RETURN 1 + 'a' AS x", "20.21 SR 3");
    bad("RETURN TRUE * 2 AS x", "20.21 SR 3");
    bad("RETURN [1] - [2] AS x", "20.21 SR 3");
    bad("RETURN -TRUE AS x", "20.21 SR 3");
    // a parameter's type is unknown
    ok("RETURN $p + 1 AS x");
}

#[test]
fn string_expressions() {
    // 20.23 SR 2, 4
    ok("RETURN 'a' || 'b' AS x");
    ok("RETURN X'0F' || X'A0' AS x");
    ok("RETURN SESSION_USER || 'a' AS x");
    bad("RETURN 'a' || 1 AS x", "20.23 SR 2");
    bad("RETURN 'a' || X'0F' AS x", "20.23 SR 4");
    bad("RETURN TRUE || FALSE AS x", "20.23 SR 2");
}

#[test]
fn temporal_expressions() {
    // 4.16.6.4 Table 1, 20.26, 20.28
    // 'P1D' alone fails 21.2 SR 68 as the verifier reads <iso8601 days and time>
    // a date moved by a duration: refused by the 20.26 SR 1 reading (the fifteenth review)
    bad_on_a_tree("RETURN CURRENT_DATE + DURATION 'P1DT0H' AS x", "20.26 SR 1 moved");
    ok("RETURN LOCAL_TIMESTAMP - DURATION 'PT1H' AS x");
    ok("RETURN DURATION 'PT1H' + CURRENT_TIMESTAMP AS x");
    ok("RETURN DURATION 'P1Y' + DURATION 'P2M' AS x");
    ok("RETURN DURATION 'P1Y' * 2 AS x, 2 * DURATION 'P1Y' AS y");
    ok("RETURN DURATION 'PT1H' / 2 AS x, -DURATION 'PT1H' AS y");
    ok("RETURN ABS(DURATION 'PT1H') AS x, ABS(-1) AS y");
    bad("RETURN LOCAL_TIME + SESSION_USER AS x", "4.16.6.4");
    // a datetime function is no primary without parentheses
    bad("RETURN CURRENT_DATE + (CURRENT_DATE) AS x", "4.16.6.4");
    bad("RETURN CURRENT_DATE - (CURRENT_DATE) AS x", "4.16.6.4");
    bad("RETURN DURATION 'PT1H' - (CURRENT_DATE) AS x", "4.16.6.4");
    bad("RETURN 2 / DURATION 'PT1H' AS x", "4.16.6.4");
    bad("RETURN (CURRENT_DATE) * 2 AS x", "4.16.6.4");
    bad("RETURN (CURRENT_DATE) + 1 AS x", "4.16.6.4");
    // 20.28 SR 1 a
    bad("RETURN DURATION 'P1Y' + DURATION 'PT1H' AS x", "20.28 SR 1");
    bad(
        "RETURN DURATION 'P1M' - INTERVAL '1' DAY AS x",
        "20.28 SR 1",
    );
    // 20.28 SR 3
    ok("RETURN DURATION_BETWEEN(CURRENT_DATE, DATE '2020-01-01') AS x");
    ok("RETURN DURATION_BETWEEN(LOCAL_TIME, LOCAL_TIME) AS x");
    bad(
        "RETURN DURATION_BETWEEN(CURRENT_DATE, LOCAL_TIME) AS x",
        "20.28 SR 3",
    );
    bad(
        "RETURN DURATION_BETWEEN(LOCAL_TIME, LOCAL_TIME) YEAR TO MONTH AS x",
        "20.28 SR 3",
    );
    bad(
        "RETURN DURATION_BETWEEN(1, CURRENT_DATE) AS x",
        "20.26 GR 1",
    );
    // 20.27 SR 6-10
    ok("RETURN DATE('2020-01-01') AS a, ZONED_TIME() AS b, LOCAL_DATETIME() AS c");
    ok("RETURN DURATION('P1Y') + DURATION 'P1M' AS x");
    bad(
        "RETURN DURATION('P1Y') + DURATION 'PT1M' AS x",
        "20.28 SR 1",
    );
    // 20.26 SR 1: date + duration is a local datetime
    ok("RETURN CURRENT_DATE + DURATION 'P1DT0H' > LOCAL_TIMESTAMP AS x");
    bad(
        "RETURN CURRENT_DATE + DURATION 'P1DT0H' > CURRENT_DATE AS x",
        "22.14 CR 1",
    );
}

#[test]
fn lists_and_paths() {
    // 20.15 SR 1-2
    ok("RETURN [1, 2] || [3] AS x");
    ok("RETURN [1] || [2.5] AS x");
    bad("RETURN [1] || ['a'] AS x", "22.19 SR 4");
    bad("RETURN [1] || 2 AS x", "20.15 SR 1");
    // 20.13, 20.14
    ok("MATCH p = (a)-[e]->(b) RETURN p || p AS q, PATH[a, e, b] AS r");
    bad("MATCH (a)-[e]->(b) RETURN PATH[e] AS r", "20.1 SR 4");
    bad("MATCH (a)-[e]->(b) RETURN PATH[a, b, b] AS r", "20.1 SR 5");
    bad("MATCH p = (a) RETURN p || 'a' AS q", "20.13 SR 2");
    // 20.16
    ok("RETURN TRIM([1, 2], 1) AS x");
    // the refined grammar keeps the count an integer form, so this is a tree of the ISO grammar
    assert!(
        verdicts_in(&ISO, "RETURN TRIM([1, 2], 1.5) AS x", &verifier())
            .iter()
            .all(|v| v.iter().any(|v| v.rule == "20.16 SR 1"))
    );
    bad("RETURN TRIM('ab', 1) AS x", "20.15 SR 1");
    ok("MATCH p = (a)-[e]->(b) RETURN ELEMENTS(p) AS x");
    bad("MATCH (a) RETURN ELEMENTS(a) AS x", "20.13 SR 2");
}

#[test]
fn boolean_expressions() {
    // 20.20 SR 3
    ok("RETURN TRUE AND NOT FALSE OR UNKNOWN XOR TRUE AS x");
    ok("RETURN (1 = 1) IS NOT UNKNOWN AS x");
    ok("RETURN NULL AND TRUE AS x");
    bad("RETURN true OR 1 AS x", "20.20 SR 3");
    bad("RETURN NOT 'a' AS x", "20.20 SR 3");
    bad("RETURN 1 IS TRUE AS x", "20.20 SR 3");
    bad("RETURN 1 AND 2 AS x", "20.20 SR 3");
}

#[test]
fn conditions() {
    // a <search condition> is a <boolean value expression> (19.1, 20.20 SR 3)
    ok("FILTER true FINISH");
    ok("FILTER NULL FINISH");
    ok("MATCH (x) FILTER x.k > 1 RETURN x");
    ok("MATCH (x) WHERE x.k RETURN x");
    bad("FILTER '' FINISH", "20.20 SR 3");
    bad("FILTER WHERE 1 FINISH", "20.20 SR 3");
    bad("MATCH (x WHERE 1) RETURN x", "20.20 SR 3");
    bad("MATCH (x) WHERE x RETURN x", "20.20 SR 3");
    bad("MATCH ((x)-[e]->(y) WHERE 'a') RETURN x", "20.20 SR 3");
    bad("RETURN CASE WHEN 1 THEN 2 END AS x", "20.20 SR 3");
}

#[test]
fn comparisons() {
    // 19.3 SR 2, 22.13-22.14 CR 1 without GA04
    ok("RETURN 1 = 1.5 AS a, 'a' < 'b' AS b, TRUE <> FALSE AS c");
    ok("RETURN [1, 2] = [3] AS a, {k: 1} = {k: 2.5} AS b");
    ok("RETURN CURRENT_DATE >= DATE '2020-01-01' AS x");
    ok("MATCH (a)-[e]->(b) RETURN a = b AS x, e <> e AS y");
    ok("RETURN NULL = 1 AS x");
    bad("RETURN 1 = 'a' AS x", "22.13 CR 1");
    bad("RETURN 1 < 'a' AS x", "22.14 CR 1");
    bad("RETURN CURRENT_DATE = LOCAL_TIME AS x", "22.13 CR 1");
    bad("RETURN [1] = ['a'] AS x", "22.13 CR 1");
    bad("RETURN {k: 1} = {l: 1} AS x", "22.13 CR 1");
    bad("MATCH (a)-[e]->(b) RETURN a = e AS x", "22.13 CR 1");
    bad("RETURN DURATION 'P1Y' > DURATION 'PT1H' AS x", "22.14 CR 1");
}

#[test]
fn predicates() {
    // 19.5-19.13
    ok("MATCH (a) RETURN a IS NULL AS x, a.k IS NOT NULL AS y");
    ok("RETURN 1 IS TYPED INT AS x, 'a' IS NOT TYPED STRING AS y");
    ok("RETURN 'a' IS NORMALIZED AS x, 'a' IS NOT NFKC NORMALIZED AS y");
    bad("RETURN 1 IS NORMALIZED AS x", "20.23 SR 2, 4");
    ok("MATCH (a)-[e]->(b) RETURN e IS DIRECTED AS x");
    bad("MATCH (a)-[e]->(b) RETURN a IS DIRECTED AS x", "19.8 SR 3");
    // `LET a = 1 RETURN a IS DIRECTED`: the scope checker refuses a value variable as an
    // element variable reference first (tests/scope_checker.rs, 16.10 SR 3)
    ok("MATCH (a)-[e]->(b) RETURN a IS LABELED L AS x, e:L AS y");
    // refused by the scope checker first (16.10 SR 3: a value variable is no element
    // variable reference, a stricter reading): LET a = 'a' RETURN a IS LABELED L AS x
    ok("MATCH (a)-[e]->(b) RETURN a IS SOURCE OF e AS x, b IS DESTINATION OF e AS y");
    bad(
        "MATCH (a)-[e]->(b) RETURN e IS SOURCE OF e AS x",
        "19.10 SR 2",
    );
    bad(
        "MATCH (a)-[e]->(b) RETURN a IS SOURCE OF b AS x",
        "19.10 SR 3",
    );
    ok("MATCH (a)-[e]->(b) RETURN ALL_DIFFERENT(a, b) AS x, SAME(e, e) AS y");
    bad("MATCH (a)-[e]->(b) RETURN SAME(a, e) AS x", "22.13 CR 1");
    // refused by the scope checker first (16.10 SR 3: a value variable is no element
    // variable reference, a stricter reading): LET a = 1 RETURN ALL_DIFFERENT(a, a) AS x
    ok("MATCH (a) RETURN PROPERTY_EXISTS(a, k) AS x");
    // refused by the scope checker first (16.10 SR 3: a value variable is no element
    // variable reference, a stricter reading): LET a = 1 RETURN PROPERTY_EXISTS(a, k) AS x
    ok("RETURN EXISTS { MATCH (a) WHERE a.k = 1 } AS x");
    bad("RETURN EXISTS { MATCH (a) WHERE 'a' } AS x", "20.20 SR 3");
}

#[test]
fn numeric_functions() {
    // 20.22
    ok("RETURN ABS(-1) AS a, MOD(5, 2) AS b, SIN(1) AS c, LOG(2, 8) AS d, LOG10(5) AS e");
    ok("RETURN LN(1) AS a, EXP(1) AS b, POWER(2, 3) AS c, SQRT(4) AS d");
    ok("RETURN FLOOR(1.5) AS a, CEIL(1.5) AS b, CEILING(1E1) AS c");
    ok("RETURN CHAR_LENGTH('a') AS a, BYTE_LENGTH(X'0F') AS b, SIZE([1]) AS c");
    ok("MATCH p = (a) RETURN PATH_LENGTH(p) AS a, CARDINALITY(p) AS b");
    ok("RETURN CARDINALITY([1]) AS a, CARDINALITY({k: 1}) AS b");
    bad(
        "RETURN CARDINALITY('a') AS x",
        "20.1 SR 3, 6, 20.13 SR 2, 20.15 SR 1",
    );
    bad("RETURN SIZE('a') AS x", "20.15 SR 1");
    bad("RETURN CHAR_LENGTH(1) AS x", "20.23 SR 2");
    bad("RETURN OCTET_LENGTH('a') AS x", "20.23 SR 4");
    bad("RETURN PATH_LENGTH([1]) AS x", "20.13 SR 2");
    bad("RETURN ABS('a') AS x", "20.21 SR 3");
    bad("RETURN MOD('a', 2) AS x", "20.21 SR 3");
    bad("RETURN SIN(TRUE) AS x", "20.21 SR 3");
    bad("RETURN POWER(2, 'a') AS x", "20.21 SR 3");
    bad("RETURN FLOOR(DURATION 'P1Y') AS x", "20.21 SR 3");
    // the result is numeric; a function is no primary without parentheses
    bad("RETURN (CHAR_LENGTH('a')) || 'b' AS x", "20.23 SR 2");
    ok("RETURN FLOOR(1.5) + SIZE([1]) AS x");
}

#[test]
fn string_functions() {
    // 20.24, 20.25
    ok("RETURN UPPER('a') AS a, LOWER('A') AS b, NORMALIZE('a', NFC) AS c");
    // LEFT and RIGHT derive as a character and as a byte string function; the tree of the
    // operand's own kind is valid (H3: each tree is judged as written).
    for text in ["RETURN LEFT('ab', 1) AS a", "RETURN RIGHT(X'0F0F', 1) AS b"] {
        let trees = verdicts(text, &verifier());
        assert!(trees.iter().any(Vec::is_empty), "{text}: {trees:#?}");
    }
    ok_some_tree("RETURN TRIM('  a ') AS a, TRIM(BOTH 'x' FROM 'xax') AS b, LTRIM('ab', 'a') AS c");
    ok_some_tree("RETURN TRIM(X'00' FROM X'000F') AS x");
    bad_on_a_tree("RETURN UPPER(1) AS x", "20.23 SR 2");
    bad("RETURN LEFT(1, 1) AS x", "20.23 SR 2, 4");
    bad_on_a_tree("RETURN LEFT('a', 'b') AS x", "20.21 SR 3");
    bad_on_a_tree("RETURN BTRIM(X'0F') AS x", "20.23 SR 2");
    bad_on_a_tree("RETURN TRIM(1) AS x", "20.23 SR 2, 4");
    bad_on_a_tree("RETURN TRIM('x' FROM X'0F') AS x", "20.24 SR 3");
    bad_on_a_tree("RETURN (UPPER('a')) + 1 AS x", "20.21 SR 3");
    ok_some_tree("RETURN (LEFT('ab', 1)) || 'c' AS x");
    bad_on_a_tree("RETURN (LEFT(X'0F', 1)) || 'c' AS x", "20.23 SR 4");
}

#[test]
fn case_expressions() {
    // 20.7
    ok("RETURN CASE WHEN true THEN 1 ELSE 2 END AS x");
    ok("RETURN CASE WHEN true THEN 1 END AS x");
    ok("RETURN CASE WHEN true THEN 1 ELSE NULL END AS x");
    ok("RETURN CASE 1 WHEN 1, 2 THEN 'a' WHEN > 5 THEN 'b' ELSE 'c' END AS x");
    ok("RETURN COALESCE(NULL, 1) AS x, NULLIF(1, 2) AS y");
    ok("RETURN COALESCE(1, 2.5, NULL) + 1 AS x");
    ok("RETURN CASE WHEN true THEN 1 END + 1 AS x");
    bad(
        "RETURN CASE WHEN true THEN 1 ELSE 'a' END AS x",
        "22.19 SR 4",
    );
    bad("RETURN COALESCE(1, 'a') AS x", "22.19 SR 4");
    bad("RETURN NULLIF(1, 'a') AS x", "22.13 CR 1");
    // SR 3
    bad("RETURN CASE WHEN true THEN NULL END AS x", "20.7 SR 3");
    bad(
        "RETURN CASE WHEN true THEN NULL ELSE NULL END AS x",
        "20.7 SR 3",
    );
    // Cor 1 SR 2 g: the transformed predicates follow Clause 19
    bad("RETURN CASE 1 WHEN 'a' THEN 1 END AS x", "22.13 CR 1");
    bad("RETURN CASE 1 WHEN < 'a' THEN 1 END AS x", "22.14 CR 1");
    ok("MATCH (a)-[e]->(b) RETURN CASE e WHEN IS DIRECTED THEN 1 ELSE 2 END AS x");
    bad(
        "MATCH (a)-[e]->(b) RETURN CASE a WHEN IS DIRECTED THEN 1 END AS x",
        "19.8 SR 3",
    );
    bad(
        "RETURN CASE 1 WHEN IS DIRECTED THEN 1 END AS x",
        "16.10 SR 3",
    );
    bad(
        "RETURN CASE 1 WHEN IS NORMALIZED THEN 1 END AS x",
        "20.23 SR 2, 4",
    );
    ok("RETURN CASE 'a' WHEN IS NULL THEN 1 WHEN IS TYPED INT THEN 2 END AS x");
    // the result has the combined type
    bad("RETURN CASE WHEN true THEN 'a' END * 2 AS x", "20.21 SR 3");
}

#[test]
fn casts() {
    // 20.8, Table 4
    ok("RETURN CAST('1' AS INT) AS x");
    ok("RETURN CAST(1 AS STRING) AS a, CAST(1.5 AS INT) AS b, CAST('true' AS BOOL) AS c");
    ok(
        "RETURN CAST(CURRENT_DATE AS LOCAL DATETIME) AS a, CAST('P1Y' AS DURATION(YEAR TO MONTH)) AS b",
    );
    ok("RETURN CAST(NULL AS INT) AS x, CAST([1] AS LIST<STRING>) AS y");
    ok("MATCH (a) RETURN CAST(a.k AS INT) AS x, CAST(a AS PATH) AS y");
    ok("RETURN CAST({k: 1, l: 2} AS RECORD {k STRING}) AS x");
    bad("RETURN CAST(1 AS DATE) AS x", "20.8 SR 8");
    bad("RETURN CAST(TRUE AS INT) AS x", "20.8 SR 8");
    bad("RETURN CAST(X'0F' AS STRING) AS x", "20.8 SR 8");
    bad("RETURN CAST(CURRENT_DATE AS LOCAL TIME) AS x", "20.8 SR 8");
    bad("RETURN CAST(LOCAL_TIME AS DATE) AS x", "20.8 SR 8");
    bad("RETURN CAST([1] AS LIST<DATE>) AS x", "20.8 SR 11 d");
    bad("RETURN CAST({k: 1} AS RECORD {l INT}) AS x", "20.8 SR 8");
    bad("MATCH (a) RETURN CAST(a AS EDGE) AS x", "20.8 SR 8");
    // SR 4-5
    bad("RETURN CAST(1 AS NULL) AS x", "20.8 SR 4");
    bad("RETURN CAST(NULL AS INT NOT NULL) AS x", "20.8 SR 5");
    // the result has the target type
    bad("RETURN CAST('1' AS INT) || 'a' AS x", "20.23 SR 2");
    ok("RETURN CAST(1 AS STRING) || 'a' AS x");
}

#[test]
fn aggregates() {
    // 20.9
    ok("MATCH (a) RETURN COUNT(*) AS a, COUNT(a) AS b, SUM(a.k) AS c, AVG(a.k) AS d");
    ok("MATCH (a) RETURN MIN(a.k) AS a, MAX(a) AS b, COLLECT_LIST(a) AS c, STDDEV_POP(a.k) AS d");
    ok("MATCH (a) RETURN PERCENTILE_CONT(a.k, 0.5) AS x");
    ok("FOR x IN [1, 2] RETURN SUM(x) + 1 AS y");
    bad("FOR x IN ['a'] RETURN SUM(x) AS y", "20.9 SR 8");
    bad("FOR x IN ['a'] RETURN AVG(x) AS y", "20.9 SR 8");
    bad("FOR x IN [TRUE] RETURN STDDEV_SAMP(x) AS y", "20.9 SR 8");
    bad(
        "FOR x IN ['a'] RETURN PERCENTILE_DISC(x, 0.5) AS y",
        "20.21 SR 3",
    );
    bad(
        "MATCH (a) RETURN PERCENTILE_DISC(a.k, 'a') AS y",
        "20.21 SR 3",
    );
    bad("FOR x IN [1] RETURN COUNT(x) || 'a' AS y", "20.23 SR 2");
    ok("FOR x IN ['a'] RETURN COLLECT_LIST(x) || ['b'] AS y");
    bad(
        "FOR x IN ['a'] RETURN COLLECT_LIST(x) || [1] AS y",
        "22.19 SR 4",
    );
    // a group variable is one element inside an aggregate function
    ok("MATCH (x) ((a)-[e]->(b)){1,3} (y) WHERE SUM(e.k) > 1 RETURN x, y");
    ok("MATCH ((a)-[e]->(b)){2} RETURN COUNT(e) AS n, COLLECT_LIST(a) AS l");
    // outside one it is a list, as scope also reports
    let unscoped = Verifier::new(Grammar::new(&ISO_BNF));
    let found = verdicts("MATCH ((a)-[e]->(b)){2} RETURN a.k AS k", &unscoped);
    assert!(found.iter().any(|t| t.iter().any(|v| v.rule == "20.1 SR 4-6 primary")), "{found:#?}");
}

#[test]
fn property_references() {
    // 20.11
    ok("MATCH (a)-[e]->(b) RETURN a.k AS x, e.k AS y");
    ok("RETURN {k: 1}.k + 1 AS x");
    ok("LET r = {k: 'a'} RETURN r.k || 'b' AS x");
    bad("RETURN {k: 1}.l AS x", "20.11 SR 2");
    bad("LET r = {k: 'a'} RETURN r.k * 2 AS x", "20.21 SR 3");
    bad_on_a_tree("RETURN (1).k AS x", "20.1 SR 4-6 primary");
    bad_on_a_tree("LET x = 'a' RETURN x.k AS y", "20.1 SR 4-6 primary");
    // an open record has dynamically typed fields
    ok("RETURN CAST({k: 1} AS RECORD).k AS x");
    ok("MATCH (a) RETURN ELEMENT_ID(a) = ELEMENT_ID(a) AS x");
    // `9.M` is a decimal literal or property M of 9 (tests/parse.rs); types pick the literal
    ok("RETURN 9.M AS x, 9.F AS y, 9.E+9F AS z");
    ok("RETURN 9.M + 1 AS x");
    // the literal tree breaks 20.23 SR 2, the property tree 20.1 SR 4-6 (H3)
    bad_on_a_tree("RETURN 9.M || 'a' AS x", "20.23 SR 2");
    bad_on_a_tree("RETURN 9.M || 'a' AS x", "20.1 SR 4-6 primary");
    // the literal tree breaks 10.3 SR 8, the property tree 20.1 SR 4-6 (H3)
    bad_on_a_tree("LET VALUE x TYPED STRING = 9.E-2 RETURN x AS y", "10.3 SR 8");
}

#[test]
fn variables() {
    // pattern variables (16.3), LET (14.7), FOR (14.8), RETURN and NEXT (14.10, 9.2)
    ok("MATCH (a)-[e]->(b) RETURN a, e, b");
    ok("LET x = 1 RETURN x + 1 AS y");
    bad("LET x = 'a' RETURN x * 2 AS y", "20.21 SR 3");
    ok("LET x = 1, y = 'a' RETURN x + 1 AS a, y || 'b' AS b");
    ok("FOR x IN [1, 2] RETURN x * 2 AS y");
    bad("FOR x IN ['a'] RETURN x * 2 AS y", "20.21 SR 3");
    ok("FOR x IN [1] WITH ORDINALITY i RETURN x + i AS y");
    ok("RETURN 'a' AS x NEXT RETURN x || 'b' AS y");
    bad("RETURN 'a' AS x NEXT RETURN x + 1 AS y", "20.21 SR 3");
    ok("RETURN 1 AS x NEXT YIELD x AS z RETURN z + 1 AS y");
    bad(
        "RETURN 'a' AS x NEXT YIELD x AS z RETURN z + 1 AS y",
        "20.21 SR 3",
    );
    ok("MATCH (a) LET k = a.k RETURN k + 1 AS y");
    bad("MATCH (a) LET b = a RETURN b + 1 AS y", "20.21 SR 3");
    bad(
        "MATCH (a)-[e]->(b) FOR x IN [e] RETURN x * 2 AS y",
        "20.21 SR 3",
    );
    // an unbound name is unknown; scope reports it
    let unscoped = Verifier::new(Grammar::new(&ISO_BNF));
    assert!(violations_in("RETURN z + 1 AS y", unscoped).is_empty());
    // LET and VALUE definitions with a declared type (10.3 SR 8)
    ok("LET VALUE x TYPED INT = 1 RETURN x AS y");
    ok("LET VALUE x :: FLOAT = 1 RETURN x AS y");
    ok("LET VALUE x STRING = NULL RETURN x AS y");
    bad("LET VALUE x TYPED INT = 'a' RETURN x AS y", "10.3 SR 8");
    bad(
        "LET VALUE x TYPED INT NOT NULL = NULL RETURN x AS y",
        "10.3 SR 8",
    );
    bad("LET VALUE x LIST<INT> = ['a'] RETURN x AS y", "10.3 SR 8");
    // the declared type wins
    bad(
        "LET VALUE x TYPED STRING = NULL RETURN x + 1 AS y",
        "20.21 SR 3",
    );
    // 20.5
    ok("RETURN LET x = 1 IN x + 1 END AS y");
    bad("RETURN LET x = 'a' IN x + 1 END AS y", "20.21 SR 3");
    // a procedure-local definition (10.3)
    ok("VALUE x = 1 RETURN x + 1 AS y");
    bad("VALUE x = 'a' RETURN x + 1 AS y", "20.21 SR 3");
    bad("VALUE x INT = 'a' RETURN x AS y", "10.3 SR 8");
}

#[test]
fn for_sources() {
    // 14.8 SR 10 a: a list or a binding table
    bad("FOR x IN 1 RETURN x", "20.15 SR 1, 20.1 SR 3");
    bad("FOR x IN 'ab' RETURN x", "20.15 SR 1, 20.1 SR 3");
    ok("FOR x IN $xs RETURN x");
    ok("MATCH ((a)-[e]->(b)){2} FOR x IN e RETURN x");
}

#[test]
fn subqueries() {
    // 20.6
    ok("RETURN VALUE { RETURN 1 AS z LIMIT 1 } + 1 AS x");
    bad(
        "RETURN VALUE { RETURN 'a' AS z LIMIT 1 } + 1 AS x",
        "20.21 SR 3",
    );
    bad(
        "RETURN VALUE { RETURN 1 AS a, 2 AS b LIMIT 1 } AS x",
        "20.6 SR 3",
    );
    // inner queries see the outer variables
    ok("LET x = 1 CALL { RETURN x + 1 AS y } RETURN y * 2 AS z");
    bad(
        "LET x = 'a' CALL { RETURN x + 1 AS y } RETURN y AS z",
        "20.21 SR 3",
    );
    bad("CALL { RETURN 'a' AS y } RETURN y * 2 AS z", "20.21 SR 3");
    ok("OPTIONAL MATCH (a) RETURN a.k AS x");
    bad("OPTIONAL MATCH (a) RETURN a + 1 AS x", "20.21 SR 3");
    ok("RETURN 1 AS x UNION RETURN 2 AS x");
}

#[test]
fn unknown_operands_pass() {
    // 4.14.4: a dynamic or open operand meets every requirement
    ok("MATCH (a) RETURN a.k || 'x' AS a1, a.k + DURATION 'PT1H' AS a2, a.k AND true AS a3");
    ok("MATCH (a) RETURN CASE WHEN a.k THEN 1 ELSE 2 END AS b1, CAST(a.k AS DATE) AS b2");
    ok("MATCH (a) RETURN UPPER(a.k) AS c2, CHAR_LENGTH(a.k) AS c3");
    // but not in a static combination (22.19 SR 2, read without GV65)
    bad(
        "MATCH (a) RETURN CASE WHEN a.k THEN a.k ELSE 1 END AS b1",
        "22.19 SR 2",
    );
    bad("MATCH (a) RETURN [a.k, 1] AS c1", "22.19 SR 2");
    ok("MATCH (a) RETURN a.k = 'a' AS d1, a.k < 1 AS d2, NOT a.k AS d3, -a.k AS d4");
    ok("RETURN $p || 'x' AS e1, $p AND true AS e2, CARDINALITY($p) AS e3, $p.k AS e4");
    ok("MATCH (a) WHERE a.name = 'x' AND a.age > 3 RETURN a.name AS n ORDER BY n");
}

#[test]
fn statements() {
    ok("MATCH (a) RETURN a.k AS k, COUNT(*) AS c GROUP BY k");
    ok("SELECT 1 + 1 AS x");
    bad("SELECT 'a' + 1 AS x", "20.21 SR 3");
    ok("INSERT (a {k: 1}) RETURN a");
    bad("INSERT (a {k: 'a' * 2}) RETURN a", "20.21 SR 3");
    bad(
        "MATCH (a) INSERT (a)-[e {k: a}]->(b {k: 1 + TRUE}) RETURN e",
        "20.21 SR 3",
    );
    ok("MATCH (a) SET a.k = 1 RETURN a");
    bad("MATCH (a) SET a.k = 1 || 2 RETURN a", "20.23 SR 2");
    ok("USE g MATCH (a) RETURN a");
    // `"g"` and `a.b` are catalog references too; on the other tree they are typed as written
    // (H3), so `VALUE v = 1 USE v.w` breaks 20.1 SR 4-6 there (tests/probes_checker.rs)
    ok("USE \"g\" MATCH (a) RETURN a");
    bad_on_a_tree("USE 'g' MATCH (a) RETURN a", "11.1 SR 3");
    // `INT | STRING LIST` reads two ways (a union with a list, a list of a union), and a date
    // goes to neither
    bad(
        "LET VALUE x INT | STRING LIST = CURRENT_DATE RETURN x AS y",
        "10.3 SR 8",
    );
    ok("LET VALUE x ANY<INT | STRING> = 1 RETURN x AS y");
    ok("GRAPH g = CURRENT_GRAPH TABLE t = { RETURN 1 AS x } RETURN 1 AS y");
    bad_on_a_tree("VALUE v = 1 USE v MATCH (a) RETURN a", "11.1 SR 3");
    bad_on_a_tree("VALUE v = 1 USE (v) MATCH (a) RETURN a", "11.1 SR 3");
    ok("OPTIONAL CALL { RETURN 1 AS x } RETURN x + 1 AS y");
    bad(
        "MATCH (a) CALL (a) { RETURN a * 2 AS y } RETURN y",
        "20.21 SR 3",
    );
    ok("MATCH (a) CALL () { RETURN 1 AS y } RETURN y + 1 AS z");
    ok("RETURN 1 AS x NEXT RETURN 2 AS y NEXT RETURN y * 2 AS z");
    bad(
        "RETURN 1 AS x NEXT RETURN 'a' AS y NEXT RETURN y * 2 AS z",
        "20.21 SR 3",
    );
    ok("MATCH (a) RETURN a NEXT MATCH (a)-[e]->(b) RETURN b");
    ok("FILTER EXISTS { RETURN 1 AS x } FINISH");
    ok("FILTER VALUE { RETURN TRUE AS x LIMIT 1 } FINISH");
    bad(
        "FILTER VALUE { RETURN 1 AS x LIMIT 1 } FINISH",
        "20.20 SR 3",
    );
}

#[test]
fn order_and_page() {
    ok("MATCH (a) RETURN a.k AS k ORDER BY k OFFSET 1 LIMIT 2");
    bad("MATCH (a) RETURN a ORDER BY a + 1", "20.21 SR 3");
    ok("MATCH (a) ORDER BY a.k LIMIT 1 RETURN a");
}

/// 20.1 SR 4-6 with 21.2 SR 67: a bare NULL has no node, edge or record type to take from a
/// property source.
#[test]
fn a_property_of_null() {
    bad("RETURN NULL . a AS x", "20.1 SR 4-6");
    ok("MATCH (x) RETURN x . a AS y");
    ok("MATCH (x)-[e]->(y) RETURN e . a AS z");
}

#[test]
fn dynamic_casts() {
    // 20.8 SR 10: a property has the dynamic property value type, whose components H2 takes to
    // include the predefined types and no others
    ok("MATCH (x) RETURN CAST(x.a AS INT) AS y");
    ok("MATCH (x) RETURN CAST(x.a AS STRING) AS y, CAST(x.a AS DURATION(DAY TO SECOND)) AS z");
    bad("MATCH (x) RETURN CAST(x.a AS NODE) AS y", "20.8 SR 10");
    bad("MATCH (x) RETURN CAST(x.a AS PATH) AS y", "20.8 SR 10");
    bad("MATCH (x) RETURN CAST(x.a AS LIST<INT>) AS y", "20.8 SR 10");
    bad(
        "MATCH (x) RETURN COLLECT_LIST(x.a) AS l NEXT RETURN CAST(l AS LIST<EDGE>) AS y",
        "20.8 SR 11 d",
    );
    // a closed union source: some component casts
    // (a closed union target is refused by the 20.8 SR 9 reading, the twelfth review)
    bad("RETURN CAST(CAST(1 AS ANY<INT | STRING>) AS DATE) AS y", "20.8 SR 9");
    bad(
        "RETURN CAST(CAST(1 AS ANY<INT | STRING>) AS BYTES) AS y",
        "20.8 SR 10",
    );
    // 20.8 SR 9: a cast to a dynamic union type from a subtype of it
    ok("RETURN CAST(1 AS ANY) AS y, CAST(1 AS ANY VALUE) AS z");
    ok("MATCH (x) RETURN CAST(x AS ANY) AS y, CAST(x.a AS ANY PROPERTY VALUE) AS z");
    bad("RETURN CAST(1 AS ANY<INT | STRING>) AS y, CAST('a' AS INT | STRING) AS z", "20.8 SR 9");
    bad("RETURN CAST(TRUE AS ANY<INT | STRING>) AS y", "20.8 SR 9");
    bad(
        "MATCH (x) RETURN CAST(x AS ANY PROPERTY VALUE) AS y",
        "20.8 SR 9",
    );
    bad(
        "MATCH (x) RETURN CAST(x.a AS ANY<INT | STRING>) AS y",
        "20.8 SR 9",
    );
    // with nullability: a material union takes only what is known not null
    bad("RETURN CAST(1 AS ANY NOT NULL) AS y", "20.8 SR 9");
    bad("RETURN CAST(NULL AS ANY NOT NULL) AS y", "20.8 SR 5");
    ok("RETURN CAST(NULL AS ANY) AS y");
}

#[test]
fn closed_element_types() {
    // 20.11 SR 3 a: a property of a closed node or edge reference value type names one of its
    // property types, and has its value type
    ok("MATCH (x) RETURN CAST(x AS (:L {a INT})).a + 1 AS y");
    bad(
        "MATCH (x) RETURN CAST(x AS (:L {a INT})).b AS y",
        "20.11 SR 3",
    );
    bad(
        "MATCH (x) RETURN CAST(x AS (:L {a STRING})).a + 1 AS y",
        "20.21 SR 3",
    );
    ok("MATCH (x) LET v = CAST(x AS (:L {a INT})) RETURN v.a AS y");
    bad(
        "MATCH (x) LET v = CAST(x AS (:L {a INT})) RETURN v.b AS y",
        "20.11 SR 3",
    );
    bad(
        "MATCH ()-[e]->() RETURN CAST(e AS (:A)-[:L {a INT}]->(:B {b INT})).b AS y",
        "20.11 SR 3",
    );
    ok("MATCH ()-[e]->() RETURN CAST(e AS (:A)-[:L {a INT}]->(:B {b INT})).a AS y");
    // through a FOR over a list of them
    bad(
        "MATCH (x) FOR v IN [CAST(x AS (:L {a INT}))] RETURN v.b AS y",
        "20.11 SR 3",
    );
    // different closed types combined: not followed (reading)
    bad(
        "MATCH (x) LET v = CASE WHEN TRUE THEN CAST(x AS (:L {a INT})) ELSE CAST(x AS (:M {a INT})) END RETURN v.a AS y",
        "20.11 SR 3",
    );
    // with an open one, the supertype is open
    ok("MATCH (x) LET v = CASE WHEN TRUE THEN CAST(x AS (:L {a INT})) ELSE x END RETURN v.b AS y");
    // 16.8 SR 4 b ii: a labeled predicate names labels of the closed type
    // `LET v = CAST(x AS (:L&M ..)) RETURN v IS LABELED L`: valid by 16.10 SR 3, refused by
    // the scope checker's stricter reading (a value variable is no element variable reference)
    // refused by the scope checker first (16.10 SR 3: a value variable is no element
    // variable reference, a stricter reading): MATCH (x) LET v = CAST(x AS (:L {a INT})) RETURN v IS LABELED N AS y
    bad(
        "MATCH (x) LET v = CAST(x AS (:L {a INT})) RETURN CASE v WHEN IS LABELED N THEN 1 END AS y",
        "16.8 SR 4",
    );
    // an open variable is not known to be of a closed type (10.3 SR 8 b i 1, 4.16.7)
    bad(
        "MATCH (x) LET VALUE v :: (:L) = x RETURN v AS y",
        "10.3 SR 8",
    );
    // a property type has a supported property value type (18.6 SR 4, 18.7 SR 4)
    bad(
        "MATCH (x) RETURN CAST(x AS (:L {a NOTHING})) AS y",
        "18.7 SR 4",
    );
    bad(
        "MATCH (x) RETURN CAST(x AS (:L {a NULL NOT NULL})) AS y",
        "18.6 SR 4",
    );
    bad(
        "MATCH (x) RETURN CAST(x AS (:L {a NULL})) AS y",
        "18.7 SR 4",
    );
    bad(
        "MATCH (x) RETURN CAST(x AS (:L {a NODE})) AS y",
        "18.7 SR 4",
    );
}

#[test]
fn value_types() {
    // 18.9 SR 68: a group list of nodes or edges
    bad("SESSION SET VALUE $b GROUP LIST<PATH> = NULL", "18.9 SR 68");
    bad(
        "SESSION SET VALUE $b GROUP LIST<NODE | EDGE> = NULL",
        "18.9 SR 68",
    );
    ok("SESSION SET VALUE $b GROUP LIST<NODE> = NULL");
    ok("SESSION SET VALUE $b LIST<PATH> = NULL");
    bad(
        "VALUE v :: INT GROUP LIST = NULL RETURN 1 AS y",
        "18.9 SR 68",
    );
    // 18.9 SR 88: all components possibly nullable or all known not nullable
    bad(
        "SESSION SET VALUE $b ANY<INT NOT NULL | STRING> = 1",
        "18.9 SR 88",
    );
    bad(
        "SESSION SET VALUE $b INT | STRING NOT NULL = 1",
        "18.9 SR 88",
    );
    // (a type test: no value goes to the type, which assignment and cast would ask of a
    // known not nullable one)
    ok("FILTER 1 IS TYPED ANY<INT NOT NULL | STRING NOT NULL> FINISH");
    ok("SESSION SET VALUE $b ANY<INT | STRING> = 1");
    // a nested union is known not nullable when its components are (SR 85, 86)
    ok("FILTER 1 IS TYPED ANY<INT NOT NULL | ANY<STRING NOT NULL | BOOL NOT NULL>> FINISH");
    bad(
        "SESSION SET VALUE $b ANY<INT NOT NULL | ANY<STRING | BOOL>> = 1",
        "18.9 SR 88",
    );
}

#[test]
fn set_values() {
    // 13.3 SR 3 a iv, b iii 2: a supported property value type (reading: the predefined types)
    ok("MATCH (a) SET a.k = 1, a.l = a.m RETURN a");
    ok("MATCH (a) SET a = {k: 'x', l: DATE '2020-01-01'} RETURN a");
    bad("MATCH (a) SET a.k = NULL RETURN a", "13.3 SR 3");
    bad("MATCH (a) SET a = {k: NULL} RETURN a", "13.3 SR 3");
    bad("MATCH (a) SET a.k = [1] RETURN a", "13.3 SR 3");
    bad("MATCH (a), (b) SET a.k = b RETURN a", "13.3 SR 3");
}

#[test]
fn composite_queries() {
    // 14.2 SR 10 a v: column-combinable
    ok("RETURN 1 AS x UNION ALL RETURN 1.5 AS x");
    ok("RETURN 1 AS x OTHERWISE RETURN 2 AS x");
    bad("RETURN 1 AS x UNION ALL RETURN 'a' AS x", "14.2 SR 10");
    bad(
        "RETURN [1] AS x UNION ALL RETURN DATE '2020-01-01' AS x",
        "14.2 SR 10",
    );
    // three operands: the left one is the combination of the first two
    bad(
        "RETURN 1 AS x UNION ALL RETURN 2 AS x UNION ALL RETURN 'a' AS x",
        "14.2 SR 10",
    );
    // 14.2 SR 10 a vii 1: under UNION DISTINCT (implicit), EXCEPT, INTERSECT, no column of a
    // dynamic union type with non-comparable components
    bad(
        "MATCH (a) RETURN a.k AS x UNION RETURN 1 AS x",
        "14.2 SR 10",
    );
    bad(
        "MATCH (a) RETURN a.k AS x EXCEPT ALL RETURN 1 AS x",
        "14.2 SR 10",
    );
    bad(
        "MATCH (a) RETURN a.k AS x INTERSECT DISTINCT MATCH (b) RETURN b.k AS x",
        "14.2 SR 10",
    );
    // 22.19 SR 2 (reading): a dynamic column in the static combination
    bad(
        "MATCH (a) RETURN a.k AS x UNION ALL RETURN 1 AS x",
        "22.19 SR 2",
    );
    ok("RETURN 1 AS x UNION RETURN 2 AS x");
}

#[test]
fn grouping_and_aggregating() {
    // 14.11 SR 10 a ii as Cor 1 has it
    ok("MATCH (a) RETURN a.k AS k, COUNT(*) AS c GROUP BY k");
    bad(
        "MATCH (a) RETURN a AS a, COUNT(*) AS c GROUP BY a, c",
        "14.11 SR 10",
    );
}

#[test]
fn typed_graphs_and_tables() {
    // 10.1 SR 8 b i 1: a closed graph type's initializer is not followed (reading)
    ok("GRAPH g :: ANY GRAPH = CURRENT_GRAPH RETURN 1 AS y");
    bad(
        "GRAPH g :: GRAPH { (:L) } = CURRENT_GRAPH RETURN 1 AS y",
        "10.1 SR 8",
    );
    // 10.2 SR 8 b i 1: a nested query's columns are followed
    ok("TABLE t :: TABLE { x INT } = { RETURN 1 AS x } RETURN 1 AS y");
    bad(
        "TABLE t :: TABLE { x INT } = { RETURN 'a' AS x } RETURN 1 AS y",
        "10.2 SR 8",
    );
    bad(
        "TABLE t :: TABLE { y INT } = { RETURN 1 AS x } RETURN 1 AS y",
        "10.2 SR 8",
    );
    // a table variable's columns are followed too (the unknowns audit)
    ok("TABLE s = { RETURN 1 AS x } TABLE t :: TABLE { x INT } = s RETURN 1 AS y");
    bad(
        "TABLE s = { RETURN 'a' AS x } TABLE t :: TABLE { x INT } = s RETURN 1 AS y",
        "10.2 SR 8",
    );
    // a catalog table's are the environment's, not followed (reading)
    bad(
        "TABLE t :: TABLE { x INT } = / s RETURN 1 AS y",
        "10.2 SR 8",
    );
    // 7.1 SR 6 c i, ii
    ok("SESSION SET GRAPH $g :: ANY GRAPH = CURRENT_GRAPH");
    bad(
        "SESSION SET GRAPH $g :: GRAPH { (:L) } = CURRENT_GRAPH",
        "7.1 SR 6",
    );
    ok("SESSION SET TABLE $t :: TABLE { x INT } = { RETURN 1 AS x }");
    bad(
        "SESSION SET TABLE $t :: TABLE { x INT } = { RETURN 'a' AS x }",
        "7.1 SR 6",
    );
}

#[test]
fn null_cases() {
    // 20.7 SR 3 through 20.7 SR 1 b-d
    ok("RETURN NULLIF(1, 1) AS y, NULLIF(1, NULL) AS z");
    bad("RETURN NULLIF(NULL, 1) AS y", "20.7 SR 3");
    ok("RETURN COALESCE(NULL, NULL, 1) AS y, COALESCE(1, NULL) AS z");
    bad("RETURN COALESCE(NULL, NULL) AS y", "20.7 SR 3");
    bad("RETURN COALESCE(1, NULL, NULL) AS y", "20.7 SR 3");
}

#[test]
fn select_bodies_and_session_values() {
    // a SELECT with a body: its expressions are typed, its variables followed
    bad(
        "SELECT 1 + 'a' AS x FROM CURRENT_GRAPH MATCH (a)",
        "20.21 SR 3",
    );
    ok("SELECT a.k AS x FROM CURRENT_GRAPH MATCH (a)");
    bad(
        "SELECT a + 1 AS x FROM CURRENT_GRAPH MATCH (a)",
        "20.21 SR 3",
    );
    bad("SELECT x || 'a' AS y FROM { RETURN 1 AS x }", "20.23 SR 2");
    bad(
        "SELECT v.b AS y FROM { MATCH (x) RETURN CAST(x AS (:L {a INT})) AS v }",
        "20.11 SR 3",
    );
    // 7.1 SR 6 c iii 3 A I
    ok("SESSION SET VALUE $b INT = 1");
    bad("SESSION SET VALUE $b INT = 'a'", "7.1 SR 6");
    bad("SESSION SET VALUE $b BOOL NOT NULL = NULL", "7.1 SR 6");
    bad("SESSION SET VALUE $b = 1 + TRUE", "20.21 SR 3");
}

#[test]
fn reference_value_expressions() {
    // 20.1 SR 2, 3 on the derivation a tree takes: a primary read as a <graph reference value
    // expression> has a graph type, as a <binding table reference value expression> a table type
    bad_on_a_tree("RETURN 1 AS x", "20.1 SR 2");
    bad_on_a_tree("RETURN 'a' AS x", "20.1 SR 3");
    bad_on_a_tree("GRAPH g = CURRENT_GRAPH RETURN g AS x", "20.1 SR 3");
    bad_on_a_tree("FOR x IN [1, 2] RETURN x AS y", "20.1 SR 3");
    // a graph, an unknown or a dynamic value is no violation of SR 2 on any tree
    never_on_a_tree("GRAPH g = CURRENT_GRAPH RETURN g AS x", "20.1 SR 2");
    never_on_a_tree("RETURN $p AS x", "20.1 SR 2");
    never_on_a_tree("RETURN $p AS x", "20.1 SR 3");
    never_on_a_tree("MATCH (a) RETURN CAST(a.k AS ANY) AS x", "20.1 SR 2");
    never_on_a_tree("TABLE t = { RETURN $p AS a } RETURN t AS x", "20.1 SR 3");
}

/// No tree of `text` reports `rule`.
#[track_caller]
fn never_on_a_tree(text: &str, rule: &str) {
    let all = verdicts(text, &Verifier::new(Grammar::new(&ISO_BNF)).with_scope());
    assert!(
        all.iter().all(|v| v.iter().all(|v| v.rule != rule)),
        "{text:?}: {all:#?}"
    );
}

#[test]
fn session_parameters_set_twice() {
    // 7.1 SR 6 d ii 1 B: a later SESSION SET of a parameter takes a type assignable to the
    // declared type the first gave it
    ok("SESSION SET VALUE $b INT = 1 SESSION SET VALUE $b = 2");
    ok("SESSION SET VALUE $b INT = 1 SESSION SET VALUE $b INT = 2");
    ok("SESSION SET VALUE $b ANY = 1 SESSION SET VALUE $b = 'a'");
    ok("SESSION SET VALUE $c = 1 SESSION SET VALUE $b STRING = 'a'");
    bad(
        "SESSION SET VALUE $b INT = 1 SESSION SET VALUE $b = 'a'",
        "7.1 SR 6",
    );
    bad(
        "SESSION SET VALUE $b INT = 1 SESSION SET VALUE $b STRING = 'a'",
        "7.1 SR 6",
    );
    // the first command's type, whatever came between (SR 6 d ii 1 C)
    bad(
        "SESSION SET VALUE $b INT = 1 SESSION SET VALUE $b = 2 SESSION SET VALUE $b = TRUE",
        "7.1 SR 6",
    );
    // nullability is not inferred: an undeclared type is nullable
    bad(
        "SESSION SET VALUE $b INT NOT NULL = 1 SESSION SET VALUE $b = 2",
        "7.1 SR 6",
    );
    // across kinds
    bad(
        "SESSION SET GRAPH $b = CURRENT_GRAPH SESSION SET VALUE $b = 1",
        "7.1 SR 6",
    );
    ok("SESSION SET GRAPH $b ANY GRAPH = CURRENT_GRAPH SESSION SET GRAPH $b = CURRENT_GRAPH");
    bad(
        "SESSION SET TABLE $b TABLE { x INT } = { RETURN 1 AS x } SESSION SET TABLE $b TABLE { y INT } = { RETURN 1 AS y }",
        "7.1 SR 6",
    );
}

#[test]
fn untyped_session_tables_are_typed() {
    // The fifth review: an untyped SESSION SET TABLE body was not typed.
    bad("SESSION SET TABLE $b = { RETURN 1 + TRUE AS x }", "20.21 SR 3");
    ok("SESSION SET TABLE $b = { RETURN 1 + 1 AS x }");
}

#[test]
fn immaterial_types_nested_in_a_cast_target() {
    // 20.8 SR 4 read strictly (the fifth review): no immaterial type anywhere in TD.
    bad("RETURN CAST ( NULL AS NOTHING LIST ) AS x", "20.8 SR 4");
    bad("RETURN CAST ( NULL AS NULL | PATH ) AS x", "20.8 SR 4");
    bad("RETURN CAST ( NULL AS INT NOT NULL | NOTHING LIST ) AS x", "20.8 SR 4");
    ok("RETURN CAST ( NULL AS INT LIST ) AS x");
}

#[test]
fn grouping_aliases_reach_aggregates() {
    // 14.11 SR 10 a ix (the eighth review): SUM of a node through a grouping alias.
    bad("MATCH ( x ) RETURN x AS y , SUM ( y ) AS z GROUP BY y", "20.9 SR 8");
}
