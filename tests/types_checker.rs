use gql_proof::ISO_BNF_XML;
use gql_proof::bnf;
use gql_proof::cfg::Cfg;
use gql_proof::parse::Parser;
use gql_proof::tokens::Grammar;
use gql_proof::verify::{Verifier, Violation, types};
use std::cell::RefCell;
use std::sync::LazyLock;

static ISO_BNF: LazyLock<bnf::Bnf> = LazyLock::new(|| bnf::parse(ISO_BNF_XML).unwrap());
static ISO: LazyLock<Cfg> = LazyLock::new(|| Cfg::from_bnf(&ISO_BNF));

/// The typing violations of `text`, the same for every tree of it the verifier accepts. Types
/// are only read on trees whose names are in scope: `TABLE / a` also derives as a division of
/// two unbound variables.
fn violations(text: &str) -> Vec<Violation> {
    violations_in(text, Verifier::new(Grammar::new(&ISO_BNF)).with_scope())
}

fn violations_in(text: &str, verifier: Verifier) -> Vec<Violation> {
    let tokens = Grammar::new(&ISO_BNF);
    let parser = Parser::new(&ISO, &tokens, "GQL-program").unwrap();
    let verdicts = RefCell::new(Vec::new());
    // Accept no tree, so the parser offers every one up to its limit.
    let parsed = parser
        .parse(text, |n| {
            let plain = n.export(&ISO);
            if verifier.verify(&plain, &n.render(&ISO)).is_empty() {
                let mut rules: Vec<_> = types::check(&plain).iter().map(|v| v.rule).collect();
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
    types::check(&verdicts[0].1)
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
    ok("RETURN CURRENT_DATE + DURATION 'P1DT0H' AS x");
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
    bad("RETURN TRIM([1, 2], 1.5) AS x", "20.16 SR 1");
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
    bad("LET a = 1 RETURN a IS DIRECTED AS x", "16.10 SR 3");
    ok("MATCH (a)-[e]->(b) RETURN a IS LABELED L AS x, e:L AS y");
    bad("LET a = 'a' RETURN a IS LABELED L AS x", "16.10 SR 3");
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
    bad("LET a = 1 RETURN ALL_DIFFERENT(a, a) AS x", "16.10 SR 3");
    ok("MATCH (a) RETURN PROPERTY_EXISTS(a, k) AS x");
    bad("LET a = 1 RETURN PROPERTY_EXISTS(a, k) AS x", "16.10 SR 3");
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
    ok("RETURN LEFT('ab', 1) AS a, RIGHT(X'0F0F', 1) AS b");
    ok("RETURN TRIM('  a ') AS a, TRIM(BOTH 'x' FROM 'xax') AS b, LTRIM('ab', 'a') AS c");
    ok("RETURN TRIM(X'00' FROM X'000F') AS x");
    bad("RETURN UPPER(1) AS x", "20.23 SR 2");
    bad("RETURN LEFT(1, 1) AS x", "20.23 SR 2, 4");
    bad("RETURN LEFT('a', 'b') AS x", "20.21 SR 3");
    bad("RETURN BTRIM(X'0F') AS x", "20.23 SR 2");
    bad("RETURN TRIM(1) AS x", "20.23 SR 2, 4");
    bad("RETURN TRIM('x' FROM X'0F') AS x", "20.24 SR 3");
    bad("RETURN (UPPER('a')) + 1 AS x", "20.21 SR 3");
    ok("RETURN (LEFT('ab', 1)) || 'c' AS x");
    bad("RETURN (LEFT(X'0F', 1)) || 'c' AS x", "20.23 SR 4");
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
    bad("RETURN CAST([1] AS LIST<DATE>) AS x", "20.8 SR 8");
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
    let found = violations_in("MATCH ((a)-[e]->(b)){2} RETURN a.k AS k", unscoped);
    assert!(found.iter().any(|v| v.rule == "20.1 SR 4-6"), "{found:#?}");
}

#[test]
fn property_references() {
    // 20.11
    ok("MATCH (a)-[e]->(b) RETURN a.k AS x, e.k AS y");
    ok("RETURN {k: 1}.k + 1 AS x");
    ok("LET r = {k: 'a'} RETURN r.k || 'b' AS x");
    bad("RETURN {k: 1}.l AS x", "20.11 SR 2");
    bad("LET r = {k: 'a'} RETURN r.k * 2 AS x", "20.21 SR 3");
    bad("RETURN (1).k AS x", "20.1 SR 4-6");
    bad("LET x = 'a' RETURN x.k AS y", "20.1 SR 4-6");
    bad("MATCH p = (a) RETURN p.k AS x", "20.1 SR 4-6");
    // an open record has dynamically typed fields
    ok("RETURN CAST({k: 1} AS RECORD).k AS x");
    ok("MATCH (a) RETURN ELEMENT_ID(a) = ELEMENT_ID(a) AS x");
    // `9.M` is a decimal literal or property M of 9 (tests/parse.rs); types pick the literal
    ok("RETURN 9.M AS x, 9.F AS y, 9.E+9F AS z");
    ok("RETURN 9.M + 1 AS x");
    bad("RETURN 9.M || 'a' AS x", "20.23 SR 2");
    bad(
        "LET VALUE x TYPED STRING = 9.E-2 RETURN x AS y",
        "10.3 SR 8",
    );
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
    ok("RETURN VALUE { RETURN 1 AS z } + 1 AS x");
    bad("RETURN VALUE { RETURN 'a' AS z } + 1 AS x", "20.21 SR 3");
    bad("RETURN VALUE { RETURN 1 AS a, 2 AS b } AS x", "20.6 SR 3");
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
    ok("MATCH (a) RETURN CASE WHEN a.k THEN a.k ELSE 1 END AS b1, CAST(a.k AS DATE) AS b2");
    ok("MATCH (a) RETURN [a.k, 1] AS c1, UPPER(a.k) AS c2, CHAR_LENGTH(a.k) AS c3");
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
    // `"g"` and `a.b` are catalog references too
    ok("USE \"g\" MATCH (a) RETURN a");
    ok("VALUE v = 1 USE v.w MATCH (a) RETURN a");
    bad("USE 'g' MATCH (a) RETURN a", "11.1 SR 3");
    // the value types of a union are unmodelled: `ANY | STRING LIST` reads two ways
    ok("LET VALUE x INT | STRING LIST = CURRENT_DATE RETURN x AS y");
    ok("GRAPH g = CURRENT_GRAPH TABLE t = { RETURN 1 AS x } RETURN 1 AS y");
    bad("VALUE v = 1 USE v MATCH (a) RETURN a", "11.1 SR 3");
    bad("VALUE v = 1 USE (v) MATCH (a) RETURN a", "11.1 SR 3");
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
    ok("FILTER VALUE { RETURN TRUE AS x } FINISH");
    bad("FILTER VALUE { RETURN 1 AS x } FINISH", "20.20 SR 3");
}

#[test]
fn order_and_page() {
    ok("MATCH (a) RETURN a.k AS k ORDER BY k OFFSET 1 LIMIT 2");
    bad("MATCH (a) RETURN a ORDER BY a + 1", "20.21 SR 3");
    ok("MATCH (a) ORDER BY a.k LIMIT 1 RETURN a");
}
