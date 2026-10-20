//! The syntax rules compiled into the grammar (`refine`) against their direct reading
//! (`verify`). Probes are skeleton trees holding only the nodes the rules look at, run through
//! both; the differential test runs both over generated trees.

use gql_proof::cfg::Cfg;
use gql_proof::leaf::StubProvider;
use gql_proof::purdom::{Analysis, Config, Generator, Length};
use gql_proof::refine::{accepts, all_rules, refine};
use gql_proof::tokens::Grammar;
use gql_proof::verify::{Plain, Verifier};
use gql_proof::{ISO_BNF_XML, MatchModeDefault, bnf};
use proptest::prelude::*;
use std::sync::LazyLock;

static ISO: LazyLock<bnf::Bnf> = LazyLock::new(|| bnf::parse(ISO_BNF_XML).unwrap());
static BASE: LazyLock<Cfg> = LazyLock::new(|| Cfg::from_bnf(&ISO));

const RULES: [&str; 3] = ["16.4 SR 14", "16.4 SR 6", "13.1 SR 5"];

fn d(name: &str, children: Vec<Plain>) -> Plain {
    Plain::Def {
        name: name.into(),
        synthetic: false,
        children,
    }
}

fn kw(text: &str) -> Plain {
    Plain::Kw(text.into())
}

/// The verdicts of both implementations: the automaton's, and the syntax rules the verifier
/// reports.
fn verdicts(tree: &Plain, id086: MatchModeDefault) -> (bool, Vec<&'static str>) {
    let automaton = accepts(&all_rules(id086), tree).is_ok();
    let verifier = Verifier::new(Grammar::new(&ISO)).with_syntax_rules(id086);
    let rendered = verifier.render(tree);
    let mut broken: Vec<&'static str> = verifier
        .verify(tree, &rendered)
        .into_iter()
        .map(|v| v.rule)
        .filter(|r| RULES.contains(r))
        .collect();
    broken.dedup();
    (automaton, broken)
}

/// Both implementations accept, or both reject with `rule`.
fn expect(tree: &Plain, id086: MatchModeDefault, rule: Option<&str>) {
    let (automaton, broken) = verdicts(tree, id086);
    match rule {
        None => {
            assert!(automaton, "automaton rejects");
            assert!(broken.is_empty(), "verifier reports {broken:?}");
        }
        Some(rule) => {
            assert!(!automaton, "automaton accepts");
            assert_eq!(broken, [rule]);
        }
    }
}

// --- skeleton pieces ---------------------------------------------------------------------

/// `-[:R]->` followed by a quantifier.
fn quantified(quantifier: Plain) -> Plain {
    d(
        "quantified path primary",
        vec![
            d("path primary", vec![]),
            d("graph pattern quantifier", vec![quantifier]),
        ],
    )
}

fn plus() -> Plain {
    d("plus sign", vec![Plain::Term("+".into())])
}

fn star() -> Plain {
    d("asterisk", vec![Plain::Term("*".into())])
}

/// `{m,}` or `{m,n}`.
fn braces(upper: bool) -> Plain {
    let mut parts = vec![d("lower bound", vec![]), Plain::Term(",".into())];
    if upper {
        parts.push(d("upper bound", vec![]));
    }
    d("general quantifier", parts)
}

fn mode(m: &str) -> Plain {
    d("path mode", vec![kw(m)])
}

fn mode_prefix(m: &str) -> Plain {
    d(
        "path pattern prefix",
        vec![d("path mode prefix", vec![mode(m)])],
    )
}

fn search_prefix(kind: &str) -> Plain {
    d(
        "path pattern prefix",
        vec![d("path search prefix", vec![d(kind, vec![])])],
    )
}

fn path_pattern(prefix: Option<Plain>, body: Plain) -> Plain {
    let mut children: Vec<Plain> = prefix.into_iter().collect();
    children.push(d("path pattern expression", vec![body]));
    d("path pattern", children)
}

/// `( [mode] body )`.
fn parens(mode_name: Option<&str>, body: Plain) -> Plain {
    let mut children = vec![Plain::Term("(".into())];
    if let Some(m) = mode_name {
        children.push(d("path mode prefix", vec![mode(m)]));
    }
    children.push(d("path pattern expression", vec![body]));
    children.push(Plain::Term(")".into()));
    d("parenthesized path pattern expression", children)
}

fn graph_pattern(match_mode: Option<&str>, patterns: Vec<Plain>, keep: Option<Plain>) -> Plain {
    let mut children = Vec::new();
    match match_mode {
        Some("DIFFERENT") => children.push(d(
            "match mode",
            vec![d("different edges match mode", vec![kw("DIFFERENT")])],
        )),
        Some(_) => children.push(d(
            "match mode",
            vec![d("repeatable elements match mode", vec![kw("REPEATABLE")])],
        )),
        None => {}
    }
    children.push(d("path pattern list", patterns));
    if let Some(prefix) = keep {
        children.push(d("keep clause", vec![kw("KEEP"), prefix]));
    }
    d("graph pattern", children)
}

const PORTABLE: MatchModeDefault = MatchModeDefault::Portable;
const DIFFERENT: MatchModeDefault = MatchModeDefault::DifferentEdges;

// --- probes from gql-review/totality/match-mode-probes.md --------------------------------

#[test]
fn probe_1_and_16_no_match_mode_depends_on_id086() {
    let gp = graph_pattern(
        None,
        vec![path_pattern(None, quantified(braces(false)))],
        None,
    );
    expect(&gp, PORTABLE, Some("16.4 SR 14"));
    expect(
        &gp,
        MatchModeDefault::RepeatableElements,
        Some("16.4 SR 14"),
    );
    expect(&gp, DIFFERENT, None);
}

#[test]
fn probes_2_and_3_repeatable_elements_unbounded() {
    for q in [braces(false), plus(), star()] {
        let gp = graph_pattern(
            Some("REPEATABLE"),
            vec![path_pattern(None, quantified(q))],
            None,
        );
        expect(&gp, PORTABLE, Some("16.4 SR 14"));
        expect(&gp, DIFFERENT, Some("16.4 SR 14"));
    }
}

#[test]
fn probe_4_bounded() {
    let gp = graph_pattern(
        Some("REPEATABLE"),
        vec![path_pattern(None, quantified(braces(true)))],
        None,
    );
    expect(&gp, PORTABLE, None);
}

#[test]
fn probe_5_restrictive_prefix_guards() {
    let pp = path_pattern(Some(mode_prefix("TRAIL")), quantified(braces(false)));
    expect(
        &graph_pattern(Some("REPEATABLE"), vec![pp], None),
        PORTABLE,
        None,
    );
}

#[test]
fn walk_prefix_does_not_guard() {
    let pp = path_pattern(Some(mode_prefix("WALK")), quantified(plus()));
    expect(
        &graph_pattern(Some("REPEATABLE"), vec![pp], None),
        PORTABLE,
        Some("16.4 SR 14"),
    );
}

#[test]
fn probe_6_plain_parens_do_not_guard() {
    let inner = quantified(braces(false));
    let gp = graph_pattern(
        Some("REPEATABLE"),
        vec![path_pattern(None, parens(None, inner))],
        None,
    );
    expect(&gp, PORTABLE, Some("16.4 SR 14"));
}

#[test]
fn restrictive_parens_guard_what_is_inside() {
    let inner = quantified(plus());
    let gp = graph_pattern(
        Some("REPEATABLE"),
        vec![path_pattern(None, parens(Some("TRAIL"), inner))],
        None,
    );
    expect(&gp, PORTABLE, None);
}

#[test]
fn probe_7_restrictive_parens_inside_the_quantifier_do_not_guard() {
    // (TRAIL (a)-[:R]->(b)){1,}: each iteration is a trail, the iteration count is unbounded.
    let qpp = d(
        "quantified path primary",
        vec![
            d(
                "path primary",
                vec![parens(Some("TRAIL"), d("path term", vec![]))],
            ),
            d("graph pattern quantifier", vec![braces(false)]),
        ],
    );
    let gp = graph_pattern(Some("REPEATABLE"), vec![path_pattern(None, qpp)], None);
    expect(&gp, PORTABLE, Some("16.4 SR 14"));
}

#[test]
fn probe_8_selective_search_guards() {
    let pp = path_pattern(
        Some(search_prefix("any path search")),
        quantified(braces(false)),
    );
    expect(
        &graph_pattern(Some("REPEATABLE"), vec![pp], None),
        PORTABLE,
        None,
    );
}

#[test]
fn all_path_search_is_not_selective() {
    let pp = path_pattern(Some(search_prefix("all path search")), quantified(plus()));
    expect(
        &graph_pattern(Some("REPEATABLE"), vec![pp], None),
        PORTABLE,
        Some("16.4 SR 14"),
    );
}

#[test]
fn probe_9_and_15_different_edges_guards() {
    let gp = graph_pattern(
        Some("DIFFERENT"),
        vec![path_pattern(None, quantified(braces(false)))],
        None,
    );
    expect(&gp, PORTABLE, None);
    let simplified = d(
        "simplified quantified",
        vec![
            d("simplified tertiary", vec![]),
            d("graph pattern quantifier", vec![braces(false)]),
        ],
    );
    let gp = graph_pattern(
        Some("DIFFERENT"),
        vec![path_pattern(None, simplified)],
        None,
    );
    expect(&gp, PORTABLE, None);
}

#[test]
fn keep_with_a_guarding_prefix_guards() {
    let gp = graph_pattern(
        Some("REPEATABLE"),
        vec![path_pattern(None, quantified(plus()))],
        Some(search_prefix("any path search")),
    );
    expect(&gp, PORTABLE, None);
}

#[test]
fn probe_11_search_prefix_under_keep() {
    let gp = graph_pattern(
        None,
        vec![path_pattern(
            Some(search_prefix("any path search")),
            d("path term", vec![]),
        )],
        Some(search_prefix("all path search")),
    );
    expect(&gp, PORTABLE, Some("16.4 SR 6"));
}

#[test]
fn probe_12_mode_prefix_under_keep() {
    let gp = graph_pattern(
        None,
        vec![path_pattern(
            Some(mode_prefix("TRAIL")),
            d("path term", vec![]),
        )],
        Some(search_prefix("any path search")),
    );
    expect(&gp, PORTABLE, None);
}

#[test]
fn nested_graph_pattern_is_checked_on_its_own() {
    // An unguarded quantifier inside a subquery of a DIFFERENT EDGES match: the inner graph
    // pattern has its own depth, so the outer match mode does not guard it.
    let inner = graph_pattern(
        Some("REPEATABLE"),
        vec![path_pattern(None, quantified(plus()))],
        None,
    );
    let element = d("element pattern where clause", vec![inner]);
    let outer = graph_pattern(Some("DIFFERENT"), vec![path_pattern(None, element)], None);
    expect(&outer, PORTABLE, Some("16.4 SR 14"));
}

fn statement(elements: Vec<Plain>) -> Plain {
    d(
        "linear data-modifying statement",
        vec![d(
            "ambient linear data-modifying statement",
            vec![d(
                "ambient linear data-modifying statement body",
                vec![d("simple linear data-accessing statement", elements)],
            )],
        )],
    )
}

fn query_element() -> Plain {
    d(
        "simple data-accessing statement",
        vec![d("simple query statement", vec![])],
    )
}

fn insert_element() -> Plain {
    d(
        "simple data-accessing statement",
        vec![d(
            "simple data-modifying statement",
            vec![d("primitive data-modifying statement", vec![])],
        )],
    )
}

#[test]
fn probe_13_match_alone_is_not_data_modifying() {
    expect(
        &statement(vec![query_element()]),
        PORTABLE,
        Some("13.1 SR 5"),
    );
}

#[test]
fn match_then_insert_modifies() {
    expect(
        &statement(vec![query_element(), insert_element()]),
        PORTABLE,
        None,
    );
}

#[test]
fn nested_data_modifying_procedure_counts() {
    // { INSERT ... } as the whole statement: its own statement modifies.
    let inner = statement(vec![insert_element()]);
    let nested = d(
        "linear data-modifying statement",
        vec![d(
            "ambient linear data-modifying statement",
            vec![d(
                "nested data-modifying procedure specification",
                vec![d(
                    "data-modifying procedure specification",
                    vec![d(
                        "procedure body",
                        vec![d("statement block", vec![d("statement", vec![inner])])],
                    )],
                )],
            )],
        )],
    );
    expect(&nested, PORTABLE, None);
}

#[test]
fn modification_in_a_subquery_does_not_count() {
    // MATCH ... WHERE EXISTS { ... INSERT ... }: the insert is not an element of the outer
    // statement's sequence.
    let buried = d(
        "simple data-accessing statement",
        vec![d(
            "simple query statement",
            vec![d(
                "exists predicate",
                vec![statement(vec![insert_element()])],
            )],
        )],
    );
    expect(&statement(vec![buried]), PORTABLE, Some("13.1 SR 5"));
}

// --- the refined grammar --------------------------------------------------------------

fn generate(cfg: &Cfg, start: u32, seed: u64, max_depth: u32) -> Vec<Plain> {
    let analysis = Analysis::new(cfg, &StubProvider);
    let config = Config {
        seed,
        max_depth,
        length: Length::Reference,
    };
    let outcome = Generator::new(&analysis, config, StubProvider)
        .run(start)
        .unwrap();
    outcome.trees.iter().map(|t| t.root.export(cfg)).collect()
}

#[test]
fn refinement_loses_no_iso_production() {
    let start = BASE.require("GQL-program").unwrap();
    for id086 in [PORTABLE, DIFFERENT] {
        let refined = refine(&BASE, &all_rules(id086), start).unwrap();
        let mut copies = vec![false; BASE.prods.len()];
        for prod in &refined.cfg.prods {
            copies[prod.unrefined as usize] = true;
        }
        let missing: Vec<usize> = (0..copies.len()).filter(|&p| !copies[p]).collect();
        assert!(missing.is_empty(), "{missing:?}");
    }
}

#[test]
fn unrefined_trees_do_break_the_rules() {
    // The differential test below means something only if the unrefined generator does
    // produce violations for both implementations to catch.
    let start = BASE.require("GQL-program").unwrap();
    let rejected = generate(&BASE, start, 1, 46)
        .iter()
        .filter(|t| accepts(&all_rules(PORTABLE), t).is_err())
        .count();
    assert!(rejected > 0);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(12))]

    #[test]
    fn automaton_and_verifier_agree(seed in any::<u64>(), max_depth in 30u32..=60, different in any::<bool>()) {
        let id086 = if different { DIFFERENT } else { PORTABLE };
        let start = BASE.require("GQL-program").unwrap();
        for tree in generate(&BASE, start, seed, max_depth) {
            let (automaton, broken) = verdicts(&tree, id086);
            prop_assert_eq!(automaton, broken.is_empty(), "{:?}", broken);
        }
    }

    #[test]
    fn refined_trees_satisfy_the_rules(seed in any::<u64>(), max_depth in 40u32..=70, different in any::<bool>()) {
        let id086 = if different { DIFFERENT } else { PORTABLE };
        let refined = refine(&BASE, &all_rules(id086), BASE.require("GQL-program").unwrap()).unwrap();
        let verifier = Verifier::new(Grammar::new(&ISO)).with_syntax_rules(id086);
        let analysis = Analysis::new(&refined.cfg, &StubProvider);
        if analysis.min_height(refined.start) > max_depth {
            return Ok(());
        }
        for tree in generate(&refined.cfg, refined.start, seed, max_depth) {
            let rendered = verifier.render(&tree);
            let violations = verifier.verify(&tree, &rendered);
            prop_assert!(violations.is_empty(), "{:?}", violations);
        }
    }
}
