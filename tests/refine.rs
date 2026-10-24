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

const RULES: [&str; 41] = [
    "18.9 SR 88",
    "10.1 SR 8",
    "10.2 SR 8",
    "18.7 SR 4",
    "17.6 SR 1",
    "16.4 SR 12",
    "9.1 SR 5",
    "9.1 SR 6",
    "9.1 SR 7",
    "9.2 SR 4",
    "9.2 SR 5",
    "9.2 SR 6",
    "12.8 SR 2",
    "13.6 SR 2",
    "14.5 SR 2",
    "14.2 SR 3",
    "14.2 SR 4",
    "14.12 SR 26",
    "20.16 SR 1",
    "16.6 SR 2",
    "8.2 SR 2",
    "18.2 SR 2",
    "18.2 SR 3",
    "18.3 SR 2",
    "18.3 SR 3",
    "18.3 SR 4",
    "16.4 SR 14",
    "20.24 SR 3",
    "21.3 SR 4",
    "16.4 SR 6",
    "13.1 SR 5",
    "16.7 SR 8",
    "16.7 SR 9",
    "16.7 SR 16",
    "16.7 SR 20",
    "16.11 SR 3",
    "16.12 SR 1",
    "16.12 SR 2",
    "16.12 SR 3",
    "16.12 SR 4",
    "16.4 SR 12",
];

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

/// `<-` followed by a quantifier.
fn quantified(quantifier: Plain) -> Plain {
    quantified_of(edge(), quantifier)
}

fn quantified_of(primary: Plain, quantifier: Plain) -> Plain {
    d(
        "quantified path primary",
        vec![primary, d("graph pattern quantifier", vec![quantifier])],
    )
}

fn questioned(primary: Plain) -> Plain {
    d(
        "questioned path primary",
        vec![primary, Plain::Term("?".into())],
    )
}

/// A bare `<-` as a path primary.
fn edge() -> Plain {
    d(
        "path primary",
        vec![d(
            "element pattern",
            vec![d(
                "edge pattern",
                vec![d(
                    "abbreviated edge pattern",
                    vec![Plain::Term("<-".into())],
                )],
            )],
        )],
    )
}

/// An empty `()` as a path primary.
fn node() -> Plain {
    d(
        "path primary",
        vec![d(
            "element pattern",
            vec![d(
                "node pattern",
                vec![
                    Plain::Term("(".into()),
                    d("element pattern filler", vec![]),
                    Plain::Term(")".into()),
                ],
            )],
        )],
    )
}

fn factor(x: Plain) -> Plain {
    d("path factor", vec![x])
}

/// A path term of these factors, concatenated left to right as the grammar does.
fn term(mut factors: Vec<Plain>) -> Plain {
    let mut t = d("path term", vec![factors.remove(0)]);
    for f in factors {
        t = d("path term", vec![d("path concatenation", vec![t, f])]);
    }
    t
}

/// `<unsigned integer>` spelled by these tokens (`0x` and `8`, not `0x8`).
fn integer(tokens: &[&str]) -> Plain {
    d(
        "unsigned integer",
        tokens.iter().map(|t| Plain::Term((*t).into())).collect(),
    )
}

fn fixed(tokens: &[&str]) -> Plain {
    d(
        "fixed quantifier",
        vec![
            Plain::Term("{".into()),
            integer(tokens),
            Plain::Term("}".into()),
        ],
    )
}

/// `{lower,upper}` with either side optional.
fn general(lower: Option<&[&str]>, upper: Option<&[&str]>) -> Plain {
    let mut parts = vec![Plain::Term("{".into())];
    if let Some(l) = lower {
        parts.push(d("lower bound", vec![integer(l)]));
    }
    parts.push(Plain::Term(",".into()));
    if let Some(u) = upper {
        parts.push(d("upper bound", vec![integer(u)]));
    }
    parts.push(Plain::Term("}".into()));
    d("general quantifier", parts)
}

fn plus() -> Plain {
    d("plus sign", vec![Plain::Term("+".into())])
}

fn star() -> Plain {
    d("asterisk", vec![Plain::Term("*".into())])
}

/// `{1,}` or `{1,2}`.
fn braces(upper: bool) -> Plain {
    general(Some(&["1"]), upper.then_some(&["2"][..]))
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

/// `() body`: a node pattern in front keeps 16.7 SR 16 out of the way.
fn path_pattern(prefix: Option<Plain>, body: Plain) -> Plain {
    let mut children: Vec<Plain> = prefix.into_iter().collect();
    children.push(d(
        "path pattern expression",
        vec![term(vec![factor(node()), factor(body)])],
    ));
    d("path pattern", children)
}

/// A path pattern of exactly this expression body.
fn bare_pattern(body: Plain) -> Plain {
    d(
        "path pattern",
        vec![d("path pattern expression", vec![body])],
    )
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
                vec![parens(Some("TRAIL"), term(vec![factor(edge())]))],
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
            d("simplified tertiary", vec![label()]),
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
        // What a syntax rule leaves no valid tree for, by its literal text: 17.6 SR 1 b asks a
        // parent reference with no schema reference for a solidus it cannot hold.
        let ruled_out = |p: usize| {
            let d = gql_proof::describe(&BASE, p as u32);
            d.starts_with("<catalog object parent reference> ::= <catalog object parent reference/rep")
                // A reading, not the text: every declared binding table type is closed and
                // tables are not typed (refine::ClosedInitializerTypes).
                || d.starts_with("<opt typed binding table initializer/opt1> ::=")
        };
        let missing: Vec<String> = (0..copies.len())
            .filter(|&p| !copies[p] && !ruled_out(p))
            .map(|p| gql_proof::describe(&BASE, p as u32))
            .collect();
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
            let why = accepts(&all_rules(id086), &tree).err();
            prop_assert_eq!(
                automaton,
                broken.is_empty(),
                "{:?} automaton: {:?} in {}",
                broken,
                why,
                Verifier::new(Grammar::new(&ISO)).render(&tree)
            );
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
        // The value-size limits (21.2 SR 18, 20, 21.3 SR 5 b under H2) are the gate's alone:
        // no automaton counts digits, and a random deep tree spells long numbers.
        const GATE_ONLY: [&str; 3] = ["21.2 SR 18", "21.2 SR 20", "21.3 SR 5"];
        for tree in generate(&refined.cfg, refined.start, seed, max_depth) {
            let rendered = verifier.render(&tree);
            let violations: Vec<_> = verifier
                .verify(&tree, &rendered)
                .into_iter()
                .filter(|v| !GATE_ONLY.contains(&v.rule))
                .collect();
            prop_assert!(violations.is_empty(), "{:?}", violations);
        }
    }
}

// --- 16.7 SR 8, 16, 20 and 16.11 SR 3: minimum node count and path length -----------------

fn one(pattern: Plain) -> Plain {
    graph_pattern(None, vec![pattern], None)
}

fn trail_pattern(body: Plain) -> Plain {
    d(
        "path pattern",
        vec![
            mode_prefix("TRAIL"),
            d("path pattern expression", vec![body]),
        ],
    )
}

#[test]
fn a_bare_edge_gets_implicit_nodes() {
    expect(&one(bare_pattern(factor(edge()))), PORTABLE, None);
    expect(
        &one(bare_pattern(term(vec![factor(edge()), factor(edge())]))),
        PORTABLE,
        None,
    );
}

#[test]
fn a_questioned_or_zero_quantified_edge_alone_has_no_node() {
    expect(
        &one(bare_pattern(factor(questioned(edge())))),
        PORTABLE,
        Some("16.7 SR 16"),
    );
    let parens = d("path primary", vec![parens(None, factor(edge()))]);
    expect(
        &one(bare_pattern(factor(questioned(parens)))),
        PORTABLE,
        Some("16.7 SR 16"),
    );
    expect(
        &one(bare_pattern(factor(quantified(general(
            None,
            Some(&["8"]),
        ))))),
        PORTABLE,
        Some("16.7 SR 16"),
    );
    expect(
        &one(bare_pattern(factor(quantified(general(
            Some(&["0", "_", "0"]),
            Some(&["8"]),
        ))))),
        PORTABLE,
        Some("16.7 SR 16"),
    );
    // TRAIL <- *: guarded for 16.4 SR 14, still no node.
    expect(
        &one(trail_pattern(factor(quantified(star())))),
        PORTABLE,
        Some("16.7 SR 16"),
    );
}

#[test]
fn a_positive_lower_bound_or_a_node_beside_keeps_nodes() {
    expect(
        &one(bare_pattern(factor(quantified(fixed(&["1"]))))),
        PORTABLE,
        None,
    );
    expect(
        &one(bare_pattern(factor(quantified(fixed(&["0x", "8"]))))),
        PORTABLE,
        None,
    );
    expect(
        &one(trail_pattern(factor(quantified(plus())))),
        PORTABLE,
        None,
    );
    expect(
        &one(bare_pattern(factor(quantified(general(
            Some(&["1"]),
            None,
        ))))),
        PORTABLE,
        Some("16.4 SR 14"),
    );
    expect(
        &one(bare_pattern(term(vec![
            factor(node()),
            factor(quantified(general(None, Some(&["8"])))),
            factor(node()),
        ]))),
        PORTABLE,
        None,
    );
    expect(
        &one(bare_pattern(term(vec![
            factor(questioned(edge())),
            factor(node()),
        ]))),
        PORTABLE,
        None,
    );
}

#[test]
fn a_union_takes_the_smallest_operand() {
    let union = |a: Plain, b: Plain| d("path pattern union", vec![a, Plain::Term("|".into()), b]);
    let nodes = term(vec![factor(node())]);
    let none = term(vec![factor(questioned(edge()))]);
    expect(
        &one(bare_pattern(union(nodes.clone(), nodes.clone()))),
        PORTABLE,
        None,
    );
    expect(
        &one(bare_pattern(union(nodes, none))),
        PORTABLE,
        Some("16.7 SR 16"),
    );
}

#[test]
fn a_repeated_primary_has_a_positive_length() {
    let zero = d(
        "path primary",
        vec![parens(None, factor(questioned(edge())))],
    );
    expect(
        &one(path_pattern(None, questioned(zero.clone()))),
        PORTABLE,
        Some("16.7 SR 8"),
    );
    expect(
        &one(path_pattern(None, quantified_of(zero, fixed(&["2"])))),
        PORTABLE,
        Some("16.7 SR 8"),
    );
    expect(
        &one(path_pattern(None, quantified_of(node(), fixed(&["2"])))),
        PORTABLE,
        Some("16.7 SR 8"),
    );
    let one_edge = d("path primary", vec![parens(None, factor(edge()))]);
    expect(
        &one(path_pattern(None, questioned(one_edge))),
        PORTABLE,
        None,
    );
}

#[test]
fn a_named_subpath_has_a_node() {
    let named = |body: Plain| {
        d(
            "parenthesized path pattern expression",
            vec![
                Plain::Term("(".into()),
                d("subpath variable declaration", vec![]),
                d("path pattern expression", vec![body]),
                Plain::Term(")".into()),
            ],
        )
    };
    expect(
        &one(path_pattern(
            None,
            named(factor(quantified(general(None, Some(&["8"]))))),
        )),
        PORTABLE,
        Some("16.7 SR 20"),
    );
    expect(
        &one(path_pattern(None, named(factor(quantified(fixed(&["1"])))))),
        PORTABLE,
        None,
    );
}

#[test]
fn a_quantifier_does_not_nest_a_quantifier() {
    let inner = as_primary(parens(None, factor(quantified(plus()))));
    expect(
        &one(trail_pattern(factor(quantified_of(inner, plus())))),
        PORTABLE,
        Some("16.7 SR 9"),
    );
}

#[test]
fn an_upper_bound_is_not_zero() {
    // `{0}` is `{0,0}`.
    expect(
        &one(path_pattern(None, quantified(fixed(&["0"])))),
        PORTABLE,
        Some("16.11 SR 3"),
    );
    expect(
        &one(path_pattern(None, quantified(fixed(&["0b", "0"])))),
        PORTABLE,
        Some("16.11 SR 3"),
    );
    expect(
        &one(path_pattern(
            None,
            quantified(general(Some(&["1"]), Some(&["0"]))),
        )),
        PORTABLE,
        Some("16.11 SR 3"),
    );
    expect(
        &one(path_pattern(
            None,
            quantified(general(None, Some(&["0x", "0", "_", "0"]))),
        )),
        PORTABLE,
        Some("16.11 SR 3"),
    );
}

// --- 16.12 SR 1-4 and the minimums of simplified expressions ------------------------------

fn sppe(contents: Plain) -> Plain {
    d(
        "simplified path pattern expression",
        vec![d(
            "simplified defaulting left",
            vec![
                Plain::Term("<-/".into()),
                d("simplified contents", vec![contents]),
                Plain::Term("/-".into()),
            ],
        )],
    )
}

fn label() -> Plain {
    d("simplified primary", vec![d("label name", vec![])])
}

fn grouped(contents: Plain) -> Plain {
    d(
        "simplified primary",
        vec![
            Plain::Term("(".into()),
            d("simplified contents", vec![contents]),
            Plain::Term(")".into()),
        ],
    )
}

fn negation(x: Plain) -> Plain {
    d("simplified negation", vec![Plain::Term("!".into()), x])
}

fn conjunction(a: Plain, b: Plain) -> Plain {
    d(
        "simplified conjunction",
        vec![a, Plain::Term("&".into()), b],
    )
}

fn override_left(x: Plain) -> Plain {
    d(
        "simplified direction override",
        vec![d(
            "simplified override left",
            vec![Plain::Term("<".into()), x],
        )],
    )
}

fn squantified(t: Plain, q: Plain) -> Plain {
    d(
        "simplified quantified",
        vec![
            d("simplified tertiary", vec![t]),
            d("graph pattern quantifier", vec![q]),
        ],
    )
}

fn squestioned(t: Plain) -> Plain {
    d(
        "simplified questioned",
        vec![d("simplified tertiary", vec![t]), Plain::Term("?".into())],
    )
}

fn sconcat(a: Plain, b: Plain) -> Plain {
    d(
        "simplified concatenation",
        vec![
            d("simplified term", vec![a]),
            d("simplified factor low", vec![b]),
        ],
    )
}

fn as_primary(x: Plain) -> Plain {
    d("path primary", vec![x])
}

#[test]
fn simplified_shapes() {
    let pattern = |contents: Plain| one(bare_pattern(factor(as_primary(sppe(contents)))));
    expect(&pattern(label()), PORTABLE, None);
    expect(&pattern(conjunction(label(), label())), PORTABLE, None);
    let questioned_in_conjunction = conjunction(label(), squestioned(label()));
    expect(
        &pattern(questioned_in_conjunction),
        PORTABLE,
        Some("16.12 SR 4"),
    );
    let quantified_in_override = override_left(grouped(squantified(label(), fixed(&["1"]))));
    expect(
        &pattern(quantified_in_override),
        PORTABLE,
        Some("16.12 SR 3"),
    );
    let nested_override = override_left(grouped(override_left(label())));
    expect(&pattern(nested_override), PORTABLE, Some("16.12 SR 2"));
    let concatenation_in_negation = negation(grouped(sconcat(label(), label())));
    expect(
        &pattern(concatenation_in_negation),
        PORTABLE,
        Some("16.12 SR 1"),
    );
    // Reading: what becomes a label expression holds no direction override either.
    let override_in_conjunction = conjunction(label(), override_left(label()));
    expect(
        &pattern(override_in_conjunction),
        PORTABLE,
        Some("16.12 SR 4"),
    );
    let override_in_negation = negation(grouped(override_left(label())));
    expect(&pattern(override_in_negation), PORTABLE, Some("16.12 SR 1"));
}

#[test]
fn simplified_minimums() {
    let pattern = |contents: Plain| one(bare_pattern(factor(as_primary(sppe(contents)))));
    // `<-/ a ? /-` has no node, `<-/ a /- ?` neither, `<-/ a b /-` and `<-/ a ? b /-` do.
    expect(&pattern(squestioned(label())), PORTABLE, Some("16.7 SR 16"));
    let questioned_whole = one(bare_pattern(factor(questioned(as_primary(sppe(label()))))));
    expect(&questioned_whole, PORTABLE, Some("16.7 SR 16"));
    expect(&pattern(sconcat(label(), label())), PORTABLE, None);
    expect(
        &pattern(sconcat(squestioned(label()), label())),
        PORTABLE,
        None,
    );
    // `<-/ ( a ? ) ? /-`: the questioned primary has length 0.
    let twice = sppe(squestioned(grouped(squestioned(label()))));
    expect(
        &one(path_pattern(None, as_primary(twice))),
        PORTABLE,
        Some("16.7 SR 8"),
    );
}

// --- 16.4 SR 12 ---------------------------------------------------------------------------

#[test]
fn a_selective_pattern_stands_alone_under_different_edges() {
    let selective = || path_pattern(Some(search_prefix("any path search")), factor(edge()));
    let plain = || path_pattern(None, factor(edge()));
    expect(
        &graph_pattern(Some("DIFFERENT"), vec![selective(), plain()], None),
        PORTABLE,
        Some("16.4 SR 12"),
    );
    expect(
        &graph_pattern(None, vec![plain(), selective()], None),
        DIFFERENT,
        Some("16.4 SR 12"),
    );
    expect(
        &graph_pattern(Some("REPEATABLE"), vec![selective(), plain()], None),
        PORTABLE,
        None,
    );
    expect(
        &graph_pattern(None, vec![selective(), plain()], None),
        PORTABLE,
        None,
    );
    expect(
        &graph_pattern(Some("DIFFERENT"), vec![selective()], None),
        PORTABLE,
        None,
    );
    expect(
        &graph_pattern(Some("DIFFERENT"), vec![plain(), plain()], None),
        PORTABLE,
        None,
    );
}

// --- 16.11 SR 3 a ii: the order of the bounds is settled at spelling time, not in the grammar

/// The automaton knows zero or nonzero, so it accepts `{ 8 , 2 }`; the checker reads the
/// values and reports it. `tree::order_bounds` keeps the two apart in a generated set, in
/// both generators.
#[test]
fn an_upper_bound_below_the_lower_is_the_checkers_alone() {
    let out_of_order = one(bare_pattern(factor(quantified(general(
        Some(&["8"]),
        Some(&["2"]),
    )))));
    let (automaton, broken) = verdicts(&out_of_order, PORTABLE);
    assert!(automaton, "the automaton does not read values");
    assert!(broken.is_empty(), "the rules compiled into the grammar: {broken:?}");
    let verifier = Verifier::new(Grammar::new(&ISO)).with_syntax_rules(PORTABLE);
    let reported: Vec<&str> = verifier
        .verify(&out_of_order, &verifier.render(&out_of_order))
        .iter()
        .map(|v| v.rule)
        .filter(|r| *r != "ISO BNF")
        .collect();
    assert_eq!(reported, ["16.11 SR 3 a ii"]);
    expect(
        &one(bare_pattern(factor(quantified(general(
            Some(&["2"]),
            Some(&["8"]),
        ))))),
        PORTABLE,
        None,
    );
    expect(
        &one(bare_pattern(factor(quantified(general(
            Some(&["8"]),
            Some(&["8"]),
        ))))),
        PORTABLE,
        None,
    );
}

#[test]
fn a_raised_bound_keeps_its_digits_and_radix() {
    use gql_proof::tree::raised_bound;
    use gql_proof::verify::unsigned_integer_value;
    use rand::SeedableRng;
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(7);
    for (text, lower) in [
        ("0o2", 8),
        ("0b1", 8),
        ("0xA", 11),
        ("2", 8),
        ("0o_2", 8),
        ("8_08", 900),
        ("0b1", 300),
        ("08", 10),
    ] {
        for _ in 0..8 {
            let raised = raised_bound(text, lower, &mut rng);
            let value = unsigned_integer_value(&raised);
            assert!(value >= lower, "{text} under {lower} became {raised} ({value})");
            let digits = text.trim_start_matches("0x").trim_start_matches("0o").trim_start_matches("0b");
            assert!(raised.ends_with(digits), "{text} under {lower} became {raised}");
            assert_eq!(&raised[..text.len() - digits.len()], &text[..text.len() - digits.len()]);
            if lower <= 255 {
                assert!(value <= 255, "{text} under {lower} became {raised} ({value})");
            }
        }
    }
    assert_eq!(unsigned_integer_value(&raised_bound("0o2", 8, &mut rng)) % 8, 2);
}

// --- 20.24 SR 3: TRIM's FROM follows a specification or a trim string ----------------------

fn trim(parts: Vec<Plain>) -> Plain {
    d("trim operands", parts)
}

fn trim_source() -> Plain {
    d("trim source", vec![])
}

#[test]
fn a_bare_from_in_trim_is_refused() {
    expect(&trim(vec![kw("FROM"), trim_source()]), PORTABLE, Some("20.24 SR 3"));
    expect(
        &trim(vec![
            d("trim specification", vec![kw("BOTH")]),
            kw("FROM"),
            trim_source(),
        ]),
        PORTABLE,
        None,
    );
    expect(
        &trim(vec![
            d("trim character string", vec![]),
            kw("FROM"),
            trim_source(),
        ]),
        PORTABLE,
        None,
    );
    expect(
        &trim(vec![
            d("trim specification", vec![kw("LEADING")]),
            d("trim character string", vec![]),
            kw("FROM"),
            trim_source(),
        ]),
        PORTABLE,
        None,
    );
    expect(&trim(vec![trim_source()]), PORTABLE, None);
    expect(
        &d(
            "byte string trim operands",
            vec![kw("FROM"), d("byte string trim source", vec![])],
        ),
        PORTABLE,
        Some("20.24 SR 3"),
    );
    expect(
        &d(
            "byte string trim operands",
            vec![
                d("trim byte string", vec![]),
                kw("FROM"),
                d("byte string trim source", vec![]),
            ],
        ),
        PORTABLE,
        None,
    );
    // BTRIM(x, y): a trim string with no FROM, which must not leak upwards.
    expect(
        &d(
            "multi-character trim function",
            vec![
                kw("BTRIM"),
                Plain::Term("(".into()),
                trim_source(),
                Plain::Term(",".into()),
                d("trim character string", vec![]),
                Plain::Term(")".into()),
            ],
        ),
        PORTABLE,
        None,
    );
}

// --- 21.3 SR 4: a delimited identifier is not empty -----------------------------------------

fn quoted(accent: bool, characters: usize) -> Plain {
    let (quote, seq, unbroken, rep) = if accent {
        (
            "grave accent",
            "accent quoted character sequence",
            "unbroken accent quoted character sequence",
            "accent quoted character representation",
        )
    } else {
        (
            "double quote",
            "double quoted character sequence",
            "unbroken double quoted character sequence",
            "double quoted character representation",
        )
    };
    let mark = || d(quote, vec![Plain::Term(if accent { "`" } else { "\"" }.into())]);
    let mut inner = vec![mark()];
    for _ in 0..characters {
        inner.push(d(
            rep,
            vec![Plain::Leaf {
                def: "character representation".into(),
                text: "x".into(),
            }],
        ));
    }
    inner.push(mark());
    d(seq, vec![d(unbroken, inner)])
}

fn delimited(accent: bool, characters: usize) -> Plain {
    d("delimited identifier", vec![quoted(accent, characters)])
}

#[test]
fn an_empty_delimited_identifier_is_refused() {
    expect(&delimited(false, 0), PORTABLE, Some("21.3 SR 4"));
    expect(&delimited(true, 0), PORTABLE, Some("21.3 SR 4"));
    expect(&delimited(false, 1), PORTABLE, None);
    expect(&delimited(true, 2), PORTABLE, None);
    // `""` is the empty string literal, the same sequence under another definition.
    expect(
        &d("character string literal", vec![quoted(false, 0)]),
        PORTABLE,
        None,
    );
}

// --- 18.2 SR 2, 3 and 18.3 SR 2, 3, 4: the shape of a node or edge type specification ---------

fn ident(text: &str) -> Plain {
    d("regular identifier", vec![Plain::Term(text.into())])
}

fn key_label_set() -> Plain {
    d("node type key label set", vec![d("implies", vec![kw("IMPLIES")])])
}

fn properties() -> Plain {
    d(
        "node type implied content",
        vec![d(
            "node type property types",
            vec![d(
                "property types specification",
                vec![Plain::Term("{".into()), Plain::Term("}".into())],
            )],
        )],
    )
}

/// `NODE TYPE [name] <filler> [AS alias]` as a node type phrase.
fn node_phrase(name: Option<&str>, filler: Plain, alias: Option<&str>) -> Plain {
    let mut filler_items = Vec::new();
    if let Some(n) = name {
        filler_items.push(d("node type name", vec![ident(n)]));
    }
    filler_items.push(d("node type filler", vec![filler]));
    let mut items = vec![d("node synonym", vec![kw("NODE")]), kw("TYPE")];
    items.push(d("node type phrase filler", filler_items));
    if let Some(a) = alias {
        items.push(kw("AS"));
        items.push(d("local node type alias", vec![ident(a)]));
    }
    d("node type specification", vec![d("node type phrase", items)])
}

fn closed_node(spec: Plain) -> Plain {
    d("closed node reference value type", vec![spec])
}

/// A value type in a graph type body's element list, where nothing is closed.
fn in_body(spec: Plain) -> Plain {
    d(
        "graph type specification body",
        vec![d(
            "element type list",
            vec![d("element type specification", vec![spec])],
        )],
    )
}

#[test]
fn a_closed_node_type_has_no_alias_key_labels_or_name() {
    expect(&closed_node(node_phrase(None, properties(), None)), PORTABLE, None);
    expect(
        &closed_node(node_phrase(None, properties(), Some("a"))),
        PORTABLE,
        Some("18.2 SR 2"),
    );
    expect(
        &closed_node(node_phrase(None, key_label_set(), None)),
        PORTABLE,
        Some("18.2 SR 2"),
    );
    expect(
        &closed_node(node_phrase(Some("n"), properties(), None)),
        PORTABLE,
        Some("18.2 SR 2"),
    );
    // The same specifications in a graph type body are fine.
    expect(&in_body(node_phrase(None, properties(), Some("a"))), PORTABLE, None);
    expect(&in_body(node_phrase(None, key_label_set(), None)), PORTABLE, None);
    expect(&in_body(node_phrase(Some("n"), properties(), None)), PORTABLE, None);
}

#[test]
fn a_named_node_type_has_no_key_labels_or_alias() {
    expect(
        &in_body(node_phrase(Some("n"), key_label_set(), None)),
        PORTABLE,
        Some("18.2 SR 3"),
    );
    expect(
        &in_body(node_phrase(Some("n"), properties(), Some("a"))),
        PORTABLE,
        Some("18.2 SR 3"),
    );
}

#[test]
fn a_nested_node_type_is_judged_by_its_own_parent() {
    // A closed node type whose property's type is a graph type with an aliased node type:
    // the inner specification is not simply contained in the closed reference value type.
    let inner = in_body(node_phrase(None, properties(), Some("a")));
    let property_types = d(
        "node type implied content",
        vec![d(
            "node type property types",
            vec![d(
                "property types specification",
                vec![d(
                    "property type",
                    vec![d(
                        "value type",
                        vec![d(
                            "closed graph reference value type",
                            vec![d("nested graph type specification", vec![inner])],
                        )],
                    )],
                )],
            )],
        )],
    );
    expect(&closed_node(node_phrase(None, property_types, None)), PORTABLE, None);
    // But a closed node type nested in the property's type is judged closed again.
    let inner = closed_node(node_phrase(None, properties(), Some("a")));
    let property_types = d(
        "node type implied content",
        vec![d(
            "node type property types",
            vec![d(
                "property types specification",
                vec![d("property type", vec![d("value type", vec![inner])])],
            )],
        )],
    );
    expect(
        &closed_node(node_phrase(None, property_types, None)),
        PORTABLE,
        Some("18.2 SR 2"),
    );
}

fn endpoint(alias: Option<&str>, filler: Option<Plain>, def: &str) -> Plain {
    let mut items = vec![Plain::Term("(".into())];
    if let Some(a) = alias {
        let which = if def.starts_with("source") {
            "source node type alias"
        } else {
            "destination node type alias"
        };
        items.push(d(which, vec![ident(a)]));
    }
    if let Some(f) = filler {
        items.push(d("node type filler", vec![f]));
    }
    items.push(Plain::Term(")".into()));
    d(def, items)
}

/// `[kind] EDGE TYPE [name] <source> -[ <filler> ]-> <destination>` as an edge type pattern.
fn edge_pattern(
    kind: Option<&str>,
    name: Option<&str>,
    source: Plain,
    filler: Plain,
    destination: Plain,
    directed: bool,
) -> Plain {
    let mut items = Vec::new();
    if let Some(k) = kind {
        items.push(d("edge kind", vec![kw(k)]));
    }
    if let Some(n) = name {
        items.push(d("edge synonym", vec![kw("EDGE")]));
        items.push(kw("TYPE"));
        items.push(d("edge type name", vec![ident(n)]));
    }
    let arc = d(
        "arc type pointing right",
        vec![
            Plain::Term("-[".into()),
            d("edge type filler", vec![filler]),
            Plain::Term("]->".into()),
        ],
    );
    let shape = if directed {
        d(
            "edge type pattern directed",
            vec![d(
                "edge type pattern pointing right",
                vec![source, arc, destination],
            )],
        )
    } else {
        d("edge type pattern undirected", vec![source, arc, destination])
    };
    items.push(shape);
    d("edge type specification", vec![d("edge type pattern", items)])
}

fn edge_properties() -> Plain {
    d(
        "edge type implied content",
        vec![d(
            "edge type property types",
            vec![d(
                "property types specification",
                vec![Plain::Term("{".into()), Plain::Term("}".into())],
            )],
        )],
    )
}

fn edge_key_label_set() -> Plain {
    d("edge type key label set", vec![d("implies", vec![kw("IMPLIES")])])
}

fn closed_edge(spec: Plain) -> Plain {
    d("closed edge reference value type", vec![spec])
}

fn plain_source() -> Plain {
    endpoint(None, None, "source node type reference")
}

fn plain_destination() -> Plain {
    endpoint(None, None, "destination node type reference")
}

#[test]
fn a_closed_edge_type_has_no_key_labels_name_or_aliases() {
    let plain = || edge_pattern(None, None, plain_source(), edge_properties(), plain_destination(), true);
    expect(&closed_edge(plain()), PORTABLE, None);
    expect(
        &closed_edge(edge_pattern(None, None, plain_source(), edge_key_label_set(), plain_destination(), true)),
        PORTABLE,
        Some("18.3 SR 2"),
    );
    expect(
        &closed_edge(edge_pattern(None, Some("e"), plain_source(), edge_properties(), plain_destination(), true)),
        PORTABLE,
        Some("18.3 SR 2"),
    );
    expect(
        &closed_edge(edge_pattern(
            None,
            None,
            endpoint(Some("a"), None, "source node type reference"),
            edge_properties(),
            plain_destination(),
            true,
        )),
        PORTABLE,
        Some("18.3 SR 2"),
    );
    expect(
        &closed_edge(edge_pattern(
            None,
            None,
            plain_source(),
            edge_properties(),
            endpoint(None, Some(key_label_set()), "destination node type reference"),
            true,
        )),
        PORTABLE,
        Some("18.3 SR 2"),
    );
    // In a graph type body, all of these are fine.
    expect(
        &in_body(edge_pattern(None, Some("e"), plain_source(), edge_properties(), plain_destination(), true)),
        PORTABLE,
        None,
    );
    expect(
        &in_body(edge_pattern(
            None,
            None,
            endpoint(None, Some(key_label_set()), "source node type reference"),
            edge_key_label_set(),
            plain_destination(),
            true,
        )),
        PORTABLE,
        None,
    );
}

#[test]
fn a_named_edge_type_has_no_key_labels() {
    expect(
        &in_body(edge_pattern(None, Some("e"), plain_source(), edge_key_label_set(), plain_destination(), true)),
        PORTABLE,
        Some("18.3 SR 3"),
    );
}

#[test]
fn the_edge_kind_matches_the_shape() {
    expect(
        &in_body(edge_pattern(Some("DIRECTED"), Some("e"), plain_source(), edge_properties(), plain_destination(), true)),
        PORTABLE,
        None,
    );
    expect(
        &in_body(edge_pattern(Some("UNDIRECTED"), Some("e"), plain_source(), edge_properties(), plain_destination(), false)),
        PORTABLE,
        None,
    );
    expect(
        &in_body(edge_pattern(Some("DIRECTED"), Some("e"), plain_source(), edge_properties(), plain_destination(), false)),
        PORTABLE,
        Some("18.3 SR 4"),
    );
    expect(
        &in_body(edge_pattern(Some("UNDIRECTED"), Some("e"), plain_source(), edge_properties(), plain_destination(), true)),
        PORTABLE,
        Some("18.3 SR 4"),
    );
    // Reading: no edge kind, no constraint.
    expect(
        &in_body(edge_pattern(None, None, plain_source(), edge_properties(), plain_destination(), false)),
        PORTABLE,
        None,
    );
}

// --- 18.9 SR 7, 10, 13, 21, 29, 38, 40: type values, settled at spelling time -------------

fn length(def: &str, tokens: &[&str]) -> Plain {
    d(def, vec![integer(tokens)])
}

fn string_type(min: Option<&[&str]>, max: &[&str]) -> Plain {
    let mut items = vec![kw("STRING"), Plain::Term("(".into())];
    if let Some(min) = min {
        items.push(length("min length", min));
        items.push(Plain::Term(",".into()));
    }
    items.push(length("max length", max));
    items.push(Plain::Term(")".into()));
    d("character string type", items)
}

fn decimal(precision: &[&str], scale: Option<&[&str]>) -> Plain {
    let mut items = vec![kw("DECIMAL"), Plain::Term("(".into())];
    items.push(d("precision", vec![d("unsigned decimal integer", precision.iter().map(|t| Plain::Term((*t).into())).collect())]));
    if let Some(scale) = scale {
        items.push(Plain::Term(",".into()));
        items.push(d("scale", vec![d("unsigned decimal integer", scale.iter().map(|t| Plain::Term((*t).into())).collect())]));
    }
    items.push(Plain::Term(")".into()));
    d("decimal exact numeric type", items)
}

fn float(precision: &[&str]) -> Plain {
    d(
        "approximate numeric type",
        vec![
            kw("FLOAT"),
            Plain::Term("(".into()),
            d("precision", vec![d("unsigned decimal integer", precision.iter().map(|t| Plain::Term((*t).into())).collect())]),
            Plain::Term(")".into()),
        ],
    )
}

/// The syntax rules the verifier reports on `tree`, the ISO BNF left aside.
fn reported(tree: &Plain) -> Vec<&'static str> {
    let verifier = Verifier::new(Grammar::new(&ISO)).with_syntax_rules(PORTABLE);
    verifier
        .verify(tree, &verifier.render(tree))
        .iter()
        .map(|v| v.rule)
        .filter(|r| *r != "ISO BNF")
        .collect()
}

/// The automaton does not read values, so the checker alone reports these; `tree::order_bounds`
/// keeps them out of a generated set.
#[test]
fn type_values_are_the_checkers_alone() {
    let cases: Vec<(Plain, Vec<&str>)> = vec![
        (string_type(None, &["8"]), vec![]),
        (string_type(None, &["0"]), vec!["18.9 SR 7"]),
        (string_type(None, &["0b", "0"]), vec!["18.9 SR 7"]),
        (string_type(Some(&["8"]), &["2"]), vec!["18.9 SR 13"]),
        (string_type(Some(&["2"]), &["8"]), vec![]),
        (string_type(Some(&["0"]), &["0"]), vec!["18.9 SR 7"]),
        (
            d("character string type", vec![kw("CHAR"), Plain::Term("(".into()), length("fixed length", &["0"]), Plain::Term(")".into())]),
            vec!["18.9 SR 10"],
        ),
        (
            d("byte string type", vec![kw("BYTES"), Plain::Term("(".into()), length("min length", &["3"]), Plain::Term(",".into()), length("max length", &["2"]), Plain::Term(")".into())]),
            vec!["18.9 SR 21"],
        ),
        (
            d("list value type", vec![kw("LIST"), Plain::Term("[".into()), length("max length", &["0"]), Plain::Term("]".into())]),
            vec!["18.9 SR 7"],
        ),
        (decimal(&["8"], None), vec![]),
        (decimal(&["0"], None), vec!["18.9 SR 29"]),
        (decimal(&["2"], Some(&["8"])), vec!["18.9 SR 38"]),
        (decimal(&["8"], Some(&["8"])), vec![]),
        (float(&["0"]), vec!["18.9 SR 29"]),
        (float(&["1"]), vec!["18.9 SR 40"]),
        (float(&["2"]), vec![]),
        // An Arabic-Indic digit three reads as 3 (21.4 SR 2).
        (float(&["\u{0663}"]), vec![]),
    ];
    for (tree, want) in cases {
        let (automaton, broken) = verdicts(&tree, PORTABLE);
        assert!(automaton, "the automaton does not read values");
        assert!(broken.is_empty(), "{broken:?}");
        assert_eq!(reported(&tree), want, "{}", tree.text());
    }
}

#[test]
fn digit_values_follow_unicode_runs() {
    use gql_proof::verify::{digit_value, unsigned_integer_value};
    assert_eq!(digit_value('7'), Some(7));
    assert_eq!(digit_value('\u{0660}'), Some(0));
    assert_eq!(digit_value('\u{0663}'), Some(3));
    assert_eq!(digit_value('\u{09EF}'), Some(9));
    // Mathematical digits: five runs of ten in a row.
    assert_eq!(digit_value('\u{1D7D8}'), Some(0));
    assert_eq!(digit_value('\u{1D7E3}'), Some(1));
    assert_eq!(digit_value('a'), None);
    assert_eq!(unsigned_integer_value("1\u{0663}"), 13);
    assert_eq!(unsigned_integer_value("0x1_A"), 26);
}

/// Every value rule above, repaired in a generated tree by `tree::order_bounds`, the way both
/// generators run it.
#[test]
fn order_bounds_raises_type_values() {
    use gql_proof::tree::order_bounds;
    use rand::SeedableRng;
    let analysis = Analysis::new(&BASE, &StubProvider);
    let verifier = Verifier::new(Grammar::new(&ISO)).with_syntax_rules(PORTABLE);
    for (def, text) in [
        ("character string type", "STRING(0)"),
        ("character string type", "STRING(8,2)"),
        ("character string type", "CHAR(0b0)"),
        ("character string type", "VARCHAR(0x0)"),
        ("byte string type", "BYTES(0xA,8)"),
        ("list value type", "LIST[0]"),
        ("decimal exact numeric type", "DECIMAL(0)"),
        ("decimal exact numeric type", "DECIMAL(2,8)"),
        ("signed binary exact numeric type", "INT(0)"),
        ("approximate numeric type", "FLOAT(1)"),
        ("approximate numeric type", "FLOAT(0,8)"),
        ("general quantifier", "{8,2}"),
    ] {
        let nt = BASE.require(def).unwrap();
        let mut tree = analysis.spell(nt, text).unwrap_or_else(|| panic!("{text} does not spell"));
        let before = tree.export(&BASE);
        assert!(!reported(&before).is_empty(), "{text} is not broken");
        let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
        assert!(order_bounds(&BASE, &mut tree, &|nt, t| analysis.spell(nt, t), &mut rng), "{text} not raised");
        let after = tree.export(&BASE);
        assert!(reported(&after).is_empty(), "{text} became {}: {:?}", after.text(), reported(&after));
        assert!(verifier.verify(&after, &verifier.render(&after)).is_empty(), "{text} became {}", after.text());
    }
}

// --- 8.2 SR 2: exactly one transaction access mode --------------------------------------------

fn access_mode() -> Plain {
    d(
        "transaction mode",
        vec![d("transaction access mode", vec![kw("READ"), kw("ONLY")])],
    )
}

fn characteristics(modes: Vec<Plain>) -> Plain {
    d("transaction characteristics", modes)
}

#[test]
fn transaction_characteristics_hold_one_access_mode() {
    expect(&characteristics(vec![access_mode()]), PORTABLE, None);
    expect(
        &characteristics(vec![access_mode(), Plain::Term(",".into()), access_mode()]),
        PORTABLE,
        Some("8.2 SR 2"),
    );
    let implementation = d(
        "transaction mode",
        vec![Plain::Leaf {
            def: "implementation-defined access mode".into(),
            text: "x".into(),
        }],
    );
    expect(
        &characteristics(vec![implementation.clone()]),
        PORTABLE,
        Some("8.2 SR 2"),
    );
    expect(
        &characteristics(vec![access_mode(), Plain::Term(",".into()), implementation]),
        PORTABLE,
        None,
    );
}

// --- 20.16 SR 1 a: TRIM's list count, by its shape ----------------------------------------------

fn nve_of(primary: Plain) -> Plain {
    d(
        "numeric value expression",
        vec![d("term", vec![d("factor", vec![d("numeric primary", vec![primary])])])],
    )
}

fn literal(def_chain: &[&str], leaf: Plain) -> Plain {
    def_chain.iter().rev().fold(leaf, |inner, def| d(def, vec![inner]))
}

fn int_primary(tokens: &[&str]) -> Plain {
    literal(
        &[
            "value expression primary",
            "non-parenthesized value expression primary",
            "non-parenthesized value expression primary special case",
            "unsigned value specification",
            "unsigned literal",
            "unsigned numeric literal",
            "exact numeric literal",
        ],
        integer(tokens),
    )
}

fn trim_list(count: Plain) -> Plain {
    d(
        "trim list function",
        vec![
            kw("TRIM"),
            Plain::Term("(".into()),
            d("list value expression", vec![]),
            Plain::Term(",".into()),
            count,
            Plain::Term(")".into()),
        ],
    )
}

#[test]
fn trims_count_is_an_integer_form() {
    expect(&trim_list(nve_of(int_primary(&["2"]))), PORTABLE, None);
    let sum = d(
        "numeric value expression",
        vec![
            nve_of(int_primary(&["2"])),
            d("plus sign", vec![Plain::Term("+".into())]),
            d("term", vec![d("factor", vec![d("numeric primary", vec![int_primary(&["1"])])])]),
        ],
    );
    expect(&trim_list(sum), PORTABLE, None);
    let quotient = d(
        "numeric value expression",
        vec![d(
            "term",
            vec![
                d("term", vec![d("factor", vec![d("numeric primary", vec![int_primary(&["2"])])])]),
                d("solidus", vec![Plain::Term("/".into())]),
                d("factor", vec![d("numeric primary", vec![int_primary(&["1"])])]),
            ],
        )],
    );
    expect(&trim_list(quotient), PORTABLE, Some("20.16 SR 1"));
    let variable = nve_of(d(
        "value expression primary",
        vec![d(
            "non-parenthesized value expression primary",
            vec![d("binding variable reference", vec![])],
        )],
    ));
    expect(&trim_list(variable), PORTABLE, Some("20.16 SR 1"));
    let null = nve_of(literal(
        &[
            "value expression primary",
            "non-parenthesized value expression primary",
            "non-parenthesized value expression primary special case",
            "unsigned value specification",
            "unsigned literal",
            "general literal",
            "null literal",
        ],
        kw("NULL"),
    ));
    expect(&trim_list(null), PORTABLE, Some("20.16 SR 1"));
}

#[test]
fn a_zero_path_count_is_the_checkers_and_repaired() {
    use gql_proof::tree::order_bounds;
    use rand::SeedableRng;
    let zero = d(
        "number of paths",
        vec![d("non-negative integer specification", vec![integer(&["0"])])],
    );
    let (automaton, _) = verdicts(&zero, PORTABLE);
    assert!(automaton);
    assert_eq!(reported(&zero), ["16.6 SR 2"]);
    let analysis = Analysis::new(&BASE, &StubProvider);
    for text in ["0", "0b0", "0x0"] {
        let nt = BASE.require("number of paths").unwrap();
        let mut tree = analysis.spell(nt, text).unwrap();
        let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(3);
        assert!(order_bounds(&BASE, &mut tree, &|nt, t| analysis.spell(nt, t), &mut rng));
        assert!(reported(&tree.export(&BASE)).is_empty(), "{}", tree.export(&BASE).text());
    }
}

/// Copies per definition in the refined grammar, the widest first:
/// `cargo test --release --test refine census -- --ignored --nocapture`.
#[test]
#[ignore]
fn census() {
    let refined = refine(&BASE, &all_rules(PORTABLE), BASE.require("GQL-program").unwrap()).unwrap();
    let mut prods: std::collections::BTreeMap<&str, (usize, usize)> = Default::default();
    for nt in &refined.cfg.nts {
        let e = prods.entry(nt.base.as_str()).or_default();
        e.0 += 1;
        e.1 += nt.prods.len();
    }
    let mut v: Vec<_> = prods.into_iter().collect();
    v.sort_by_key(|(_, (_, p))| std::cmp::Reverse(*p));
    eprintln!("{} nonterminals, {} productions", refined.cfg.nts.len(), refined.cfg.prods.len());
    for (b, (n, p)) in v.iter().take(25) {
        eprintln!("{p:>6} productions {n:>4} copies <{b}>");
    }
}

#[test]
#[ignore]
fn debug_field_names() {
    let refined = refine(&BASE, &all_rules(DIFFERENT), BASE.require("GQL-program").unwrap()).unwrap();
    let verifier = Verifier::new(Grammar::new(&ISO)).with_syntax_rules(DIFFERENT);
    for tree in generate(&refined.cfg, refined.start, 6551283619, 63) {
        let v = verifier.verify(&tree, &verifier.render(&tree));
        if v.iter().any(|v| v.rule == "18.10 SR 2") {
            let mut fts = Vec::new();
            fn find<'t>(n: &'t Plain, want: &str, out: &mut Vec<&'t Plain>) {
                if let Plain::Def { name, children, .. } = n {
                    if name == want { out.push(n); }
                    children.iter().for_each(|c| find(c, want, out));
                }
            }
            find(&tree, "field types specification", &mut fts);
            for f in fts { eprintln!("FTS {}", verifier.render(f)); }
            for x in &v { eprintln!("V {x}"); }
            break;
        }
    }
}
