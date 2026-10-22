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

const RULES: [&str; 13] = [
    "16.4 SR 14",
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
