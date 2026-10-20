use gql_proof::bnf::{self, Ebnf};
use gql_proof::cfg::Cfg;
use gql_proof::leaf::StubProvider;
use gql_proof::purdom::{Analysis, Config, Generator, Length, Outcome, Reason};
use gql_proof::tokens::Grammar;
use gql_proof::verify::Verifier;
use gql_proof::{ISO_BNF_XML, describe};
use proptest::prelude::*;
use std::sync::LazyLock;

static ISO_BNF: LazyLock<bnf::Bnf> = LazyLock::new(|| bnf::parse(ISO_BNF_XML).unwrap());
static ISO: LazyLock<Cfg> = LazyLock::new(|| Cfg::from_bnf(&ISO_BNF));

fn run(cfg: &Cfg, start: &str, seed: u64, max_depth: u32, length: Length) -> Outcome {
    let analysis = Analysis::new(cfg, &StubProvider);
    let config = Config {
        seed,
        max_depth,
        length,
    };
    Generator::new(&analysis, config, StubProvider)
        .run(cfg.require(start).unwrap())
        .unwrap()
}

/// Shortest covering sentence per production, keyed by its description.
fn covering(cfg: &Cfg, start: &str, max_depth: u32) -> Vec<(String, Option<u32>)> {
    let analysis = Analysis::new(cfg, &StubProvider);
    let config = Config {
        seed: 0,
        max_depth,
        length: Length::Unbounded,
    };
    let generator = Generator::new(&analysis, config, StubProvider);
    let lens = generator.covering_lengths(cfg.require(start).unwrap());
    (0..cfg.prods.len() as u32)
        .map(|p| (describe(cfg, p), lens[p as usize]))
        .collect()
}

fn toy(defs: &str) -> Cfg {
    Cfg::from_bnf(&bnf::parse(&format!("<grammar>{defs}</grammar>")).unwrap())
}

fn sentences(outcome: &Outcome, cfg: &Cfg) -> Vec<String> {
    outcome.trees.iter().map(|t| t.root.render(cfg)).collect()
}

/// `<s> ::= a [ b ] { c | d }... | <s> + <s>`
const ARITH: &str = r#"
<BNFdef name="s"><rhs>
  <alt><kw>a</kw><opt><kw>b</kw></opt><group><alt><kw>c</kw></alt><alt><kw>d</kw></alt></group><repeat/></alt>
  <alt><BNF name="s"/><terminalsymbol unicode="002B">+</terminalsymbol><BNF name="s"/></alt>
</rhs></BNFdef>"#;

/// The sample grammar of Xu, Zheng & Chen, "A Toolkit for Generating Sentences from
/// Context-Free Grammars": `S -> E`, `E -> E + T | T`, `T -> T * F | F`, `F -> id | ( E )`.
const XU: &str = r#"
<BNFdef name="S"><rhs><BNF name="E"/></rhs></BNFdef>
<BNFdef name="E"><rhs><alt><BNF name="E"/><terminalsymbol>+</terminalsymbol><BNF name="T"/></alt><alt><BNF name="T"/></alt></rhs></BNFdef>
<BNFdef name="T"><rhs><alt><BNF name="T"/><terminalsymbol>*</terminalsymbol><BNF name="F"/></alt><alt><BNF name="F"/></alt></rhs></BNFdef>
<BNFdef name="F"><rhs><alt><kw>id</kw></alt><alt><terminalsymbol>(</terminalsymbol><BNF name="E"/><terminalsymbol>)</terminalsymbol></alt></rhs></BNFdef>"#;

#[test]
fn iso_grammar_parses_completely() {
    let bnf = bnf::parse(ISO_BNF_XML).unwrap();
    assert_eq!(bnf.defs.len(), 814);
    let mut opaque = 0;
    fn count(e: &Ebnf, n: &mut usize) {
        match e {
            Ebnf::Seq(items) | Ebnf::Alt(items) => items.iter().for_each(|i| count(i, n)),
            Ebnf::Opt(inner) | Ebnf::Repeat(inner) => count(inner, n),
            Ebnf::Opaque(_) => *n += 1,
            _ => {}
        }
    }
    bnf.defs.iter().for_each(|d| count(&d.rhs, &mut opaque));
    // 23 `seeTheRules` in the xml: 16 whole definitions in prose, 7 annotations on real
    // content such as `<double single quote> ::= <quote> <quote> !! See the Syntax Rules`.
    assert_eq!(opaque, 16);
    assert_eq!(bnf.defs.iter().filter(|d| d.see_rules).count(), 7);
    let double_single_quote = &bnf.get("double single quote").unwrap().rhs;
    assert_eq!(
        *double_single_quote,
        Ebnf::Seq(vec![Ebnf::Ref("quote".into()), Ebnf::Ref("quote".into())])
    );
}

#[test]
fn dangling_reference_is_an_error() {
    let err =
        bnf::parse(r#"<grammar><BNFdef name="s"><rhs><BNF name="t"/></rhs></BNFdef></grammar>"#)
            .unwrap_err();
    assert!(err.to_string().contains("<t> in <s>"), "{err}");
}

#[test]
fn desugars_opt_group_and_repeat() {
    let cfg = toy(ARITH);
    let prods: Vec<String> = (0..cfg.prods.len() as u32)
        .map(|p| describe(&cfg, p))
        .collect();
    assert_eq!(
        prods,
        [
            "<s/opt1> ::= b",
            "<s/opt1> ::= ε",
            "<s/alt3> ::= c",
            "<s/alt3> ::= d",
            "<s/rep2> ::= <s/alt3>",
            "<s/rep2> ::= <s/alt3> <s/rep2>",
            "<s> ::= a <s/opt1> <s/rep2>",
            r#"<s> ::= <s> "+" <s>"#,
        ]
    );
}

#[test]
fn covers_every_production_of_a_toy_grammar() {
    let cfg = toy(ARITH);
    let outcome = run(&cfg, "s", 0, 10, Length::Reference);
    assert_eq!(outcome.covered.count_ones(..), cfg.prods.len());
    assert!(outcome.uncovered.is_empty());
    for t in &outcome.trees {
        t.root.validate(&cfg).unwrap();
    }
}

#[test]
fn same_seed_same_trees() {
    let a = run(&ISO, "GQL-program", 42, 46, Length::Reference);
    let b = run(&ISO, "GQL-program", 42, 46, Length::Reference);
    assert_eq!(sentences(&a, &ISO), sentences(&b, &ISO));
}

#[test]
fn different_seeds_same_coverage() {
    let a = run(&ISO, "GQL-program", 1, 46, Length::Reference);
    let b = run(&ISO, "GQL-program", 2, 46, Length::Reference);
    assert_ne!(sentences(&a, &ISO), sentences(&b, &ISO));
    assert_eq!(a.covered, b.covered);
}

#[test]
fn depth_cap_reports_what_does_not_fit() {
    // <s> needs height 4 to reach `z`: s -> t -> u -> v -> z.
    let cfg = toy(r#"
        <BNFdef name="s"><rhs><alt><kw>a</kw></alt><alt><BNF name="t"/></alt></rhs></BNFdef>
        <BNFdef name="t"><rhs><BNF name="u"/></rhs></BNFdef>
        <BNFdef name="u"><rhs><BNF name="v"/></rhs></BNFdef>
        <BNFdef name="v"><rhs><kw>z</kw></rhs></BNFdef>
        <BNFdef name="orphan"><rhs><kw>o</kw></rhs></BNFdef>"#);
    let outcome = run(&cfg, "s", 0, 3, Length::Reference);
    let reasons: Vec<(String, Reason)> = outcome
        .uncovered
        .iter()
        .map(|&(p, r)| (describe(&cfg, p), r))
        .collect();
    assert_eq!(
        reasons,
        [
            ("<s> ::= <t>".to_string(), Reason::NeedsDepth(4)),
            ("<t> ::= <u>".to_string(), Reason::NeedsDepth(4)),
            ("<u> ::= <v>".to_string(), Reason::NeedsDepth(4)),
            ("<v> ::= z".to_string(), Reason::NeedsDepth(4)),
            ("<orphan> ::= o".to_string(), Reason::Unreachable),
        ]
    );
    assert_eq!(run(&cfg, "s", 0, 4, Length::Reference).uncovered.len(), 1);
    let analysis = Analysis::new(&cfg, &StubProvider);
    assert_eq!(analysis.reference_height(cfg.require("s").unwrap()), 4);
}

#[test]
fn xu_sample_lengths_match_the_paper() {
    let cfg = toy(XU);
    let analysis = Analysis::new(&cfg, &StubProvider);
    // F -> ( E ) sits under S, E and T and needs E -> T -> F -> id inside: height 7.
    assert_eq!(analysis.reference_height(cfg.require("S").unwrap()), 7);
    // Shortest covering sentences, counted by hand in nodes. The paper's example 2 gives
    // `id + id` as length 10.
    let expected = [
        ("<S> ::= <E>", 5),             // id
        (r#"<E> ::= <E> "+" <T>"#, 10), // id + id
        ("<E> ::= <T>", 5),             // id
        (r#"<T> ::= <T> "*" <F>"#, 9),  // id * id
        ("<T> ::= <F>", 5),             // id
        ("<F> ::= id", 5),              // id
        (r#"<F> ::= "(" <E> ")""#, 10), // ( id )
    ];
    let mut got = covering(&cfg, "S", 7);
    got.sort();
    let mut want: Vec<(String, Option<u32>)> = expected
        .iter()
        .map(|(d, l)| (d.to_string(), Some(*l)))
        .collect();
    want.sort();
    assert_eq!(got, want);

    let outcome = run(&cfg, "S", 0, 7, Length::Reference);
    assert_eq!(outcome.reference_length, 10);
    assert!(outcome.uncovered.is_empty());
    for t in &outcome.trees {
        assert!(
            t.length <= 10,
            "{} has length {}",
            t.root.render(&cfg),
            t.length
        );
    }
    let unbounded = run(&cfg, "S", 0, 7, Length::Unbounded);
    assert!(unbounded.uncovered.is_empty());
    assert!(unbounded.trees.len() <= outcome.trees.len());
}

#[test]
fn need_depth_matches_brute_force() {
    for (grammar, start) in [(XU, "S"), (ARITH, "s")] {
        let cfg = toy(grammar);
        let analysis = Analysis::new(&cfg, &StubProvider);
        let start_nt = cfg.require(start).unwrap();
        let need = analysis.need_depths(start_nt);
        let floor = analysis.min_height(start_nt);
        for (p, &want) in need.iter().enumerate() {
            let brute = (floor..=20).find(|&d| {
                run(&cfg, start, 0, d, Length::Unbounded)
                    .covered
                    .contains(p)
            });
            assert_eq!(want, brute, "{}", describe(&cfg, p as u32));
        }
    }
}

#[test]
fn length_modes_trade_count_for_size() {
    let unbounded = run(&ISO, "GQL-program", 1, 46, Length::Unbounded);
    let reference = run(&ISO, "GQL-program", 1, 46, Length::Reference);
    let tight = run(&ISO, "GQL-program", 1, 46, Length::Cap(60));
    assert!(unbounded.trees.len() < reference.trees.len());
    assert!(reference.trees.len() < tight.trees.len());
    assert_eq!(unbounded.covered, reference.covered);
    let max = |o: &Outcome| o.trees.iter().map(|t| t.length).max().unwrap();
    assert!(max(&reference) <= reference.reference_length);
    assert!(max(&tight) <= 60);
    assert!(
        tight
            .uncovered
            .iter()
            .any(|(_, r)| matches!(r, Reason::NeedsLength(_)))
    );
}

#[test]
fn iso_reference_height() {
    let analysis = Analysis::new(&ISO, &StubProvider);
    assert_eq!(
        analysis.reference_height(ISO.require("GQL-program").unwrap()),
        46
    );
}

#[test]
fn snapshot_seed_1() {
    let outcome = run(&ISO, "GQL-program", 1, 46, Length::Cap(60));
    insta::assert_snapshot!(sentences(&outcome, &ISO).join("\n"));
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(16))]

    #[test]
    fn trees_are_valid_and_accounted_for(
        seed in any::<u64>(),
        max_depth in 20u32..=60,
        length in prop_oneof![
            Just(Length::Unbounded),
            Just(Length::Reference),
            (30u32..200).prop_map(Length::Cap),
        ],
    ) {
        let cfg = &*ISO;
        let verifier = Verifier::new(Grammar::new(&ISO_BNF));
        let outcome = run(cfg, "GQL-program", seed, max_depth, length);
        for t in &outcome.trees {
            prop_assert!(t.root.validate(cfg).is_ok());
            let violations = verifier.verify(&t.root.export(cfg), &t.root.render(cfg));
            prop_assert!(violations.is_empty(), "{:?}", violations);
            prop_assert!(t.root.height() <= max_depth);
            prop_assert!(t.new > 0);
            if let Some(cap) = outcome.length_cap {
                prop_assert!(t.length <= cap, "length {} over cap {}", t.length, cap);
            }
        }
        prop_assert_eq!(outcome.covered.count_ones(..) + outcome.uncovered.len(), cfg.prods.len());
        for &(_, reason) in &outcome.uncovered {
            match reason {
                Reason::NeedsDepth(d) => prop_assert!(d > max_depth),
                Reason::NeedsLength(l) => prop_assert!(outcome.length_cap.is_some_and(|c| l > c)),
                _ => {}
            }
        }
    }
}
