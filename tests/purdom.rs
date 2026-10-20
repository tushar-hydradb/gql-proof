use gql_proof::bnf::{self, Ebnf};
use gql_proof::cfg::Cfg;
use gql_proof::leaf::StubProvider;
use gql_proof::purdom::{Config, Generator, Outcome, Reason};
use gql_proof::tokens::Grammar;
use gql_proof::verify::Verifier;
use gql_proof::{ISO_BNF_XML, describe};
use proptest::prelude::*;
use std::sync::LazyLock;

static ISO_BNF: LazyLock<bnf::Bnf> = LazyLock::new(|| bnf::parse(ISO_BNF_XML).unwrap());
static ISO: LazyLock<Cfg> = LazyLock::new(|| Cfg::from_bnf(&ISO_BNF));

fn run(cfg: &Cfg, start: &str, seed: u64, max_depth: u32, max_new: Option<usize>) -> Outcome {
    let config = Config {
        seed,
        max_depth,
        max_new_per_tree: max_new,
    };
    Generator::new(cfg, config, StubProvider)
        .run(cfg.require(start).unwrap())
        .unwrap()
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
    let outcome = run(&cfg, "s", 0, 10, None);
    assert_eq!(outcome.covered.count_ones(..), cfg.prods.len());
    assert!(outcome.uncovered.is_empty());
    for t in &outcome.trees {
        t.root.validate(&cfg).unwrap();
    }
}

#[test]
fn same_seed_same_trees() {
    let a = run(&ISO, "GQL-program", 42, 50, None);
    let b = run(&ISO, "GQL-program", 42, 50, None);
    assert_eq!(sentences(&a, &ISO), sentences(&b, &ISO));
}

#[test]
fn different_seeds_same_coverage() {
    let a = run(&ISO, "GQL-program", 1, 50, None);
    let b = run(&ISO, "GQL-program", 2, 50, None);
    assert_ne!(sentences(&a, &ISO), sentences(&b, &ISO));
    assert_eq!(a.covered, b.covered);
}

#[test]
fn depth_cap_reports_what_does_not_fit() {
    // <s> needs height 5 to reach `z`: s -> t -> u -> v -> z.
    let cfg = toy(r#"
        <BNFdef name="s"><rhs><alt><kw>a</kw></alt><alt><BNF name="t"/></alt></rhs></BNFdef>
        <BNFdef name="t"><rhs><BNF name="u"/></rhs></BNFdef>
        <BNFdef name="u"><rhs><BNF name="v"/></rhs></BNFdef>
        <BNFdef name="v"><rhs><kw>z</kw></rhs></BNFdef>
        <BNFdef name="orphan"><rhs><kw>o</kw></rhs></BNFdef>"#);
    let outcome = run(&cfg, "s", 0, 3, None);
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
    assert_eq!(run(&cfg, "s", 0, 4, None).uncovered.len(), 1);
}

#[test]
fn max_new_per_tree_gives_more_smaller_trees() {
    let all = run(&ISO, "GQL-program", 1, 50, None);
    let capped = run(&ISO, "GQL-program", 1, 50, Some(5));
    assert!(capped.trees.len() > all.trees.len());
    assert_eq!(capped.covered, all.covered);
}

#[test]
fn snapshot_seed_1() {
    let outcome = run(&ISO, "GQL-program", 1, 50, Some(20));
    insta::assert_snapshot!(sentences(&outcome, &ISO).join("\n"));
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(16))]

    #[test]
    fn trees_are_valid_and_accounted_for(
        seed in any::<u64>(),
        max_depth in 20u32..=60,
        max_new in proptest::option::of(1usize..50),
    ) {
        let cfg = &*ISO;
        let verifier = Verifier::new(Grammar::new(&ISO_BNF));
        let outcome = run(cfg, "GQL-program", seed, max_depth, max_new);
        for t in &outcome.trees {
            prop_assert!(t.root.validate(cfg).is_ok());
            let violations = verifier.verify(&t.root.export(cfg), &t.root.render(cfg));
            prop_assert!(violations.is_empty(), "{:?}", violations);
            prop_assert!(t.root.height() <= max_depth);
            prop_assert!(t.new > 0);
        }
        prop_assert_eq!(outcome.covered.count_ones(..) + outcome.uncovered.len(), cfg.prods.len());
        for &(_, reason) in &outcome.uncovered {
            if let Reason::NeedsDepth(d) = reason {
                prop_assert!(d > max_depth);
            }
        }
    }
}
