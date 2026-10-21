//! Scoping compiled into the grammar (`scope`): every refined tree references only variables
//! in scope and declares only new names.

use gql_proof::cfg::Cfg;
use gql_proof::leaf::StubProvider;
use gql_proof::purdom::{Analysis, Config, Generator, Length};
use gql_proof::refine::{Rule, all_rules, refine};
use gql_proof::scope::{DEFAULT_NAMES, Scope};
use gql_proof::{ISO_BNF_XML, MatchModeDefault, bnf};
use std::sync::LazyLock;
use std::time::Instant;

static ISO: LazyLock<bnf::Bnf> = LazyLock::new(|| bnf::parse(ISO_BNF_XML).unwrap());
static BASE: LazyLock<Cfg> = LazyLock::new(|| Cfg::from_bnf(&ISO));

fn rules() -> Vec<Box<dyn Rule>> {
    let mut rules = all_rules(MatchModeDefault::Portable);
    rules.push(Box::new(Scope::new(&BASE, DEFAULT_NAMES)));
    rules
}

/// The automaton's verdict on a sentence, read with the ISO parser.
fn verdict(text: &str) -> Result<(), String> {
    use gql_proof::parse::Parser;
    use gql_proof::refine::accepts;
    use gql_proof::tokens::Grammar;
    use gql_proof::verify::Verifier;
    let tokens = Grammar::new(&ISO);
    let verifier = Verifier::new(Grammar::new(&ISO));
    let parser = Parser::new(&BASE, &tokens, "GQL-program").unwrap();
    let parsed = parser
        .parse(text, |n| {
            verifier
                .verify(&n.export(&BASE), &n.render(&BASE))
                .is_empty()
        })
        .unwrap_or_else(|e| panic!("{text:?}: {e}"));
    accepts(&rules(), &parsed.tree.export(&BASE))
}

#[test]
#[ignore]
fn show_tree() {
    use gql_proof::parse::Parser;
    use gql_proof::tokens::Grammar;
    use gql_proof::verify::Verifier;
    let text = std::env::var("GQL_TEXT").unwrap();
    let tokens = Grammar::new(&ISO);
    let verifier = Verifier::new(Grammar::new(&ISO));
    let parser = Parser::new(&BASE, &tokens, "GQL-program").unwrap();
    let parsed = parser
        .parse(&text, |n| {
            verifier
                .verify(&n.export(&BASE), &n.render(&BASE))
                .is_empty()
        })
        .unwrap();
    println!("{}", parsed.tree.display(&BASE, false));
}

#[test]
fn probes() {
    for ok in [
        "MATCH (x) RETURN x",
        "MATCH (x) RETURN count(*) AS y",
        "MATCH (x)-[y]->() RETURN x, y",
        "MATCH (x) CALL (x) { RETURN 1 AS y } RETURN y",
        "LET x = 1 RETURN x",
        "FOR x IN [1] RETURN x AS y",
        "MATCH (x) RETURN x AS y NEXT RETURN y",
        "RETURN 1 AS x UNION RETURN 2 AS x",
    ] {
        assert_eq!(verdict(ok), Ok(()), "{ok:?}");
    }
    for bad in [
        "RETURN x",
        "MATCH (x) LET x = 1 RETURN x",
        "MATCH (x)-[x]->() RETURN x",
        "MATCH (x) RETURN x.k",
        "MATCH (x) RETURN x NEXT RETURN y",
        "RETURN 1 AS x UNION RETURN 2 AS y",
        "FILTER count(*) > 0 RETURN 1 AS x",
    ] {
        assert!(verdict(bad).is_err(), "{bad:?} accepted");
    }
}

#[test]
#[ignore]
fn copies_per_definition() {
    use std::collections::BTreeMap;
    let start = BASE.require("GQL-program").unwrap();
    let names = std::env::var("GQL_NAMES").unwrap_or_else(|_| "x".into());
    let names: Vec<&str> = names.split(',').collect();
    let mut rules = all_rules(MatchModeDefault::Portable);
    if let Ok(claim) = std::env::var("GQL_CLAIM") {
        use gql_proof::features::{CONFORMANCE_JSON, Claim, ClaimRules, Conformance};
        let conformance = Conformance::load(CONFORMANCE_JSON).unwrap();
        let claim = Claim::parse(&claim, &conformance).unwrap();
        let forbidden = conformance.forbidden(&claim);
        rules.push(Box::new(
            ClaimRules::new(&BASE, start, &forbidden, &[]).unwrap(),
        ));
    }
    rules.push(Box::new(Scope::new(&BASE, &names)));
    let t = Instant::now();
    let refined = refine(&BASE, &rules, start).unwrap();
    println!(
        "{names:?}: refined in {:?}: {} nonterminals, {} productions",
        t.elapsed(),
        refined.cfg.nts.len(),
        refined.cfg.prods.len()
    );
    let mut copies: BTreeMap<&str, (Vec<&str>, usize)> = BTreeMap::new();
    for nt in &refined.cfg.nts {
        let e = copies.entry(&nt.base).or_default();
        e.0.push(&nt.name);
        e.1 += nt.prods.len();
    }
    let mut by: Vec<_> = copies.into_iter().collect();
    by.sort_by_key(|(_, v)| std::cmp::Reverse(v.1));
    for (base, (names, prods)) in by.iter().take(25) {
        println!("{prods:>8} productions {:>6} copies  {base}", names.len());
    }
    for name in by[0].1.0.iter().take(12) {
        println!("  {name}");
    }
}

/// Every tree of the grammar scoping refines passes the independent checker. Slow (a few
/// minutes, several GB), so opt in: `cargo test --release --test scope -- --ignored`.
#[test]
#[ignore]
fn refined_trees_pass_the_checker() {
    let start = BASE.require("GQL-program").unwrap();
    let t = Instant::now();
    let refined = refine(&BASE, &rules(), start).unwrap();
    println!(
        "refined in {:?}: {} nonterminals, {} productions (base {} / {})",
        t.elapsed(),
        refined.cfg.nts.len(),
        refined.cfg.prods.len(),
        BASE.nts.len(),
        BASE.prods.len()
    );
    let analysis = Analysis::new(&refined.cfg, &StubProvider);
    let height = analysis.reference_height(refined.start);
    for seed in 0..2 {
        let config = Config {
            seed,
            max_depth: height,
            length: Length::Reference,
        };
        let outcome = Generator::new(&analysis, config, StubProvider)
            .run(refined.start)
            .unwrap();
        for t in &outcome.trees {
            let violations = gql_proof::verify::scope::check(&t.root.export(&refined.cfg));
            assert!(
                violations.is_empty(),
                "{}: {violations:?}",
                t.root.render(&refined.cfg)
            );
        }
    }
}
