//! CDRC and k-path coverage: target counts by hand on Xu, Zheng & Chen's sample grammar,
//! observation on a hand-built tree, minimal realizations against brute force, and the
//! iso grammar under the verifier.

use gql_proof::bnf;
use gql_proof::cfg::{Cfg, Lit, Sym};
use gql_proof::coverage::{Criteria, Target, observe, targets};
use gql_proof::leaf::StubProvider;
use gql_proof::purdom::{Analysis, Config, Generator, Length, Outcome, size};
use gql_proof::refine::{all_rules, refine};
use gql_proof::tokens::Grammar;
use gql_proof::tree::Node;
use gql_proof::verify::Verifier;
use gql_proof::{ISO_BNF_XML, MatchModeDefault, describe};
use proptest::prelude::*;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::LazyLock;

/// `S -> E`, `E -> E + T | T`, `T -> T * F | F`, `F -> id | ( E )`.
const XU: &str = r#"<grammar>
<BNFdef name="S"><rhs><BNF name="E"/></rhs></BNFdef>
<BNFdef name="E"><rhs><alt><BNF name="E"/><terminalsymbol>+</terminalsymbol><BNF name="T"/></alt><alt><BNF name="T"/></alt></rhs></BNFdef>
<BNFdef name="T"><rhs><alt><BNF name="T"/><terminalsymbol>*</terminalsymbol><BNF name="F"/></alt><alt><BNF name="F"/></alt></rhs></BNFdef>
<BNFdef name="F"><rhs><alt><kw>id</kw></alt><alt><terminalsymbol>(</terminalsymbol><BNF name="E"/><terminalsymbol>)</terminalsymbol></alt></rhs></BNFdef>
</grammar>"#;

static XU_CFG: LazyLock<Cfg> = LazyLock::new(|| Cfg::from_bnf(&bnf::parse(XU).unwrap()));

fn counts(set: &BTreeSet<Target>) -> BTreeMap<String, usize> {
    let mut out = BTreeMap::new();
    for t in set {
        let k = match t {
            Target::Cdrc(..) => "cdrc".to_string(),
            Target::Path(p) => format!("{}-path", p.len()),
        };
        *out.entry(k).or_default() += 1;
    }
    out
}

fn criteria(cdrc: bool, k: u32) -> Criteria {
    Criteria {
        cdrc,
        k,
        lexical: false,
    }
}

#[test]
fn xu_targets_counted_by_hand() {
    let start = XU_CFG.require("S").unwrap();
    let got = counts(&targets(&XU_CFG, start, criteria(true, 3)));
    // CDRC: E occurs 3 times, T 3, F 2, each with 2 productions, plus S's production at the
    // root: 6 + 6 + 4 + 1.
    // k-paths: 13 symbol occurrences; E's 3 occurrences each point at E's 4 (E, +, T, T), T's 3
    // at T's 4, F's 2 at F's 4: 12 + 12 + 8 = 32; one more step gives 80.
    let want: BTreeMap<String, usize> =
        [("cdrc", 17), ("1-path", 13), ("2-path", 32), ("3-path", 80)]
            .into_iter()
            .map(|(k, n)| (k.to_string(), n))
            .collect();
    assert_eq!(got, want);
}

/// A node built by the description of its production; literal positions fill themselves.
fn node(cfg: &Cfg, production: &str, mut nts: Vec<Node>) -> Node {
    let p = (0..cfg.prods.len() as u32)
        .find(|&p| describe(cfg, p) == production)
        .unwrap_or_else(|| panic!("no production {production}"));
    let prod = cfg.prod(p);
    nts.reverse();
    let children = prod
        .rhs
        .iter()
        .map(|&sym| match sym {
            Sym::Nt(_) => nts.pop().unwrap(),
            Sym::Lit(l) => {
                let text = match &cfg.lits[l as usize] {
                    Lit::Kw(t) | Lit::Term(t) | Lit::Opaque(t) => t.clone(),
                };
                Node {
                    sym,
                    prod: None,
                    text: Some(text),
                    children: Vec::new(),
                }
            }
        })
        .collect();
    Node {
        sym: Sym::Nt(prod.lhs),
        prod: Some(p),
        text: None,
        children,
    }
}

#[test]
fn observe_id_plus_id() {
    let c = &*XU_CFG;
    let id = || node(c, "<F> ::= id", vec![]);
    let t = |f| node(c, "<T> ::= <F>", vec![f]);
    let tree = node(
        c,
        "<S> ::= <E>",
        vec![node(
            c,
            r#"<E> ::= <E> "+" <T>"#,
            vec![node(c, "<E> ::= <T>", vec![t(id())]), t(id())],
        )],
    );
    // Occurrences on the tree: E (in S), E and + and T (in E + T), T (in E -> T), F (in T -> F),
    // id. Chains, by hand: 7 single occurrences, 7 pairs, 5 triples.
    let got = counts(&observe(c, &tree, criteria(false, 3)));
    let want: BTreeMap<String, usize> = [("1-path", 7), ("2-path", 7), ("3-path", 5)]
        .into_iter()
        .map(|(k, n)| (k.to_string(), n))
        .collect();
    assert_eq!(got, want);
    // CDRC pairs: S's production at the root, E -> E + T at E in S, E -> T at E in E + T,
    // T -> F at T in E + T and at T in E -> T, F -> id at F in T -> F (one occurrence, seen
    // twice): 6.
    assert_eq!(counts(&observe(c, &tree, criteria(true, 0)))["cdrc"], 6);
}

/// Every tree from `nt` of at most `size` nodes and `height` levels.
fn all_trees(cfg: &Cfg, nt: u32, height: u32, budget: u32) -> Vec<Node> {
    if height == 0 {
        return Vec::new();
    }
    let mut out = Vec::new();
    for &p in &cfg.nts[nt as usize].prods {
        let prod = cfg.prod(p);
        let mut partial: Vec<(Vec<Node>, u32)> = vec![(Vec::new(), 1)];
        for &sym in &prod.rhs {
            let mut next = Vec::new();
            for (kids, used) in partial {
                match sym {
                    Sym::Lit(l) => {
                        if used < budget {
                            let text = match &cfg.lits[l as usize] {
                                Lit::Kw(t) | Lit::Term(t) | Lit::Opaque(t) => t.clone(),
                            };
                            let mut k = kids.clone();
                            k.push(Node {
                                sym,
                                prod: None,
                                text: Some(text),
                                children: Vec::new(),
                            });
                            next.push((k, used + 1));
                        }
                    }
                    Sym::Nt(c) => {
                        for sub in all_trees(cfg, c, height - 1, budget - used) {
                            let n = size(cfg, &sub);
                            if used + n <= budget {
                                let mut k = kids.clone();
                                k.push(sub);
                                next.push((k, used + n));
                            }
                        }
                    }
                }
            }
            partial = next;
        }
        for (children, _) in partial {
            out.push(Node {
                sym: Sym::Nt(nt),
                prod: Some(p),
                text: None,
                children,
            });
        }
    }
    out
}

#[test]
fn realizations_are_shortest() {
    let cfg = &*XU_CFG;
    let start = cfg.require("S").unwrap();
    let (height, budget) = (7, 16);
    let c = criteria(true, 3);
    // The shortest tree containing each target, by brute force.
    let mut best: BTreeMap<Target, u32> = BTreeMap::new();
    for tree in all_trees(cfg, start, height, budget) {
        let n = size(cfg, &tree);
        for t in observe(cfg, &tree, c) {
            let slot = best.entry(t).or_insert(u32::MAX);
            *slot = (*slot).min(n);
        }
    }
    let analysis = Analysis::new(cfg, &StubProvider);
    let config = Config {
        seed: 0,
        max_depth: height,
        length: Length::Unbounded,
    };
    let generator = Generator::new(&analysis, config, StubProvider);
    for t in targets(cfg, start, c) {
        let realized = generator.shortest_containing(start, &t);
        match best.get(&t) {
            Some(&n) => assert_eq!(realized, Some(n), "{t:?}"),
            // Not within the brute-force budget: the search must agree it is longer.
            None => assert!(realized.is_none_or(|r| r > budget), "{t:?}: {realized:?}"),
        }
    }
}

fn run(cfg: &Cfg, start: u32, base: &Cfg, seed: u64, depth: u32, c: Criteria) -> Outcome {
    let analysis = Analysis::new(cfg, &StubProvider);
    let config = Config {
        seed,
        max_depth: depth,
        length: Length::Reference,
    };
    Generator::new(&analysis, config, StubProvider)
        .run_with(start, base, c)
        .unwrap()
}

#[test]
fn xu_fully_covered() {
    let start = XU_CFG.require("S").unwrap();
    let outcome = run(&XU_CFG, start, &XU_CFG, 0, 9, criteria(true, 3));
    for report in &outcome.targets {
        assert_eq!(
            report.covered, report.total,
            "{}: {:?}",
            report.kind, report.uncovered
        );
    }
    let found: BTreeSet<Target> = outcome
        .trees
        .iter()
        .flat_map(|t| observe(&XU_CFG, &t.root, criteria(true, 3)))
        .collect();
    assert_eq!(found, targets(&XU_CFG, start, criteria(true, 3)));
}

static ISO: LazyLock<bnf::Bnf> = LazyLock::new(|| bnf::parse(ISO_BNF_XML).unwrap());
static BASE: LazyLock<Cfg> = LazyLock::new(|| Cfg::from_bnf(&ISO));

proptest! {
    #![proptest_config(ProptestConfig::with_cases(6))]

    #[test]
    fn iso_targeted_trees_verify(seed in any::<u64>(), depth in 46u32..=60) {
        let id086 = MatchModeDefault::Portable;
        let refined = refine(&BASE, &all_rules(id086), BASE.require("GQL-program").unwrap()).unwrap();
        let c = criteria(true, 3);
        let outcome = run(&refined.cfg, refined.start, &BASE, seed, depth, c);
        let verifier = Verifier::new(Grammar::new(&ISO)).with_syntax_rules(id086);
        let all = targets(&BASE, BASE.require("GQL-program").unwrap(), c);
        let mut seen = BTreeSet::new();
        for t in &outcome.trees {
            let plain = t.root.export(&refined.cfg);
            let violations = verifier.verify(&plain, &t.root.render(&refined.cfg));
            prop_assert!(violations.is_empty(), "{:?}", violations);
            // A settled tree grew after the search, by the digits the bound repair added.
            prop_assert!(
                t.root.height() <= depth || t.settled,
                "height {} above the cap {depth}",
                t.root.height()
            );
            seen.extend(observe(&refined.cfg, &t.root, c));
        }
        prop_assert!(seen.is_subset(&all), "observed targets the enumeration does not know");
        for report in &outcome.targets {
            prop_assert_eq!(report.covered + report.uncovered.len(), report.total, "{}", report.kind);
        }
    }
}
