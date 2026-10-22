//! Shared by the context tests: per-target extraction against the emitted grammar.

#![allow(dead_code)]

use gql_proof::cfg::{Cfg, Lit, Sym};
use gql_proof::context::{Context, Options, accepts};
use gql_proof::coverage::Criteria;
use gql_proof::leaf::{LeafProvider, StubProvider};
use gql_proof::purdom::Analysis;
use std::collections::BTreeSet;

/// Per-target extraction covers exactly the productions and cdrc pairs the emitted grammar
/// can derive, outside the lexical layer and below spelled names, among productions the
/// leaf provider can fill: the same fixed point read two ways. Every extracted sentence
/// passes the scope checker (and the types checker, when `typed`) and the rule itself.
pub fn extraction_matches_emission<C: Context>(base: &Cfg, rule: &C, options: &Options, typed: bool) {
    let start = base.require("GQL-program").unwrap();
    let analyzed = gql_proof::context::analyze(base, rule, options).unwrap();
    let built = analyzed.emit(start, "x").unwrap();
    let lexical = |p: u32| base.nts[base.prods[p as usize].lhs as usize].lexical;
    // A spelled name is derived from its text in both paths, never chosen: pairs below one
    // are not something a sentence can cover either way.
    let spelled = |name: &str| matches!(name, "identifier" | "binding variable");
    // A production with a prose leaf the provider cannot fill, or a child no production
    // fills, is never generated either way.
    let mut fillable: Vec<bool> = base
        .prods
        .iter()
        .map(|prod| {
            prod.rhs.iter().all(|s| match s {
                Sym::Lit(l) => match &base.lits[*l as usize] {
                    Lit::Opaque(name) => StubProvider.supports(name),
                    _ => true,
                },
                Sym::Nt(_) => true,
            })
        })
        .collect();
    loop {
        let before = fillable.clone();
        for (p, prod) in base.prods.iter().enumerate() {
            if fillable[p]
                && prod.rhs.iter().any(|s| {
                    matches!(s, Sym::Nt(c) if base.nts[*c as usize].prods.iter().all(|&q| !fillable[q as usize]))
                })
            {
                fillable[p] = false;
            }
        }
        if fillable == before {
            break;
        }
    }
    let (mut e_prods, mut e_pairs) = (BTreeSet::new(), BTreeSet::new());
    for q in &built.cfg.prods {
        if lexical(q.unrefined) || !fillable[q.unrefined as usize] {
            continue;
        }
        e_prods.insert(q.unrefined);
        for (i, sym) in q.rhs.iter().enumerate() {
            let Sym::Nt(c) = sym else { continue };
            if spelled(built.cfg.base(*c)) {
                continue;
            }
            for &p in &built.cfg.nts[*c as usize].prods {
                let pp = &built.cfg.prods[p as usize];
                if !lexical(pp.unrefined) && fillable[pp.unrefined as usize] {
                    e_pairs.insert((q.occ[i], pp.unrefined));
                }
            }
        }
    }
    // The same from the extracted trees.
    let analysis = Analysis::new(base, &StubProvider);
    let names: Vec<String> = ["x", "y", "z", "w"].iter().map(|s| s.to_string()).collect();
    let template = |nt: u32| StubProvider.token(base.base(nt)).and_then(|t| analysis.spell(nt, t));
    let extractor = analyzed.extractor(start, &StubProvider);
    let covered = extractor.cover(
        Criteria {
            cdrc: true,
            k: 0,
            lexical: false,
        },
        &names,
        |nt, s| analysis.spell(nt, s),
        &template,
        &mut StubProvider,
        1,
        false,
    );
    let (mut x_prods, mut x_pairs) = (BTreeSet::new(), BTreeSet::new());
    fn walk(cfg: &Cfg, n: &gql_proof::tree::Node, prods: &mut BTreeSet<u32>, pairs: &mut BTreeSet<(u32, u32)>) {
        let Some(p) = n.prod else { return };
        let lexical = |p: u32| cfg.nts[cfg.prods[p as usize].lhs as usize].lexical;
        if lexical(p) {
            return;
        }
        prods.insert(p);
        let prod = &cfg.prods[p as usize];
        for (i, c) in n.children.iter().enumerate() {
            let spelled = matches!(c.sym, Sym::Nt(nt) if matches!(cfg.base(nt), "identifier" | "binding variable"));
            if let Some(cp) = c.prod
                && !lexical(cp)
                && !spelled
            {
                pairs.insert((prod.occ[i], cp));
            }
            walk(cfg, c, prods, pairs);
        }
    }
    let mut bad = 0;
    for (root, _) in &covered.trees {
        walk(base, root, &mut x_prods, &mut x_pairs);
        let plain = root.export(base);
        let mut violations = gql_proof::verify::scope::check(&plain);
        if typed {
            violations.extend(gql_proof::verify::types::check(&plain));
        }
        let rule_says = accepts(rule, &plain);
        if !violations.is_empty() || rule_says.is_err() {
            bad += 1;
            if bad <= 5 {
                eprintln!(
                    "{}\n  checkers: {violations:?}\n  rule: {rule_says:?}",
                    root.render(base)
                );
            }
        }
    }
    eprintln!(
        "emission {} productions, {} pairs; extraction {} trees, {} productions, {} pairs; {bad} bad trees",
        e_prods.len(),
        e_pairs.len(),
        covered.trees.len(),
        x_prods.len(),
        x_pairs.len()
    );
    for p in e_prods.difference(&x_prods).take(10) {
        eprintln!("  only emission: {}", gql_proof::describe(base, *p));
    }
    for p in x_prods.difference(&e_prods).take(10) {
        eprintln!("  only extraction: {}", gql_proof::describe(base, *p));
    }
    for (o, p) in e_pairs.difference(&x_pairs).take(10) {
        eprintln!("  pair only emission: occ {o} {}", gql_proof::describe(base, *p));
    }
    for (o, p) in x_pairs.difference(&e_pairs).take(10) {
        eprintln!("  pair only extraction: occ {o} {}", gql_proof::describe(base, *p));
    }
    assert_eq!(e_prods, x_prods);
    assert_eq!(e_pairs, x_pairs);
    assert_eq!(bad, 0);
}
