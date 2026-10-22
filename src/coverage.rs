//! Coverage criteria beyond Purdom's: context-dependent rule coverage (Lämmel, "Grammar
//! Testing", FASE 2001) and k-path coverage (Havrikov, Kampmann & Zeller, "From Input
//! Coverage to Code Coverage", TOSEM 2022).
//!
//! Both are defined over occurrences: positions on right hand sides, so the same symbol in two
//! places is two things to cover.
//!
//! - A CDRC target is a production of X used at one occurrence of X. Empty alternatives count,
//!   so every optional is seen absent in every context.
//! - A k-path is a chain of k symbolic occurrences (references to ISO definitions and literals)
//!   along a root path of a derivation tree, desugaring groups skipped: Havrikov's grammar graph,
//!   whose alternation and quantifier nodes are our groups. Empty alternatives have no symbols,
//!   so k-paths never cover them; CDRC and Purdom do.
//!
//! Targets are enumerated on the unrefined grammar, so their number does not depend on which
//! syntax rules are compiled in; a refined tree reports the same occurrences and the unrefined
//! production of each node. Token-level definitions are leaves unless `lexical` is set: their
//! insides are prose stubs, so covering them says little.

use crate::cfg::{Cfg, Lit, NtId, OccId, ProdId, Sym};
use crate::tree::Node;
use std::collections::BTreeSet;

/// The occurrence of the root, which sits on no right hand side.
pub const ROOT: OccId = OccId::MAX;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Target {
    /// Production (unrefined) used at an occurrence.
    Cdrc(OccId, ProdId),
    /// Symbolic occurrences, root side first.
    Path(Vec<OccId>),
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Criteria {
    pub cdrc: bool,
    /// Cover every j-path for j up to this; 0 for none.
    pub k: u32,
    /// Descend into token-level definitions.
    pub lexical: bool,
}

impl Criteria {
    pub fn any(&self) -> bool {
        self.cdrc || self.k > 0
    }
}

/// Whether coverage looks inside `nt`.
fn descends(cfg: &Cfg, nt: NtId, c: Criteria) -> bool {
    c.lexical || !cfg.nts[nt as usize].lexical
}

/// Every target of the enabled criteria reachable from `start` in `cfg`.
pub fn targets(cfg: &Cfg, start: NtId, c: Criteria) -> BTreeSet<Target> {
    let mut out = BTreeSet::new();
    if c.cdrc {
        for &p in &cfg.nts[start as usize].prods {
            out.insert(Target::Cdrc(ROOT, p));
        }
        for nt in visited(cfg, start, c) {
            for &q in &cfg.nts[nt as usize].prods {
                let prod = &cfg.prods[q as usize];
                for (&sym, &occ) in prod.rhs.iter().zip(&prod.occ) {
                    if let Sym::Nt(x) = sym {
                        for &p in &cfg.nts[x as usize].prods {
                            out.insert(Target::Cdrc(occ, p));
                        }
                    }
                }
            }
        }
    }
    if c.k > 0 {
        let graph = Graph::new(cfg, c);
        let mut paths = Vec::new();
        for &first in &graph.reachable(start) {
            graph.extend(&mut vec![first], c.k, &mut paths);
        }
        out.extend(paths.into_iter().map(Target::Path));
    }
    out
}

/// Nonterminals coverage visits from `start`.
fn visited(cfg: &Cfg, start: NtId, c: Criteria) -> Vec<NtId> {
    let mut seen = vec![false; cfg.nts.len()];
    let mut stack = vec![start];
    let mut out = Vec::new();
    while let Some(nt) = stack.pop() {
        if std::mem::replace(&mut seen[nt as usize], true) || !descends(cfg, nt, c) {
            continue;
        }
        out.push(nt);
        for &p in &cfg.nts[nt as usize].prods {
            for sym in &cfg.prods[p as usize].rhs {
                if let Sym::Nt(child) = sym {
                    stack.push(*child);
                }
            }
        }
    }
    out
}

/// Havrikov's grammar graph on symbolic occurrences.
struct Graph {
    /// The symbolic occurrences directly below each nonterminal, groups seen through.
    below: Vec<Vec<OccId>>,
    /// The nonterminal an occurrence references, if it references one coverage enters.
    enters: Vec<Option<NtId>>,
}

impl Graph {
    fn new(cfg: &Cfg, c: Criteria) -> Self {
        let mut enters = vec![None; cfg.occs.len()];
        for prod in &cfg.prods {
            for (&sym, &occ) in prod.rhs.iter().zip(&prod.occ) {
                if let Sym::Nt(x) = sym
                    && descends(cfg, x, c)
                {
                    enters[occ as usize] = Some(x);
                }
            }
        }
        let below = (0..cfg.nts.len() as NtId)
            .map(|nt| {
                let mut out = BTreeSet::new();
                let mut seen = BTreeSet::new();
                symbolic_below(cfg, nt, &mut seen, &mut out);
                out.into_iter().collect()
            })
            .collect();
        Graph { below, enters }
    }

    /// Every symbolic occurrence on some root path from `start`.
    fn reachable(&self, start: NtId) -> BTreeSet<OccId> {
        let mut seen = BTreeSet::new();
        let mut stack: Vec<OccId> = self.below[start as usize].clone();
        while let Some(occ) = stack.pop() {
            if seen.insert(occ) {
                stack.extend_from_slice(self.children(occ));
            }
        }
        seen
    }

    /// Records `path` and every extension of it up to `k` occurrences.
    fn extend(&self, path: &mut Vec<OccId>, k: u32, out: &mut Vec<Vec<OccId>>) {
        out.push(path.clone());
        if path.len() as u32 == k {
            return;
        }
        let last = *path.last().unwrap();
        for &child in self.children(last) {
            path.push(child);
            self.extend(path, k, out);
            path.pop();
        }
    }

    /// Below a reference: the symbolic occurrences of what it references. Literals have none.
    fn children(&self, occ: OccId) -> &[OccId] {
        match self.enters[occ as usize] {
            Some(nt) => &self.below[nt as usize],
            None => &[],
        }
    }
}

/// The symbolic occurrences on `nt`'s right hand sides, looking through desugaring groups.
fn symbolic_below(cfg: &Cfg, nt: NtId, seen: &mut BTreeSet<NtId>, out: &mut BTreeSet<OccId>) {
    if !seen.insert(nt) {
        return;
    }
    for &p in &cfg.nts[nt as usize].prods {
        let prod = &cfg.prods[p as usize];
        for (&sym, &occ) in prod.rhs.iter().zip(&prod.occ) {
            match sym {
                Sym::Nt(x) if cfg.nts[x as usize].synthetic => symbolic_below(cfg, x, seen, out),
                _ => {
                    out.insert(occ);
                }
            }
        }
    }
}

/// Every target of the enabled criteria present in a tree of `cfg`, refined or not: a
/// production counts as its ISO production, so a refined copy covers the target of
/// `targets` over the ISO grammar.
pub fn observe(cfg: &Cfg, root: &Node, c: Criteria) -> BTreeSet<Target> {
    let mut out = BTreeSet::new();
    walk(cfg, root, ROOT, &mut Vec::new(), c, false, &mut out);
    out
}

/// As `observe`, with each production as the tree uses it: in a refined grammar every copy
/// is a target of its own, as `targets` over that grammar lists them.
pub fn observe_refined(cfg: &Cfg, root: &Node, c: Criteria) -> BTreeSet<Target> {
    let mut out = BTreeSet::new();
    walk(cfg, root, ROOT, &mut Vec::new(), c, true, &mut out);
    out
}

fn walk(
    cfg: &Cfg,
    node: &Node,
    occ: OccId,
    window: &mut Vec<OccId>,
    c: Criteria,
    refined: bool,
    out: &mut BTreeSet<Target>,
) {
    let symbolic = occ != ROOT && cfg.occs[occ as usize].symbolic;
    if symbolic {
        window.push(occ);
        for j in 1..=(c.k as usize).min(window.len()) {
            out.insert(Target::Path(window[window.len() - j..].to_vec()));
        }
    }
    if let (Sym::Nt(nt), Some(p)) = (node.sym, node.prod) {
        if c.cdrc {
            let as_is = if refined { p } else { cfg.prods[p as usize].unrefined };
            out.insert(Target::Cdrc(occ, as_is));
        }
        if descends(cfg, nt, c) {
            let prod = &cfg.prods[p as usize];
            for (child, &child_occ) in node.children.iter().zip(&prod.occ) {
                walk(cfg, child, child_occ, window, c, refined, out);
            }
        }
    }
    if symbolic {
        window.pop();
    }
}

/// The symbol at an occurrence, for reports.
pub fn occurrence_label(cfg: &Cfg, occ: OccId) -> String {
    if occ == ROOT {
        return "root".into();
    }
    for prod in &cfg.prods {
        if let Some(i) = prod.occ.iter().position(|&o| o == occ) {
            return match prod.rhs[i] {
                Sym::Nt(nt) => format!("<{}>", cfg.base(nt)),
                Sym::Lit(l) => match &cfg.lits[l as usize] {
                    Lit::Kw(k) => k.clone(),
                    Lit::Term(t) => format!("{t:?}"),
                    Lit::Opaque(d) => format!("!!<{d}>"),
                },
            };
        }
    }
    format!("#{occ}")
}

/// A target for reports, e.g. `3-path <graph pattern> > <path pattern list> > <path pattern>`.
pub fn describe_target(cfg: &Cfg, t: &Target) -> String {
    match t {
        Target::Cdrc(occ, p) => {
            let at = match *occ {
                ROOT => "root".to_string(),
                o => format!(
                    "{} in <{}>",
                    occurrence_label(cfg, o),
                    cfg.occs[o as usize].owner
                ),
            };
            format!("cdrc {} at {at}", crate::describe(cfg, *p))
        }
        Target::Path(occs) => {
            let labels: Vec<String> = occs.iter().map(|&o| occurrence_label(cfg, o)).collect();
            format!("{}-path {}", occs.len(), labels.join(" > "))
        }
    }
}
