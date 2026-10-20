//! Desugars the EBNF into a plain context-free grammar, which is what Purdom's algorithm
//! works on.
//!
//! - `[e]` becomes a fresh `N -> e | ε`
//! - `e...` becomes a fresh `N -> e | e N`
//! - a nested `{a | b}` becomes a fresh `N -> a | b`
//!
//! Fresh nonterminals are `synthetic` and get flattened away when a tree is printed. Covering
//! every production of the desugared grammar is stronger than covering the ISO alternatives:
//! every optional is seen both present and absent, every repeat both once and more than once.

use crate::bnf::{Bnf, Ebnf};
use anyhow::{Result, anyhow};
use std::collections::HashMap;

pub type NtId = u32;
pub type LitId = u32;
pub type ProdId = u32;
pub type OccId = u32;

/// A position on a right hand side of the ISO grammar: one node of the grammar graph of
/// Havrikov, Kampmann & Zeller. The two productions a desugared repeat becomes share theirs.
#[derive(Debug, Clone)]
pub struct Occurrence {
    /// The ISO definition whose right hand side this is.
    pub owner: String,
    /// A reference to an ISO definition or a literal. References to desugaring groups are not:
    /// those groups are the grammar graph's alternation and quantifier nodes.
    pub symbolic: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Sym {
    Nt(NtId),
    Lit(LitId),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Lit {
    Kw(String),
    Term(String),
    /// A definition given in prose, filled by a `LeafProvider`.
    Opaque(String),
}

#[derive(Debug, Clone)]
pub struct Nonterminal {
    pub name: String,
    /// The unrefined name: an ISO definition or a desugaring group. Equal to `name` unless the
    /// grammar was refined (see `refine`), which makes one copy per state of a rule.
    pub base: String,
    pub synthetic: bool,
    /// Reachable from `<token>`, so its yield is printed as a single token.
    pub lexical: bool,
    /// The ISO definition this nonterminal came from.
    pub origin: String,
    pub prods: Vec<ProdId>,
}

#[derive(Debug, Clone)]
pub struct Production {
    pub lhs: NtId,
    pub rhs: Vec<Sym>,
    /// The occurrence of each right hand side position, in step with `rhs`.
    pub occ: Vec<OccId>,
    /// The unrefined production this one specializes; itself unless refined.
    pub unrefined: ProdId,
}

#[derive(Debug, Clone)]
pub struct Cfg {
    pub nts: Vec<Nonterminal>,
    pub prods: Vec<Production>,
    pub lits: Vec<Lit>,
    pub occs: Vec<Occurrence>,
    by_name: HashMap<String, NtId>,
    lit_ids: HashMap<Lit, LitId>,
}

impl Cfg {
    pub fn from_bnf(bnf: &Bnf) -> Cfg {
        let mut cfg = Cfg {
            nts: Vec::new(),
            prods: Vec::new(),
            lits: Vec::new(),
            occs: Vec::new(),
            by_name: HashMap::new(),
            lit_ids: HashMap::new(),
        };
        // Intern every definition first so references resolve regardless of order.
        for def in &bnf.defs {
            cfg.add_nt(def.name.clone(), false, def.name.clone());
        }
        for def in &bnf.defs {
            let lhs = cfg.by_name[&def.name];
            let mut fresh = 0;
            let alts = match &def.rhs {
                Ebnf::Alt(alts) => alts.iter().collect(),
                other => vec![other],
            };
            for alt in alts {
                let rhs = cfg.lower(alt, &def.name, &mut fresh);
                cfg.add_prod(lhs, rhs);
            }
        }
        if let Some(token) = cfg.nt("token") {
            for id in cfg.reachable(token) {
                cfg.nts[id as usize].lexical = true;
            }
        }
        cfg
    }

    pub fn nt(&self, name: &str) -> Option<NtId> {
        self.by_name.get(name).copied()
    }

    pub fn require(&self, name: &str) -> Result<NtId> {
        self.nt(name)
            .ok_or_else(|| anyhow!("no definition named <{name}>"))
    }

    pub fn name(&self, nt: NtId) -> &str {
        &self.nts[nt as usize].name
    }

    /// The ISO definition or desugaring group `nt` stands for, refined or not.
    pub fn base(&self, nt: NtId) -> &str {
        &self.nts[nt as usize].base
    }

    /// A grammar built from parts, for refinements. Nonterminals' `prods` must list exactly
    /// the productions with them on the left.
    pub fn from_parts(
        nts: Vec<Nonterminal>,
        prods: Vec<Production>,
        lits: Vec<Lit>,
        occs: Vec<Occurrence>,
    ) -> Cfg {
        let by_name = nts
            .iter()
            .enumerate()
            .map(|(i, nt)| (nt.name.clone(), i as NtId))
            .collect();
        let lit_ids = lits
            .iter()
            .enumerate()
            .map(|(i, l)| (l.clone(), i as LitId))
            .collect();
        Cfg {
            nts,
            prods,
            lits,
            occs,
            by_name,
            lit_ids,
        }
    }

    pub fn prod(&self, p: ProdId) -> &Production {
        &self.prods[p as usize]
    }

    /// Nonterminals reachable from `from`, including itself.
    pub fn reachable(&self, from: NtId) -> Vec<NtId> {
        let mut seen = vec![false; self.nts.len()];
        let mut stack = vec![from];
        let mut out = Vec::new();
        while let Some(nt) = stack.pop() {
            if std::mem::replace(&mut seen[nt as usize], true) {
                continue;
            }
            out.push(nt);
            for &p in &self.nts[nt as usize].prods {
                for sym in &self.prods[p as usize].rhs {
                    if let Sym::Nt(child) = sym {
                        stack.push(*child);
                    }
                }
            }
        }
        out
    }

    fn add_nt(&mut self, name: String, synthetic: bool, origin: String) -> NtId {
        let id = self.nts.len() as NtId;
        self.by_name.insert(name.clone(), id);
        self.nts.push(Nonterminal {
            base: name.clone(),
            name,
            synthetic,
            lexical: false,
            origin,
            prods: Vec::new(),
        });
        id
    }

    fn add_prod(&mut self, lhs: NtId, rhs: Vec<(Sym, OccId)>) {
        let id = self.prods.len() as ProdId;
        let (rhs, occ) = rhs.into_iter().unzip();
        self.prods.push(Production {
            lhs,
            rhs,
            occ,
            unrefined: id,
        });
        self.nts[lhs as usize].prods.push(id);
    }

    fn lit(&mut self, lit: Lit, def: &str) -> (Sym, OccId) {
        let next = self.lits.len() as LitId;
        let id = *self.lit_ids.entry(lit.clone()).or_insert(next);
        if id == next {
            self.lits.push(lit);
        }
        (Sym::Lit(id), self.occurrence(def, true))
    }

    fn occurrence(&mut self, def: &str, symbolic: bool) -> OccId {
        self.occs.push(Occurrence {
            owner: def.to_string(),
            symbolic,
        });
        (self.occs.len() - 1) as OccId
    }

    fn fresh(&mut self, def: &str, kind: &str, counter: &mut u32) -> NtId {
        *counter += 1;
        self.add_nt(format!("{def}/{kind}{counter}"), true, def.to_string())
    }

    /// Lowers `e` to the symbol sequence that replaces it, each with its occurrence, adding
    /// fresh nonterminals as needed.
    fn lower(&mut self, e: &Ebnf, def: &str, fresh: &mut u32) -> Vec<(Sym, OccId)> {
        match e {
            Ebnf::Seq(items) => items
                .iter()
                .flat_map(|i| self.lower(i, def, fresh))
                .collect(),
            Ebnf::Ref(name) => vec![(Sym::Nt(self.by_name[name]), self.occurrence(def, true))],
            Ebnf::Kw(k) => vec![self.lit(Lit::Kw(k.clone()), def)],
            Ebnf::Term(t) => vec![self.lit(Lit::Term(t.clone()), def)],
            Ebnf::Opaque(name) => vec![self.lit(Lit::Opaque(name.clone()), def)],
            Ebnf::Alt(alts) => {
                let n = self.fresh(def, "alt", fresh);
                for alt in alts {
                    let rhs = self.lower(alt, def, fresh);
                    self.add_prod(n, rhs);
                }
                vec![(Sym::Nt(n), self.occurrence(def, false))]
            }
            Ebnf::Opt(inner) => {
                let n = self.fresh(def, "opt", fresh);
                let alts = match inner.as_ref() {
                    Ebnf::Alt(alts) => alts.iter().collect(),
                    other => vec![other],
                };
                for alt in alts {
                    let rhs = self.lower(alt, def, fresh);
                    self.add_prod(n, rhs);
                }
                self.add_prod(n, Vec::new());
                vec![(Sym::Nt(n), self.occurrence(def, false))]
            }
            Ebnf::Repeat(inner) => {
                let n = self.fresh(def, "rep", fresh);
                let once = self.lower(inner, def, fresh);
                let mut more = once.clone();
                more.push((Sym::Nt(n), self.occurrence(def, false)));
                self.add_prod(n, once);
                self.add_prod(n, more);
                vec![(Sym::Nt(n), self.occurrence(def, false))]
            }
        }
    }
}
