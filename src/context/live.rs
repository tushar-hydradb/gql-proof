//! What each nonterminal's labels may still be asked about: static liveness of label facts.
//!
//! A label carries facts up the tree (a reference that needs a binder, a flag saying an
//! aggregate is below). A fact matters at a nonterminal only if some chain of parents above it
//! reaches a definition that reads it before one that clears it. If none does, the fact can be
//! dropped there, and labels that differ only in it become one. If no reader is reachable but
//! a definition that rejects on the fact is, every label carrying it is doomed and rejected
//! where it is made, instead of being carried up to where it would be. Computed once over the
//! grammar's parent relation, so it costs the size of the grammar, and it is a union over
//! every place a nonterminal occurs, so it removes only what no tree can read.

use crate::cfg::{Cfg, NtId, Sym};
use std::collections::BTreeSet;

/// One fact a rule's labels can hold, by bit, and the definitions (by name, a desugaring group
/// counting as its definition) that read it, reject on it, or clear it.
pub struct FactSpec {
    pub bit: u32,
    pub name: &'static str,
    pub readers: Vec<&'static str>,
    pub rejecters: Vec<&'static str>,
    pub clearers: Vec<&'static str>,
}

/// Per nonterminal: the facts that may still be read above it (bits a rule declares nothing
/// about are always live), and the ones that doom a label.
#[derive(Debug, Clone, Copy, Default)]
pub struct Masks {
    pub live: u64,
    pub doomed: u64,
}

fn owner(def: &str) -> &str {
    def.split('/').next().unwrap_or(def)
}

/// The masks of every nonterminal of `cfg`. With `start_reads_all`, the start reads every
/// fact (a part of the grammar measured on its own, whose surroundings are unknown).
pub fn masks(cfg: &Cfg, specs: &[FactSpec], start: NtId, start_reads_all: bool) -> Vec<Masks> {
    let n = cfg.nts.len();
    let mut parents: Vec<BTreeSet<NtId>> = vec![BTreeSet::new(); n];
    for prod in &cfg.prods {
        for sym in &prod.rhs {
            if let Sym::Nt(c) = sym {
                parents[*c as usize].insert(prod.lhs);
            }
        }
    }
    let declared: u64 = specs.iter().fold(0, |m, s| m | 1 << s.bit);
    let mut out = vec![
        Masks {
            live: !declared,
            doomed: 0,
        };
        n
    ];
    for spec in specs {
        let role = |nt: NtId, of: &[&str]| of.contains(&owner(cfg.base(nt)));
        // Least fixed points: a reader, or a rejecter, reachable through parents that pass the
        // fact on (neither read, reject nor clear it).
        let mut live = vec![false; n];
        let mut rejected = vec![false; n];
        if start_reads_all {
            live[start as usize] = true;
        }
        let mut changed = true;
        while changed {
            changed = false;
            for nt in 0..n {
                for &m in &parents[nt] {
                    let passes = !role(m, &spec.clearers)
                        && !role(m, &spec.rejecters)
                        && !role(m, &spec.readers);
                    let l = role(m, &spec.readers) || passes && live[m as usize];
                    let r = role(m, &spec.rejecters) || passes && rejected[m as usize];
                    if l && !live[nt] {
                        live[nt] = true;
                        changed = true;
                    }
                    if r && !rejected[nt] {
                        rejected[nt] = true;
                        changed = true;
                    }
                }
            }
        }
        for nt in 0..n {
            if live[nt] {
                out[nt].live |= 1 << spec.bit;
            } else if rejected[nt] {
                out[nt].doomed |= 1 << spec.bit;
            }
        }
    }
    out
}
