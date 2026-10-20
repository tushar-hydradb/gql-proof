//! Purdom's sentence generator (P. Purdom, "A sentence generator for testing parsers",
//! BIT 12, 1972), with a cap on tree height.
//!
//! The goal is a small set of derivation trees that together use every production at least
//! once. Purdom precomputes, for each nonterminal, the shortest terminal derivation and the
//! cheapest way to get from the start symbol to it, then builds sentences that each pick up as
//! many unused productions as they can, falling back to the shortest derivation once nothing
//! new is reachable. This version keeps the same shape with two changes:
//!
//! - every cost is computed under a remaining height budget, so no tree exceeds `max_depth`,
//!   and productions that only fit in taller trees are reported rather than dropped
//! - "is something unused reachable from here" is recomputed live as productions get used,
//!   which is what Purdom's ONCE/ONST bookkeeping approximates
//!
//! The seed only breaks ties between equally cheap choices, so every seed gives the same
//! coverage with a different set of trees.

use crate::cfg::{Cfg, Lit, NtId, ProdId, Sym};
use crate::leaf::LeafProvider;
use crate::tree::Node;
use anyhow::{Result, bail};
use fixedbitset::FixedBitSet;
use rand::SeedableRng;
use rand::seq::IndexedRandom;
use rand_chacha::ChaCha8Rng;

const INF: u32 = u32::MAX;

#[derive(Debug, Clone)]
pub struct Config {
    pub seed: u64,
    /// Maximum tree height. A literal leaf has height 0.
    pub max_depth: u32,
    /// Stop chasing new productions in a tree once it has used this many.
    pub max_new_per_tree: Option<usize>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reason {
    /// The left hand side never appears in a tree from the start symbol.
    Unreachable,
    /// Reachable, but the smallest tree from the start symbol using it has this height.
    NeedsDepth(u32),
    /// No finite derivation exists.
    Unproductive,
}

#[derive(Debug, Clone)]
pub struct Generated {
    pub root: Node,
    /// Productions this tree used for the first time.
    pub new: usize,
}

#[derive(Debug, Clone)]
pub struct Outcome {
    pub trees: Vec<Generated>,
    pub covered: FixedBitSet,
    pub uncovered: Vec<(ProdId, Reason)>,
}

pub struct Generator<'g, L> {
    cfg: &'g Cfg,
    config: Config,
    leaf: L,
    rng: ChaCha8Rng,
    /// Minimum derivation height per nonterminal and per production.
    nt_height: Vec<u32>,
    prod_height: Vec<u32>,
    /// Shortest yield length per nonterminal and per production.
    nt_len: Vec<u32>,
    prod_len: Vec<u32>,
    unused: FixedBitSet,
    /// `cost(nt, r)` memo, tagged with the `generation` it was computed in.
    memo: Vec<(u32, Option<u32>)>,
    generation: u32,
    budget: usize,
}

impl<'g, L: LeafProvider> Generator<'g, L> {
    pub fn new(cfg: &'g Cfg, config: Config, leaf: L) -> Self {
        let (nt_height, prod_height) = min_heights(cfg);
        let (nt_len, prod_len) = min_lens(cfg);
        let mut unused = FixedBitSet::with_capacity(cfg.prods.len());
        unused.insert_range(..);
        let slots = cfg.nts.len() * (config.max_depth as usize + 1);
        Generator {
            cfg,
            rng: ChaCha8Rng::seed_from_u64(config.seed),
            config,
            leaf,
            nt_height,
            prod_height,
            nt_len,
            prod_len,
            unused,
            memo: vec![(0, None); slots],
            generation: 1,
            budget: 0,
        }
    }

    pub fn min_height(&self, nt: NtId) -> u32 {
        self.nt_height[nt as usize]
    }

    pub fn run(mut self, start: NtId) -> Result<Outcome> {
        let need = self.nt_height[start as usize];
        if need > self.config.max_depth {
            bail!(
                "<{}> needs a max depth of at least {need}, got {}",
                self.cfg.name(start),
                self.config.max_depth
            );
        }
        let mut trees = Vec::new();
        while self.cost(start, self.config.max_depth).is_some() {
            self.budget = self.config.max_new_per_tree.unwrap_or(usize::MAX).max(1);
            let before = self.unused.count_ones(..);
            let root = self.expand(start, self.config.max_depth);
            let new = before - self.unused.count_ones(..);
            // Every round picks up at least one production: the root follows a finite cost,
            // and nothing before that path can consume its target without itself being new.
            assert!(new > 0, "purdom round made no progress");
            trees.push(Generated { root, new });
        }
        let uncovered = self.classify(start);
        let mut covered = self.unused.clone();
        covered.toggle_range(..);
        Ok(Outcome { trees, covered, uncovered })
    }

    /// Cheapest extra yield length for a tree of height at most `r` rooted at `nt` that uses
    /// an unused production, or `None` if there is no such tree.
    fn cost(&mut self, nt: NtId, r: u32) -> Option<u32> {
        if r == 0 {
            return None;
        }
        let slot = nt as usize * (self.config.max_depth as usize + 1) + r as usize;
        if self.memo[slot].0 == self.generation {
            return self.memo[slot].1;
        }
        let cfg = self.cfg;
        let mut best = None;
        for &p in &cfg.nts[nt as usize].prods {
            if self.prod_height[p as usize] <= r {
                best = min_opt(best, self.prod_cost(p, r));
            }
        }
        self.memo[slot] = (self.generation, best);
        best
    }

    fn prod_cost(&mut self, p: ProdId, r: u32) -> Option<u32> {
        let len = self.prod_len[p as usize];
        if self.unused.contains(p as usize) {
            return Some(len);
        }
        let cfg = self.cfg;
        let mut best = None;
        for sym in &cfg.prods[p as usize].rhs {
            if let Sym::Nt(child) = *sym {
                let via = self.cost(child, r - 1).map(|c| len - self.nt_len[child as usize] + c);
                best = min_opt(best, via);
            }
        }
        best
    }

    fn expand(&mut self, nt: NtId, r: u32) -> Node {
        let cfg = self.cfg;
        let fitting: Vec<ProdId> = cfg.nts[nt as usize]
            .prods
            .iter()
            .copied()
            .filter(|&p| self.prod_height[p as usize] <= r)
            .collect();
        let mut chosen = None;
        if self.budget > 0 {
            let scored: Vec<(ProdId, u32)> = fitting
                .iter()
                .filter_map(|&p| self.prod_cost(p, r).map(|c| (p, c)))
                .collect();
            chosen = self.pick(&scored);
        }
        let p = match chosen {
            Some(p) => p,
            None => {
                let shortest: Vec<(ProdId, u32)> =
                    fitting.iter().map(|&p| (p, self.prod_len[p as usize])).collect();
                self.pick(&shortest).expect("caller checked a production fits")
            }
        };
        if self.unused.contains(p as usize) {
            self.unused.set(p as usize, false);
            self.generation += 1;
            // Fallback expansions can also use something new; that still counts.
            self.budget = self.budget.saturating_sub(1);
        }
        let children = cfg.prods[p as usize]
            .rhs
            .iter()
            .map(|&sym| match sym {
                Sym::Nt(child) => self.expand(child, r - 1),
                Sym::Lit(l) => self.literal(l),
            })
            .collect();
        Node { sym: Sym::Nt(nt), prod: Some(p), text: None, children }
    }

    /// The lowest scoring production, ties broken by the seeded rng.
    fn pick(&mut self, scored: &[(ProdId, u32)]) -> Option<ProdId> {
        let low = scored.iter().map(|&(_, c)| c).min()?;
        let ties: Vec<ProdId> = scored.iter().filter(|&&(_, c)| c == low).map(|&(p, _)| p).collect();
        ties.choose(&mut self.rng).copied()
    }

    fn literal(&mut self, l: u32) -> Node {
        let text = match &self.cfg.lits[l as usize] {
            Lit::Kw(k) => k.clone(),
            Lit::Term(t) => t.clone(),
            Lit::Opaque(name) => self.leaf.leaf(name, &mut self.rng),
        };
        Node { sym: Sym::Lit(l), prod: None, text: Some(text), children: Vec::new() }
    }

    fn classify(&self, start: NtId) -> Vec<(ProdId, Reason)> {
        let mut reachable = vec![false; self.cfg.nts.len()];
        for nt in self.cfg.reachable(start) {
            reachable[nt as usize] = true;
        }
        self.unused
            .ones()
            .map(|p| {
                let lhs = self.cfg.prods[p].lhs as usize;
                let reason = if self.prod_height[p] == INF {
                    Reason::Unproductive
                } else if !reachable[lhs] {
                    Reason::Unreachable
                } else {
                    Reason::NeedsDepth(self.height_using(start, p as ProdId))
                };
                (p as ProdId, reason)
            })
            .collect()
    }

    /// Height of the smallest tree from `start` that uses `target`.
    fn height_using(&self, start: NtId, target: ProdId) -> u32 {
        let cfg = self.cfg;
        let mut best = vec![INF; cfg.nts.len()];
        best[cfg.prods[target as usize].lhs as usize] = self.prod_height[target as usize];
        let mut changed = true;
        while changed {
            changed = false;
            for prod in &cfg.prods {
                for (i, sym) in prod.rhs.iter().enumerate() {
                    let Sym::Nt(child) = *sym else { continue };
                    let via = best[child as usize];
                    if via == INF {
                        continue;
                    }
                    let mut h = via;
                    for (j, other) in prod.rhs.iter().enumerate() {
                        if let (true, Sym::Nt(o)) = (i != j, *other) {
                            h = h.max(self.nt_height[o as usize]);
                        }
                    }
                    let h = h.saturating_add(1);
                    if h < best[prod.lhs as usize] {
                        best[prod.lhs as usize] = h;
                        changed = true;
                    }
                }
            }
        }
        best[start as usize]
    }
}

fn min_opt(a: Option<u32>, b: Option<u32>) -> Option<u32> {
    match (a, b) {
        (Some(x), Some(y)) => Some(x.min(y)),
        (x, None) => x,
        (None, y) => y,
    }
}

/// Minimum derivation height per nonterminal and per production. A literal is 0, a
/// production is one above its tallest child, so an empty rhs is 1.
fn min_heights(cfg: &Cfg) -> (Vec<u32>, Vec<u32>) {
    fixpoint(cfg, |rhs, nt| {
        rhs.iter()
            .map(|sym| match *sym {
                Sym::Lit(_) => 0,
                Sym::Nt(c) => nt[c as usize],
            })
            .max()
            .unwrap_or(0)
            .saturating_add(1)
    })
}

/// Shortest yield length per nonterminal and per production, counting each literal as 1.
fn min_lens(cfg: &Cfg) -> (Vec<u32>, Vec<u32>) {
    fixpoint(cfg, |rhs, nt| {
        rhs.iter()
            .map(|sym| match *sym {
                Sym::Lit(_) => 1,
                Sym::Nt(c) => nt[c as usize],
            })
            .fold(0u32, u32::saturating_add)
    })
}

/// Least fixed point of `measure` over all productions, with a nonterminal taking the best
/// of its productions. `INF` marks "no finite derivation yet" and must stay absorbing.
fn fixpoint(cfg: &Cfg, measure: impl Fn(&[Sym], &[u32]) -> u32) -> (Vec<u32>, Vec<u32>) {
    let mut nt = vec![INF; cfg.nts.len()];
    let mut prod = vec![INF; cfg.prods.len()];
    let mut changed = true;
    while changed {
        changed = false;
        for (p, production) in cfg.prods.iter().enumerate() {
            let value = measure(&production.rhs, &nt);
            if value < prod[p] {
                prod[p] = value;
                let lhs = production.lhs as usize;
                nt[lhs] = nt[lhs].min(value);
                changed = true;
            }
        }
    }
    (nt, prod)
}
