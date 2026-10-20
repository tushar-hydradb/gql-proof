//! Purdom's sentence generator (P. Purdom, "A sentence generator for testing parsers",
//! BIT 12, 1972), with a cap on tree height and Zheng & Wu's length control.
//!
//! The goal is a small set of derivation trees that together use every production at least
//! once. Purdom precomputes, for each nonterminal, the shortest terminal derivation and the
//! cheapest way to get from the start symbol to it, then builds sentences that each pick up as
//! many unused productions as they can, falling back to the shortest derivation once nothing
//! new is reachable. Length is Purdom's: the number of nodes in the derivation tree. This
//! version keeps that shape with three changes:
//!
//! - every measure is computed under a remaining height budget, so no tree exceeds
//!   `max_depth`, and productions that only fit in taller trees are reported, not dropped
//! - "is something unused reachable from here" is recomputed live as productions get used,
//!   which is what Purdom's ONCE/ONST bookkeeping approximates
//! - sentence length is capped. Zheng & Wu (COMPSAC 2009, as described by Xu, Zheng & Chen)
//!   take as reference the largest over all productions of the shortest sentence covering it,
//!   which is the smallest possible maximum length of any covering set. Here that reference is
//!   computed under the height cap, and every sentence stays within it
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

/// How long a sentence may get.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Length {
    /// No cap: few, long sentences, closest to Purdom's original.
    Unbounded,
    /// The reference length: the longest of the shortest sentences covering each production.
    Reference,
    /// An explicit cap. Productions whose shortest covering sentence is longer are reported.
    Cap(u32),
}

#[derive(Debug, Clone)]
pub struct Config {
    pub seed: u64,
    /// Maximum tree height. A literal leaf has height 0.
    pub max_depth: u32,
    pub length: Length,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reason {
    /// The left hand side never appears in a tree from the start symbol.
    Unreachable,
    /// Reachable, but the smallest tree from the start symbol using it has this height.
    NeedsDepth(u32),
    /// Fits the height cap, but the shortest sentence using it has this length, over the cap.
    NeedsLength(u32),
    /// No finite derivation exists.
    Unproductive,
    /// Every derivation needs a prose leaf the `LeafProvider` cannot fill, such as an
    /// implementation-defined rule.
    NoLeaf,
}

#[derive(Debug, Clone)]
pub struct Generated {
    pub root: Node,
    /// Productions this tree used for the first time.
    pub new: usize,
    /// Purdom's length: nodes in the derivation tree, grouping nodes from desugaring excluded.
    pub length: u32,
}

#[derive(Debug, Clone)]
pub struct Outcome {
    pub trees: Vec<Generated>,
    pub covered: FixedBitSet,
    pub uncovered: Vec<(ProdId, Reason)>,
    /// The length every sentence stays within, if any.
    pub length_cap: Option<u32>,
    /// The reference length under this height cap.
    pub reference_length: u32,
}

/// What the grammar and the leaf provider determine before any cap is chosen.
pub struct Analysis<'g> {
    cfg: &'g Cfg,
    fillable: Vec<bool>,
    /// Fixed subtrees for definitions whose token the provider fixes, with the productions
    /// each uses.
    templates: Vec<Option<(Node, Vec<ProdId>)>>,
    template_errors: Vec<String>,
    /// Minimum derivation height per nonterminal and per production.
    nt_height: Vec<u32>,
    prod_height: Vec<u32>,
    /// The same, ignoring what the leaf provider can fill.
    unrestricted_height: Vec<u32>,
}

impl<'g> Analysis<'g> {
    pub fn new(cfg: &'g Cfg, leaf: &impl LeafProvider) -> Self {
        // Productions needing a leaf the provider cannot fill get no finite measure, so the
        // generator never picks them.
        let fillable: Vec<bool> = cfg
            .prods
            .iter()
            .map(|prod| {
                prod.rhs.iter().all(|sym| match *sym {
                    Sym::Lit(l) => match &cfg.lits[l as usize] {
                        Lit::Opaque(name) => leaf.supports(name),
                        _ => true,
                    },
                    Sym::Nt(_) => true,
                })
            })
            .collect();
        // Tokens the provider fixes are derived once, through the grammar, so the result is an
        // ordinary derivation tree the verifier can check.
        let mut templates = vec![None; cfg.nts.len()];
        let mut template_errors = Vec::new();
        for (nt, info) in cfg.nts.iter().enumerate() {
            let Some(text) = leaf.token(&info.name).filter(|_| !info.synthetic) else {
                continue;
            };
            let chars: Vec<char> = text.chars().collect();
            let whole = derive(cfg, &fillable, nt as NtId, &chars, 0, 0)
                .into_iter()
                .find(|(_, end)| *end == chars.len());
            match whole {
                Some((node, _)) => {
                    let mut prods = Vec::new();
                    node.prods(&mut prods);
                    templates[nt] = Some((node, prods));
                }
                None => {
                    template_errors.push(format!("{text:?} does not derive from <{}>", info.name))
                }
            }
        }
        let fixed: Vec<Option<u32>> = templates
            .iter()
            .map(|t| t.as_ref().map(|(node, _)| node.height()))
            .collect();
        let (nt_height, mut prod_height) = min_heights(cfg, &fillable, &fixed);
        let all = vec![true; cfg.prods.len()];
        let (_, unrestricted_height) = min_heights(cfg, &all, &fixed);
        // A fixed token is only ever its template: its root production is as tall as the
        // template, and its other productions are never chosen.
        for (nt, template) in templates.iter().enumerate() {
            let Some((node, _)) = template else { continue };
            for &p in &cfg.nts[nt].prods {
                prod_height[p as usize] = if node.prod == Some(p) {
                    node.height()
                } else {
                    INF
                };
            }
        }
        Analysis {
            cfg,
            fillable,
            templates,
            template_errors,
            nt_height,
            prod_height,
            unrestricted_height,
        }
    }

    pub fn min_height(&self, nt: NtId) -> u32 {
        self.nt_height[nt as usize]
    }

    /// Whether `nt`'s productions may contain `child` in a tree, given a remaining height for
    /// `nt`. A templated definition only ever yields its template, never a path elsewhere.
    fn propagates(&self, nt: NtId) -> bool {
        self.templates[nt as usize].is_none()
    }

    /// For each nonterminal, the most remaining height it can be placed with in a tree of
    /// height at most `depth` from `start`, or `None` if it cannot appear.
    fn avail(&self, start: NtId, depth: u32) -> Vec<Option<u32>> {
        let mut avail = vec![None; self.cfg.nts.len()];
        avail[start as usize] = Some(depth);
        let mut changed = true;
        while changed {
            changed = false;
            for (q, prod) in self.cfg.prods.iter().enumerate() {
                let Some(room) = avail[prod.lhs as usize] else {
                    continue;
                };
                if self.prod_height[q] > room || !self.propagates(prod.lhs) {
                    continue;
                }
                for sym in &prod.rhs {
                    if let Sym::Nt(child) = *sym {
                        let slot = &mut avail[child as usize];
                        if slot.is_none_or(|have| have < room - 1) {
                            *slot = Some(room - 1);
                            changed = true;
                        }
                    }
                }
            }
        }
        avail
    }

    /// For each production, the smallest height cap under which some tree from `start` uses
    /// it. Exact: sibling subtrees are independent, and a production's height already requires
    /// every child to fit.
    pub fn need_depths(&self, start: NtId) -> Vec<Option<u32>> {
        let fits = |avail: &[Option<u32>], p: usize| {
            let lhs = self.cfg.prods[p].lhs as usize;
            avail[lhs].is_some_and(|room| self.prod_height[p] <= room)
        };
        // Everything that fits under some cap: an unbounded cap, as far as heights go.
        let unbounded = self.avail(start, INF / 2);
        let target = (0..self.cfg.prods.len())
            .filter(|&p| fits(&unbounded, p))
            .count();
        let mut need = vec![None; self.cfg.prods.len()];
        let mut found = 0;
        let mut depth = self.nt_height[start as usize];
        while found < target {
            let avail = self.avail(start, depth);
            for (p, slot) in need.iter_mut().enumerate() {
                if slot.is_none() && fits(&avail, p) {
                    *slot = Some(depth);
                    found += 1;
                }
            }
            depth += 1;
        }
        need
    }

    /// The smallest height cap under which every production that can appear at all does.
    pub fn reference_height(&self, start: NtId) -> u32 {
        self.need_depths(start)
            .into_iter()
            .flatten()
            .max()
            .unwrap_or(0)
    }
}

/// Height-aware lengths for one cap: `len[nt][r]` is the shortest derivation of `nt` within
/// remaining height `r`, in Purdom's node count.
struct Lengths {
    depth: u32,
    len: Vec<Vec<u32>>,
}

impl Lengths {
    fn new(a: &Analysis, depth: u32) -> Self {
        let cfg = a.cfg;
        let mut len = vec![vec![INF; depth as usize + 1]; cfg.nts.len()];
        for r in 1..=depth {
            for nt in 0..cfg.nts.len() {
                let best = match &a.templates[nt] {
                    Some((node, _)) if node.height() <= r => size(cfg, node),
                    Some(_) => INF,
                    None => cfg.nts[nt]
                        .prods
                        .iter()
                        .filter(|&&p| a.fillable[p as usize])
                        .map(|&p| prod_len(cfg, &len, p, r))
                        .min()
                        .unwrap_or(INF),
                };
                len[nt][r as usize] = best;
            }
        }
        Lengths { depth, len }
    }

    fn nt(&self, nt: NtId, r: u32) -> u32 {
        self.len[nt as usize][r as usize]
    }
}

/// A production's length at remaining height `r`: one for a real node, one per literal, and
/// each child's shortest length at `r - 1`.
fn prod_len(cfg: &Cfg, len: &[Vec<u32>], p: ProdId, r: u32) -> u32 {
    let prod = &cfg.prods[p as usize];
    let own = u32::from(!cfg.nts[prod.lhs as usize].synthetic);
    prod.rhs.iter().fold(own, |acc, sym| {
        let part = match *sym {
            Sym::Lit(_) => 1,
            Sym::Nt(c) => len[c as usize][r as usize - 1],
        };
        acc.saturating_add(part)
    })
}

pub struct Generator<'a, 'g, L> {
    a: &'a Analysis<'g>,
    cfg: &'g Cfg,
    config: Config,
    leaf: L,
    rng: ChaCha8Rng,
    lengths: Lengths,
    unused: FixedBitSet,
    /// `cost(nt, r)` memo, tagged with the `generation` it was computed in.
    memo: Vec<(u32, Option<u32>)>,
    generation: u32,
    /// How much longer the current sentence may get than the lengths its parents planned.
    slack: i64,
    /// The ISO definitions above the node being expanded, for leaf context.
    ctx: Vec<NtId>,
}

impl<'a, 'g, L: LeafProvider> Generator<'a, 'g, L> {
    pub fn new(a: &'a Analysis<'g>, config: Config, leaf: L) -> Self {
        let mut unused = FixedBitSet::with_capacity(a.cfg.prods.len());
        unused.insert_range(..);
        let slots = a.cfg.nts.len() * (config.max_depth as usize + 1);
        Generator {
            a,
            cfg: a.cfg,
            rng: ChaCha8Rng::seed_from_u64(config.seed),
            lengths: Lengths::new(a, config.max_depth),
            config,
            leaf,
            unused,
            memo: vec![(0, None); slots],
            generation: 1,
            slack: 0,
            ctx: Vec::new(),
        }
    }

    fn prod_len(&self, p: ProdId, r: u32) -> u32 {
        prod_len(self.cfg, &self.lengths.len, p, r)
    }

    /// For each production, the length of the shortest sentence from `start` within the
    /// height cap that uses it: Purdom's phase two, with heights.
    pub fn covering_lengths(&self, start: NtId) -> Vec<Option<u32>> {
        let depth = self.lengths.depth;
        // ctx[nt][r]: the shortest rest of a sentence around `nt` placed with room `r`.
        let mut ctx = vec![vec![INF; depth as usize + 1]; self.cfg.nts.len()];
        ctx[start as usize][depth as usize] = 0;
        for r in (1..=depth).rev() {
            for (q, prod) in self.cfg.prods.iter().enumerate() {
                let around = ctx[prod.lhs as usize][r as usize];
                let whole = self.prod_len(q as ProdId, r);
                let usable = self.a.fillable[q] && self.a.propagates(prod.lhs);
                if around == INF || whole == INF || !usable {
                    continue;
                }
                for sym in &prod.rhs {
                    if let Sym::Nt(child) = *sym {
                        let rest = around + whole - self.lengths.nt(child, r - 1);
                        let slot = &mut ctx[child as usize][r as usize - 1];
                        *slot = (*slot).min(rest);
                    }
                }
            }
        }
        (0..self.cfg.prods.len())
            .map(|p| {
                let lhs = self.cfg.prods[p].lhs as usize;
                if !self.a.fillable[p] {
                    return None;
                }
                // A templated definition's root production is as long as the template.
                let own = |r: u32| match &self.a.templates[lhs] {
                    Some((node, _)) if node.prod == Some(p as ProdId) => {
                        self.lengths.nt(lhs as NtId, r)
                    }
                    Some(_) => INF,
                    None => self.prod_len(p as ProdId, r),
                };
                (1..=depth)
                    .filter_map(|r| {
                        let (around, own) = (ctx[lhs][r as usize], own(r));
                        (around != INF && own != INF).then(|| around + own)
                    })
                    .min()
            })
            .collect()
    }

    pub fn run(mut self, start: NtId) -> Result<Outcome> {
        if !self.a.template_errors.is_empty() {
            bail!("fixed tokens: {}", self.a.template_errors.join(", "));
        }
        let depth = self.config.max_depth;
        let need = self.a.nt_height[start as usize];
        if need > depth {
            bail!(
                "<{}> needs a max depth of at least {need}, got {depth}",
                self.cfg.name(start)
            );
        }
        let covering = self.covering_lengths(start);
        let reference_length = covering.iter().flatten().copied().max().unwrap_or(0);
        let cap = match self.config.length {
            Length::Unbounded => None,
            Length::Reference => Some(reference_length),
            Length::Cap(n) => Some(n),
        };
        let shortest = self.lengths.nt(start, depth);
        let mut trees = Vec::new();
        while let Some(cost) = self.cost(start, depth) {
            // The cheapest sentence that uses something new is the shortest covering sentence
            // of some unused production, never above the reference length.
            if cap.is_some_and(|c| cost > c) {
                break;
            }
            self.slack = cap.map_or(i64::MAX / 2, |c| i64::from(c) - i64::from(shortest));
            let before = self.unused.count_ones(..);
            let root = self.expand(start, depth, shortest);
            let new = before - self.unused.count_ones(..);
            // Every round picks up at least one production: the root follows a finite cost
            // within the slack, and nothing before that path can consume its target without
            // itself being new.
            assert!(new > 0, "purdom round made no progress");
            let length = size(self.cfg, &root);
            trees.push(Generated { root, new, length });
        }
        let uncovered = self.classify(start, &covering, cap);
        let mut covered = self.unused.clone();
        covered.toggle_range(..);
        Ok(Outcome {
            trees,
            covered,
            uncovered,
            length_cap: cap,
            reference_length,
        })
    }

    /// Length of the shortest tree of height at most `r` rooted at `nt` that uses an unused
    /// production, or `None` if there is no such tree.
    fn cost(&mut self, nt: NtId, r: u32) -> Option<u32> {
        if r == 0 {
            return None;
        }
        if let Some((node, prods)) = &self.a.templates[nt as usize] {
            let fits = node.height() <= r;
            let new = prods.iter().any(|&p| self.unused.contains(p as usize));
            return (fits && new).then(|| size(self.cfg, node));
        }
        let slot = nt as usize * (self.config.max_depth as usize + 1) + r as usize;
        if self.memo[slot].0 == self.generation {
            return self.memo[slot].1;
        }
        let cfg = self.cfg;
        let mut best = None;
        for &p in &cfg.nts[nt as usize].prods {
            best = min_opt(best, self.prod_cost(p, r));
        }
        self.memo[slot] = (self.generation, best);
        best
    }

    fn prod_cost(&mut self, p: ProdId, r: u32) -> Option<u32> {
        let len = self.prod_len(p, r);
        if len == INF || !self.a.fillable[p as usize] {
            return None;
        }
        if self.unused.contains(p as usize) {
            return Some(len);
        }
        self.chase(p, r).map(|(_, c)| c)
    }

    /// The child of an already used production to chase an unused one through, and the
    /// resulting length.
    fn chase(&mut self, p: ProdId, r: u32) -> Option<(usize, u32)> {
        let len = self.prod_len(p, r);
        let cfg = self.cfg;
        let mut best: Option<(usize, u32)> = None;
        for (i, sym) in cfg.prods[p as usize].rhs.iter().enumerate() {
            let Sym::Nt(child) = *sym else { continue };
            if let Some(c) = self.cost(child, r - 1) {
                let via = len - self.lengths.nt(child, r - 1) + c;
                if best.is_none_or(|(_, b)| via < b) {
                    best = Some((i, via));
                }
            }
        }
        best
    }

    fn expand(&mut self, nt: NtId, r: u32, plan: u32) -> Node {
        if let Some((node, prods)) = &self.a.templates[nt as usize] {
            let node = node.clone();
            for p in prods.clone() {
                self.mark_used(p);
            }
            return node;
        }
        let real = !self.cfg.nts[nt as usize].synthetic;
        if real {
            self.ctx.push(nt);
        }
        let node = self.expand_free(nt, r, plan);
        if real {
            self.ctx.pop();
        }
        node
    }

    fn mark_used(&mut self, p: ProdId) {
        if self.unused.contains(p as usize) {
            self.unused.set(p as usize, false);
            self.generation += 1;
        }
    }

    /// Expands `nt` within height `r`. `plan` is the length the parent counted on; the subtree
    /// may exceed it by at most the sentence's slack.
    fn expand_free(&mut self, nt: NtId, r: u32, plan: u32) -> Node {
        let cfg = self.cfg;
        let fitting: Vec<ProdId> = cfg.nts[nt as usize]
            .prods
            .iter()
            .copied()
            .filter(|&p| self.a.fillable[p as usize] && self.prod_len(p, r) != INF)
            .collect();
        let allowance = i64::from(plan) + self.slack;
        let chases: Vec<(ProdId, u32)> = fitting
            .iter()
            .filter_map(|&p| self.prod_cost(p, r).map(|c| (p, c)))
            .filter(|&(_, c)| i64::from(c) <= allowance)
            .collect();
        let (p, chosen_len, through) = match self.pick(&chases) {
            Some(p) => {
                let len = chases.iter().find(|&&(q, _)| q == p).unwrap().1;
                // An unused production is the target itself; a used one leads to it.
                let through = match self.unused.contains(p as usize) {
                    true => None,
                    false => self.chase(p, r).map(|(i, _)| i),
                };
                (p, len, through)
            }
            None => {
                let shortest: Vec<(ProdId, u32)> =
                    fitting.iter().map(|&p| (p, self.prod_len(p, r))).collect();
                let p = self
                    .pick(&shortest)
                    .expect("caller checked a production fits");
                (p, self.prod_len(p, r), None)
            }
        };
        // The shortest fitting production is exactly the plan's floor, so this only ever
        // spends slack on a chase and never goes below zero.
        self.slack -= i64::from(chosen_len) - i64::from(plan);
        // Fix every child's plan now: what was charged against the slack is decided here, not
        // after earlier siblings have changed what is unused.
        let rhs = &cfg.prods[p as usize].rhs;
        let plans: Vec<u32> = rhs
            .iter()
            .enumerate()
            .map(|(i, &sym)| match sym {
                Sym::Nt(child) => {
                    let floor = self.lengths.nt(child, r - 1);
                    match through == Some(i) {
                        true => self.cost(child, r - 1).unwrap_or(floor),
                        false => floor,
                    }
                }
                Sym::Lit(_) => 1,
            })
            .collect();
        self.mark_used(p);
        let mut children = Vec::with_capacity(rhs.len());
        for (&sym, plan) in rhs.iter().zip(plans) {
            children.push(match sym {
                Sym::Nt(child) => self.expand(child, r - 1, plan),
                Sym::Lit(l) => self.literal(l),
            });
        }
        Node {
            sym: Sym::Nt(nt),
            prod: Some(p),
            text: None,
            children,
        }
    }

    /// The lowest scoring production, ties broken by the seeded rng.
    fn pick(&mut self, scored: &[(ProdId, u32)]) -> Option<ProdId> {
        let low = scored.iter().map(|&(_, c)| c).min()?;
        let ties: Vec<ProdId> = scored
            .iter()
            .filter(|&&(_, c)| c == low)
            .map(|&(p, _)| p)
            .collect();
        ties.choose(&mut self.rng).copied()
    }

    fn literal(&mut self, l: u32) -> Node {
        let text = match &self.cfg.lits[l as usize] {
            Lit::Kw(k) => k.clone(),
            Lit::Term(t) => t.clone(),
            Lit::Opaque(name) => {
                let ctx: Vec<&str> = self.ctx.iter().map(|&nt| self.cfg.name(nt)).collect();
                self.leaf.leaf(name, &ctx, &mut self.rng)
            }
        };
        Node {
            sym: Sym::Lit(l),
            prod: None,
            text: Some(text),
            children: Vec::new(),
        }
    }

    fn classify(
        &self,
        start: NtId,
        covering: &[Option<u32>],
        cap: Option<u32>,
    ) -> Vec<(ProdId, Reason)> {
        let mut reachable = vec![false; self.cfg.nts.len()];
        for nt in self.cfg.reachable(start) {
            reachable[nt as usize] = true;
        }
        let need = self.a.need_depths(start);
        self.unused
            .ones()
            .map(|p| {
                let lhs = self.cfg.prods[p].lhs as usize;
                let reason = if self.a.prod_height[p] == INF && self.a.unrestricted_height[p] != INF
                {
                    Reason::NoLeaf
                } else if self.a.prod_height[p] == INF {
                    Reason::Unproductive
                } else {
                    match (need[p], covering[p]) {
                        _ if !reachable[lhs] => Reason::Unreachable,
                        (None, _) => Reason::Unreachable,
                        (Some(d), _) if d > self.config.max_depth => Reason::NeedsDepth(d),
                        (_, Some(len)) if cap.is_some_and(|c| len > c) => Reason::NeedsLength(len),
                        // Fits both caps yet uncovered, which the generator rules out; report
                        // it plainly rather than hide it.
                        (Some(d), _) => Reason::NeedsDepth(d),
                    }
                };
                (p as ProdId, reason)
            })
            .collect()
    }
}

/// Purdom's length of a subtree: real nodes and literals, grouping nodes from desugaring not
/// counted.
pub fn size(cfg: &Cfg, node: &Node) -> u32 {
    match node.sym {
        Sym::Lit(_) => 1,
        Sym::Nt(nt) => {
            let own = u32::from(!cfg.nts[nt as usize].synthetic);
            own + node.children.iter().map(|c| size(cfg, c)).sum::<u32>()
        }
    }
}

fn min_opt(a: Option<u32>, b: Option<u32>) -> Option<u32> {
    match (a, b) {
        (Some(x), Some(y)) => Some(x.min(y)),
        (x, None) => x,
        (None, y) => y,
    }
}

/// Minimum derivation height per nonterminal and per production, a nonterminal taking its
/// `fixed` height when it has one. A literal is 0, a production is one above its tallest
/// child, so an empty rhs is 1. `INF` marks "no finite derivation yet" and stays absorbing.
fn min_heights(cfg: &Cfg, fillable: &[bool], fixed: &[Option<u32>]) -> (Vec<u32>, Vec<u32>) {
    let mut nt: Vec<u32> = fixed.iter().map(|f| f.unwrap_or(INF)).collect();
    let mut prod = vec![INF; cfg.prods.len()];
    let mut changed = true;
    while changed {
        changed = false;
        for (p, production) in cfg.prods.iter().enumerate() {
            if !fillable[p] {
                continue;
            }
            let value = production
                .rhs
                .iter()
                .map(|sym| match *sym {
                    Sym::Lit(_) => 0,
                    Sym::Nt(c) => nt[c as usize],
                })
                .max()
                .unwrap_or(0)
                .saturating_add(1);
            if value < prod[p] {
                prod[p] = value;
                let lhs = production.lhs as usize;
                if fixed[lhs].is_none() {
                    nt[lhs] = nt[lhs].min(value);
                }
                changed = true;
            }
        }
    }
    (nt, prod)
}

/// Every derivation of `nt` matching a prefix of `text[i..]`, with where each ends. Keywords
/// and terminals match their text, a prose leaf takes one character (the verifier checks it
/// against its rule). Used only for the short, fixed tokens a `LeafProvider` asks for.
fn derive(
    cfg: &Cfg,
    fillable: &[bool],
    nt: NtId,
    text: &[char],
    i: usize,
    depth: u32,
) -> Vec<(Node, usize)> {
    if depth > 4 * text.len() as u32 + 16 {
        return Vec::new();
    }
    let mut out = Vec::new();
    for &p in &cfg.nts[nt as usize].prods {
        if !fillable[p as usize] {
            continue;
        }
        let rhs = &cfg.prods[p as usize].rhs;
        for (children, end) in derive_seq(cfg, fillable, rhs, text, i, depth) {
            out.push((
                Node {
                    sym: Sym::Nt(nt),
                    prod: Some(p),
                    text: None,
                    children,
                },
                end,
            ));
        }
    }
    out
}

fn derive_seq(
    cfg: &Cfg,
    fillable: &[bool],
    rhs: &[Sym],
    text: &[char],
    i: usize,
    depth: u32,
) -> Vec<(Vec<Node>, usize)> {
    let Some((&head, tail)) = rhs.split_first() else {
        return vec![(Vec::new(), i)];
    };
    let firsts: Vec<(Node, usize)> = match head {
        Sym::Nt(child) => derive(cfg, fillable, child, text, i, depth + 1),
        Sym::Lit(l) => {
            let want: Option<String> = match &cfg.lits[l as usize] {
                Lit::Kw(t) | Lit::Term(t) => Some(t.clone()),
                Lit::Opaque(_) => text.get(i).map(|c| c.to_string()),
            };
            match want {
                Some(t) if text[i..].starts_with(&t.chars().collect::<Vec<_>>()) => {
                    let end = i + t.chars().count();
                    let node = Node {
                        sym: head,
                        prod: None,
                        text: Some(t),
                        children: Vec::new(),
                    };
                    vec![(node, end)]
                }
                _ => Vec::new(),
            }
        }
    };
    let mut out = Vec::new();
    for (first, mid) in firsts {
        for (mut rest, end) in derive_seq(cfg, fillable, tail, text, mid, depth) {
            rest.insert(0, first.clone());
            out.push((rest, end));
        }
    }
    out
}
