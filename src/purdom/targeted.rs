//! Targeted trees for CDRC and k-path coverage: Havrikov, Kampmann & Zeller's algorithm 1.
//!
//! For each target not yet covered, build the shortest tree within the height cap that contains
//! it, add it, and drop every target that tree happens to contain as well. Targets are tried from
//! the longest shortest-tree down, since long trees cover the most by accident.
//!
//! The shortest tree is found with the tables Purdom's phase already has: the shortest subtree
//! of each nonterminal within a remaining height, and the shortest context around a nonterminal
//! placed with some room (Purdom's phase two, with heights). A target fixes a chain of positions
//! or a production at one position; everything off that chain is the shortest subtree.

use super::{Analysis, Generated, Generator, INF, Length, Lengths, prod_len, size};
use crate::cfg::{Cfg, NtId, OccId, ProdId, Sym};
use crate::coverage::{self, Criteria, ROOT, Target};
use crate::leaf::LeafProvider;
use crate::tree::Node;
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// Why a target has no tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TargetReason {
    /// Has one only above the height cap (found within four times it).
    NeedsDepth,
    /// Its shortest tree has this length, over the length cap.
    NeedsLength(u32),
    /// No tree the grammar and its compiled syntax rules allow contains it, within four times
    /// the height cap.
    Never,
    /// It lies inside a token whose text the leaf provider fixes, such as a time zone string.
    FixedToken,
}

/// One criterion's outcome: CDRC, or k-paths of one length.
#[derive(Debug, Clone)]
pub struct Report {
    pub kind: String,
    pub total: usize,
    pub covered: usize,
    /// The longest of the shortest trees containing each target, over targets with one.
    pub reference_length: Option<u32>,
    /// Targeted trees built for targets of this kind.
    pub trees: usize,
    pub uncovered: Vec<(Target, TargetReason)>,
}

fn kind(t: &Target) -> String {
    match t {
        Target::Cdrc(..) => "cdrc".into(),
        Target::Path(occs) => format!("{}-path", occs.len()),
    }
}

/// How to build a subtree: the shortest one, or a fixed production with some children fixed.
#[derive(Debug, Clone)]
pub(super) enum Plan {
    Shortest,
    Prod(ProdId, Vec<(usize, Plan)>),
}

/// The shortest rest of a sentence around a nonterminal placed with room `r`, and the
/// production and position it was placed through.
pub(super) struct Contexts {
    pub(super) len: Vec<Vec<u32>>,
    from: Vec<Vec<Option<(ProdId, usize)>>>,
}

pub(super) fn contexts(a: &Analysis, lengths: &Lengths, start: NtId) -> Contexts {
    let cfg = a.cfg;
    let depth = lengths.depth as usize;
    let mut len = vec![vec![INF; depth + 1]; cfg.nts.len()];
    let mut from = vec![vec![None; depth + 1]; cfg.nts.len()];
    len[start as usize][depth] = 0;
    for r in (1..=depth).rev() {
        for (q, prod) in cfg.prods.iter().enumerate() {
            let around = len[prod.lhs as usize][r];
            let whole = prod_len(cfg, &lengths.len, q as ProdId, r as u32);
            let usable = a.fillable[q] && a.propagates(prod.lhs);
            if around == INF || whole == INF || !usable {
                continue;
            }
            for (i, sym) in prod.rhs.iter().enumerate() {
                if let Sym::Nt(child) = *sym {
                    let rest = around + whole - lengths.nt(child, r as u32 - 1);
                    if rest < len[child as usize][r - 1] {
                        len[child as usize][r - 1] = rest;
                        from[child as usize][r - 1] = Some((q as ProdId, i));
                    }
                }
            }
        }
    }
    Contexts { len, from }
}

/// The search for the shortest tree containing one target.
struct Tables<'t, 'g> {
    a: &'t Analysis<'g>,
    lengths: &'t Lengths,
    ctx: &'t Contexts,
    start: NtId,
    /// Every refined position carrying each occurrence.
    positions: HashMap<OccId, Vec<(ProdId, usize)>>,
}

/// Best way to carry a chain from progress `m` down through a nonterminal: its length, the
/// production and position taken, and the progress below it (`None` once the chain ends).
type Choice = Option<(u32, ProdId, usize, Option<usize>)>;

impl<'t, 'g> Tables<'t, 'g> {
    fn new(a: &'t Analysis<'g>, lengths: &'t Lengths, ctx: &'t Contexts, start: NtId) -> Self {
        let mut positions: HashMap<OccId, Vec<(ProdId, usize)>> = HashMap::new();
        for (q, prod) in a.cfg.prods.iter().enumerate() {
            for (i, &occ) in prod.occ.iter().enumerate() {
                positions.entry(occ).or_default().push((q as ProdId, i));
            }
        }
        Tables {
            a,
            lengths,
            ctx,
            start,
            positions,
        }
    }

    fn cfg(&self) -> &'g Cfg {
        self.a.cfg
    }

    /// Whether a target needs a position that only occurs inside a fixed token.
    fn in_fixed_token(&self, t: &Target) -> bool {
        let inside = |occ: &OccId| {
            let places = self.positions.get(occ).map_or(&[][..], |v| v);
            !places.is_empty()
                && places
                    .iter()
                    .all(|&(q, _)| !self.a.propagates(self.cfg().prods[q as usize].lhs))
        };
        match t {
            Target::Cdrc(occ, _) => *occ != ROOT && inside(occ),
            Target::Path(chain) => chain.iter().any(inside),
        }
    }

    fn pl(&self, p: ProdId, r: u32) -> u32 {
        match self.a.fillable[p as usize] {
            true => prod_len(self.cfg(), &self.lengths.len, p, r),
            false => INF,
        }
    }

    /// `inner`, the plan for `nt` placed with room `r`, wrapped in its shortest context.
    fn in_context(&self, mut nt: NtId, mut r: u32, mut inner: Plan) -> Plan {
        while !(nt == self.start && r == self.lengths.depth) {
            let (q, i) =
                self.ctx.from[nt as usize][r as usize].expect("placed nonterminal has a context");
            inner = Plan::Prod(q, vec![(i, inner)]);
            nt = self.cfg().prods[q as usize].lhs;
            r += 1;
        }
        inner
    }

    /// The shortest tree containing `t`: its length and how to build it.
    fn realize(&self, t: &Target) -> Option<(u32, Plan)> {
        match t {
            Target::Cdrc(occ, base) => self.realize_cdrc(*occ, *base),
            Target::Path(chain) => self.realize_path(chain),
        }
    }

    fn realize_cdrc(&self, occ: OccId, base: ProdId) -> Option<(u32, Plan)> {
        let cfg = self.cfg();
        let depth = self.lengths.depth;
        if occ == ROOT {
            return cfg.nts[self.start as usize]
                .prods
                .iter()
                .filter(|&&p| cfg.prods[p as usize].unrefined == base)
                .map(|&p| (self.pl(p, depth), Plan::Prod(p, Vec::new())))
                .filter(|(c, _)| *c != INF)
                .min_by_key(|(c, _)| *c);
        }
        let mut best: Option<(u32, NtId, u32, Plan)> = None;
        for &(q, i) in self.positions.get(&occ).into_iter().flatten() {
            let prod = &cfg.prods[q as usize];
            let Sym::Nt(child) = prod.rhs[i] else {
                continue;
            };
            for rq in 1..=depth {
                let around = self.ctx.len[prod.lhs as usize][rq as usize];
                let whole = self.pl(q, rq);
                if around == INF || whole == INF || !self.a.propagates(prod.lhs) {
                    continue;
                }
                let floor = self.lengths.nt(child, rq - 1);
                // The child's production at this position: a template fixes its own.
                let options: Vec<(u32, Plan)> = match &self.a.templates[child as usize] {
                    Some((node, _)) => node
                        .prod
                        .filter(|&p| cfg.prods[p as usize].unrefined == base)
                        .map(|_| (floor, Plan::Shortest))
                        .into_iter()
                        .collect(),
                    None => cfg.nts[child as usize]
                        .prods
                        .iter()
                        .filter(|&&p| cfg.prods[p as usize].unrefined == base)
                        .map(|&p| (self.pl(p, rq - 1), Plan::Prod(p, Vec::new())))
                        .filter(|(c, _)| *c != INF)
                        .collect(),
                };
                for (own, plan) in options {
                    let cost = around + whole - floor + own;
                    if best.as_ref().is_none_or(|b| cost < b.0) {
                        best = Some((cost, prod.lhs, rq, Plan::Prod(q, vec![(i, plan)])));
                    }
                }
            }
        }
        best.map(|(cost, nt, r, inner)| (cost, self.in_context(nt, r, inner)))
    }

    fn realize_path(&self, chain: &[OccId]) -> Option<(u32, Plan)> {
        let cfg = self.cfg();
        let mut memo = HashMap::new();
        let mut best: Option<(u32, NtId, u32, Plan)> = None;
        for &(q, i) in self.positions.get(&chain[0]).into_iter().flatten() {
            let prod = &cfg.prods[q as usize];
            if !self.a.propagates(prod.lhs) {
                continue;
            }
            for rq in 1..=self.lengths.depth {
                let around = self.ctx.len[prod.lhs as usize][rq as usize];
                let whole = self.pl(q, rq);
                if around == INF || whole == INF {
                    continue;
                }
                let found = match (chain.len(), prod.rhs[i]) {
                    (1, _) => Some((around + whole, Plan::Prod(q, Vec::new()))),
                    (_, Sym::Nt(child)) => {
                        self.down(chain, 1, child, rq - 1, &mut memo).map(|sub| {
                            let cost = around + whole - self.lengths.nt(child, rq - 1) + sub;
                            let below = self.rebuild(1, child, rq - 1, &memo);
                            (cost, Plan::Prod(q, vec![(i, below)]))
                        })
                    }
                    _ => None,
                };
                if let Some((cost, plan)) = found
                    && best.as_ref().is_none_or(|b| cost < b.0)
                {
                    best = Some((cost, prod.lhs, rq, plan));
                }
            }
        }
        best.map(|(cost, nt, r, inner)| (cost, self.in_context(nt, r, inner)))
    }

    /// The shortest subtree of `nt` within room `r` that carries `chain[m..]` down from it:
    /// through desugaring groups without progress, through the next occurrence with progress.
    fn down(
        &self,
        chain: &[OccId],
        m: usize,
        nt: NtId,
        r: u32,
        memo: &mut HashMap<(NtId, usize, u32), Choice>,
    ) -> Option<u32> {
        if let Some(choice) = memo.get(&(nt, m, r)) {
            return choice.map(|c| c.0);
        }
        if r == 0 || self.a.templates[nt as usize].is_some() {
            memo.insert((nt, m, r), None);
            return None;
        }
        let cfg = self.cfg();
        let mut best: Choice = None;
        for &p in &cfg.nts[nt as usize].prods {
            let whole = self.pl(p, r);
            if whole == INF {
                continue;
            }
            let prod = &cfg.prods[p as usize];
            for (i, (&sym, &occ)) in prod.rhs.iter().zip(&prod.occ).enumerate() {
                let candidate = match sym {
                    Sym::Nt(child) if !cfg.occs[occ as usize].symbolic => self
                        .down(chain, m, child, r - 1, memo)
                        .map(|sub| (whole - self.lengths.nt(child, r - 1) + sub, Some(m))),
                    _ if occ != chain[m] => None,
                    _ if m + 1 == chain.len() => Some((whole, None)),
                    Sym::Nt(child) => self
                        .down(chain, m + 1, child, r - 1, memo)
                        .map(|sub| (whole - self.lengths.nt(child, r - 1) + sub, Some(m + 1))),
                    Sym::Lit(_) => None,
                };
                if let Some((cost, next)) = candidate
                    && best.is_none_or(|b| cost < b.0)
                {
                    best = Some((cost, p, i, next));
                }
            }
        }
        memo.insert((nt, m, r), best);
        best.map(|b| b.0)
    }

    fn rebuild(
        &self,
        m: usize,
        nt: NtId,
        r: u32,
        memo: &HashMap<(NtId, usize, u32), Choice>,
    ) -> Plan {
        let (_, p, i, next) = memo[&(nt, m, r)].expect("rebuilt choices exist");
        let fixed = match (next, self.cfg().prods[p as usize].rhs[i]) {
            (Some(next), Sym::Nt(child)) => {
                vec![(i, self.rebuild(next, child, r - 1, memo))]
            }
            _ => Vec::new(),
        };
        Plan::Prod(p, fixed)
    }
}

impl<L: LeafProvider> Generator<'_, '_, L> {
    /// The shortest tree from `start` within the height cap, if there is one.
    pub fn shortest(mut self, start: NtId) -> Option<Node> {
        let r = self.config.max_depth;
        (self.lengths.nt(start, r) != INF).then(|| self.materialize(start, r, &Plan::Shortest))
    }

    /// For each target, whether some tree from `start` within the height cap contains it.
    pub fn realizable(&self, start: NtId, targets: &[Target]) -> Vec<bool> {
        let ctx = contexts(self.a, &self.lengths, start);
        let tables = Tables::new(self.a, &self.lengths, &ctx, start);
        targets
            .iter()
            .map(|t| tables.realize(t).is_some())
            .collect()
    }

    /// The length of the shortest tree from `start` within the height cap containing `t`.
    pub fn shortest_containing(&self, start: NtId, t: &Target) -> Option<u32> {
        let ctx = contexts(self.a, &self.lengths, start);
        Tables::new(self.a, &self.lengths, &ctx, start)
            .realize(t)
            .map(|(cost, _)| cost)
    }

    /// Builds a tree for `nt` within room `r` following `plan`, the shortest subtree wherever
    /// the plan leaves a choice.
    fn materialize(&mut self, nt: NtId, r: u32, plan: &Plan) -> Node {
        if let Some((node, prods)) = &self.a.templates[nt as usize] {
            let node = node.clone();
            for p in prods.clone() {
                self.mark_used(p);
            }
            return node;
        }
        let cfg = self.cfg;
        let real = !cfg.nts[nt as usize].synthetic;
        if real {
            self.ctx.push(nt);
        }
        let (p, fixed): (ProdId, &[(usize, Plan)]) = match plan {
            Plan::Prod(p, fixed) => (*p, fixed),
            Plan::Shortest => {
                let options: Vec<(ProdId, u32)> = cfg.nts[nt as usize]
                    .prods
                    .iter()
                    .filter(|&&p| self.a.fillable[p as usize])
                    .map(|&p| (p, self.prod_len(p, r)))
                    .filter(|&(_, l)| l != INF)
                    .collect();
                (self.pick(&options).expect("a shortest subtree fits"), &[])
            }
        };
        self.mark_used(p);
        let rhs = &cfg.prods[p as usize].rhs;
        let mut children = Vec::with_capacity(rhs.len());
        for (i, &sym) in rhs.iter().enumerate() {
            children.push(match sym {
                Sym::Nt(child) => {
                    let sub = fixed
                        .iter()
                        .find(|(j, _)| *j == i)
                        .map_or(&Plan::Shortest, |(_, s)| s);
                    self.materialize(child, r - 1, sub)
                }
                Sym::Lit(l) => self.literal(l),
            });
        }
        if real {
            self.ctx.pop();
        }
        Node {
            sym: Sym::Nt(nt),
            prod: Some(p),
            text: None,
            children,
        }
    }

    /// Algorithm 1 over every enabled criterion, after Purdom's `trees`.
    pub(super) fn cover(
        &mut self,
        start: NtId,
        base: &Cfg,
        base_start: NtId,
        criteria: Criteria,
        trees: &mut Vec<Generated>,
    ) -> Vec<Report> {
        let cfg = self.cfg;
        let depth = self.config.max_depth;
        let all = coverage::targets(base, base_start, criteria);
        let mut seen: BTreeSet<Target> = BTreeSet::new();
        for t in trees.iter() {
            seen.extend(coverage::observe(cfg, &t.root, criteria));
        }

        let ctx = contexts(self.a, &self.lengths, start);
        let tables = Tables::new(self.a, &self.lengths, &ctx, start);
        let mut realized = Vec::new();
        let mut out_of_reach = Vec::new();
        for t in all.iter().filter(|t| !seen.contains(t)) {
            match tables.realize(t) {
                Some((cost, plan)) => realized.push((t.clone(), cost, plan)),
                None => out_of_reach.push(t.clone()),
            }
        }
        let mut references: BTreeMap<String, u32> = BTreeMap::new();
        for (t, cost, _) in &realized {
            let r = references.entry(kind(t)).or_default();
            *r = (*r).max(*cost);
        }
        let cap = match self.config.length {
            Length::Unbounded => None,
            Length::Reference => references.values().max().copied(),
            Length::Cap(n) => Some(n),
        };

        // Out of reach under this height cap: look again with four times the room. Nothing
        // built below can contain these either, since any such tree would be a realization.
        let mut uncovered = Vec::new();
        if !out_of_reach.is_empty() {
            let deep = Lengths::new(self.a, depth * 4);
            let deep_ctx = contexts(self.a, &deep, start);
            let deep_tables = Tables::new(self.a, &deep, &deep_ctx, start);
            for t in out_of_reach {
                let reason = match deep_tables.realize(&t) {
                    _ if tables.in_fixed_token(&t) => TargetReason::FixedToken,
                    Some(_) => TargetReason::NeedsDepth,
                    None => TargetReason::Never,
                };
                uncovered.push((t, reason));
            }
        }

        // Longest first: those trees cover the most targets by accident.
        realized.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
        let mut built: BTreeMap<String, usize> = BTreeMap::new();
        for (t, cost, plan) in realized {
            if seen.contains(&t) {
                continue;
            }
            if cap.is_some_and(|c| cost > c) {
                uncovered.push((t, TargetReason::NeedsLength(cost)));
                continue;
            }
            let before = self.unused.count_ones(..);
            let root = self.materialize(start, depth, &plan);
            let length = size(cfg, &root);
            assert_eq!(
                length, cost,
                "a realized tree has the length its search found"
            );
            let found = coverage::observe(cfg, &root, criteria);
            assert!(found.contains(&t), "a realized tree contains its target");
            seen.extend(found);
            *built.entry(kind(&t)).or_default() += 1;
            trees.push(Generated {
                root,
                new: before - self.unused.count_ones(..),
                length,
                covers: Some(coverage::describe_target(base, &t)),
            });
        }

        let mut kinds: BTreeMap<String, Report> = BTreeMap::new();
        for t in &all {
            let k = kind(t);
            let report = kinds.entry(k.clone()).or_insert_with(|| Report {
                kind: k.clone(),
                total: 0,
                covered: 0,
                reference_length: references.get(&k).copied(),
                trees: built.get(&k).copied().unwrap_or(0),
                uncovered: Vec::new(),
            });
            report.total += 1;
            if seen.contains(t) {
                report.covered += 1;
            }
        }
        for (t, reason) in uncovered {
            kinds
                .get_mut(&kind(&t))
                .unwrap()
                .uncovered
                .push((t, reason));
        }
        kinds.into_values().collect()
    }
}
