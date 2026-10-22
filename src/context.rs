//! Context-sensitive rules (scoping, types) without multiplying the grammar.
//!
//! `refine` compiles a rule into the grammar: one copy of each nonterminal per inherited and
//! synthesized state, every child-state combination of every production enumerated. With
//! state per variable name that grows with every name and every fact (a third name never
//! finished). This engine keeps the grammar and computes, per nonterminal, the labels its
//! subtrees can have:
//!
//! - a label is synthesized only: what the subtree needs from outside and what it offers,
//!   never the environment around it. A [`Context`] makes inherited conditions into
//!   synthesized ones checked at the ancestor
//! - variables are slots, not names: a label holds its slots in a canonical order, so trees
//!   that differ only by renaming have one label. When slots of two children meet, the rule
//!   says which are the same variable ([`Link`]); names are given after generation
//! - a production is scanned left to right, like a route in RAPTOR (Delling, Pajor, Werneck,
//!   ALENEX 2012): the partial label so far meets each label of the next child and the
//!   results are deduplicated before the one after, instead of enumerating every tuple
//! - labels are found in rounds, each rescanning only the productions with a child that
//!   gained a label or a smaller witness in the round before, and each label keeps only the
//!   size of its smallest tree (Knuth 1977, semi-naive evaluation)
//!
//! What it emits is still a `Cfg`, one nonterminal per (nonterminal, label) reachable from
//! the start, so generation and coverage run unchanged. See
//! `research/context-generation-2026-10-21.md`.

pub mod extract;
pub mod live;
pub mod pair;
pub mod scope;
pub mod stats;
pub mod types;

pub use live::{FactSpec, Masks};

use stats::{ProdStats, RoundStats, Stats};
use std::cell::RefCell;

use crate::cfg::{Cfg, Nonterminal, NtId, ProdId, Production, Sym};
use crate::refine::{Item, Node, items_of};
use crate::tree;
use crate::verify::Plain;
use anyhow::{Result, bail};
use petgraph::unionfind::UnionFind;
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::fmt::Debug;
use std::time::{Duration, Instant};

/// A variable's place in a label.
pub type Slot = u8;

/// Where each slot of a step's inputs goes in its output: the partial label's slots first,
/// then the child's. A slot past the output label's own is a variable closed in this step,
/// local to the production: inputs that share one are one variable. `None` drops a slot.
#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Link(pub Vec<Option<Slot>>);

/// A context-sensitive rule over synthesized labels.
pub trait Context {
    type Label: Clone + Ord + Debug;
    fn name(&self) -> &str;
    /// How many slots `label` holds.
    fn slots(&self, label: &Self::Label) -> usize;
    /// The partial label of `node` before its first child.
    fn empty(&self, node: &Node) -> Self::Label;
    /// The partial labels after the child at `pos`, given the partial label before it and
    /// the child's label (`None` for a token, read from `node.items`). Empty rejects.
    fn push(
        &self,
        node: &Node,
        pos: usize,
        partial: &Self::Label,
        child: Option<&Self::Label>,
    ) -> Vec<(Self::Label, Link)>;
    /// The labels of `node` from its complete partial label. Empty rejects.
    fn finish(&self, node: &Node, partial: &Self::Label) -> Vec<(Self::Label, Link)>;
    /// Whether a whole sentence may have `label`.
    fn top(&self, label: &Self::Label) -> bool;
    /// Whether `def` with `label` spells the name of the label's one slot (`<binding
    /// variable>`, an `<identifier>` that is an alias).
    fn spells(&self, def: &str, label: &Self::Label) -> bool;
    /// A short form of `label`, for naming nonterminals.
    fn show(&self, label: &Self::Label) -> String;
    /// The facts this rule's labels hold that only some definitions read (see [`live`]).
    /// Undeclared facts are always kept.
    fn facts(&self) -> Vec<FactSpec> {
        Vec::new()
    }
    /// `label` with the facts `masks` says nothing above reads dropped, or rejected if it holds
    /// one that dooms it.
    fn project(&self, _label: &Self::Label, _masks: Masks) -> Projection<Self::Label> {
        Projection::Keep
    }
    /// Labels that may join (see [`Context::join`]) share a key; `None` never joins.
    fn join_key(&self, _label: &Self::Label) -> Option<Self::Label> {
        None
    }
    /// One label standing for exactly the trees of `a` and those of `b`, if the rule can say
    /// that (`a` itself when `b`'s trees are among `a`'s). Every `push` and `finish` must
    /// distribute over it: what the joined label gives is what `a` and `b` give together.
    fn join(&self, _a: &Self::Label, _b: &Self::Label) -> Option<Self::Label> {
        None
    }
    /// The ground labels a joined one stands for: each choice it leaves open, made. Emission
    /// emits only ground labels, so the grammar it makes stays context free and sound.
    fn grounds(&self, label: &Self::Label) -> Vec<Self::Label> {
        vec![label.clone()]
    }
    /// Whether trees with label `b` fit wherever `a` is asked for: `a` is `b` with choices
    /// made.
    fn within(&self, a: &Self::Label, b: &Self::Label) -> bool {
        a == b
    }
    /// A key of partial label `partial` before the child at `pos`, for [`Context::compatible`].
    fn partial_key(&self, _node: &Node, _pos: usize, _partial: &Self::Label) -> u64 {
        0
    }
    /// A key of `child` as the child at `pos`, for [`Context::compatible`].
    fn child_key(&self, _node: &Node, _pos: usize, _child: &Self::Label) -> u64 {
        0
    }
    /// Whether a partial label and a child with these keys may lead to a label of `node`: a
    /// necessary condition, so the engine skips the pair when it is false (a join key, as in a
    /// database: the scan of a production is a join).
    fn compatible(&self, _node: &Node, _pos: usize, _partial: u64, _child: u64) -> bool {
        true
    }
    /// Whether a partial label of a ground walk can no longer finish within `target`: slot
    /// `j` of `partial` becomes slot `map[j]` of the finished label (`None` if it closes on
    /// the way), and what a slot asks only grows along a walk, so a partial already asking
    /// more of a slot than `target` does there is a dead end. A rule that cannot tell says
    /// false.
    fn narrower(&self, _partial: &Self::Label, _map: &[Option<Slot>], _target: &Self::Label) -> bool {
        false
    }
}

/// A position's options grouped by [`Context::child_key`], so that a scan pushes a partial
/// label only with the groups [`Context::compatible`] allows for its key: sideways
/// information passing, a hash join in place of the nested loop. The pairs never enumerated
/// are the ones the rule's keys rule out, which the push would reject. Without
/// `Options::keys` every option is in group 0.
struct Keyed<L> {
    by: BTreeMap<u64, Vec<(Opt<L>, u64)>>,
    len: usize,
}

impl<L> Keyed<L> {
    /// The options a partial label with key `partial` is pushed with.
    fn compatible<'s, C: Context<Label = L>>(
        &'s self,
        ctx: &'s C,
        node: &'s Node<'s>,
        pos: usize,
        partial: u64,
    ) -> impl Iterator<Item = &'s (Opt<L>, u64)> {
        self.by
            .iter()
            .filter(move |(k, _)| ctx.compatible(node, pos, partial, **k))
            .flat_map(|(_, v)| v)
    }
}

/// What [`Context::project`] makes of a label.
pub enum Projection<L> {
    Keep,
    Reject,
    /// A smaller label, and where the old one's slots went in it.
    Replace(L, Link),
}

/// How a run goes: whether it reports as it goes, an optional deadline, whether every label
/// of the start is a top (to measure a part of the grammar on its own, `reads_all` then names
/// that start, which reads every fact), and the two savings each switchable alone: facts
/// nothing reads dropped ([`live`]), and one backward pass per production in emission.
#[derive(Debug, Clone)]
pub struct Options {
    pub progress: bool,
    pub deadline: Option<Duration>,
    pub any_top: bool,
    pub reads_all: Option<NtId>,
    pub live: bool,
    pub single_pass: bool,
    /// Labels the rule can join become one in the fixed point (answer subsumption), and
    /// emission makes them ground again.
    pub join: bool,
    /// Pairs whose keys the rule says are incompatible are not pushed.
    pub keys: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            progress: true,
            deadline: None,
            any_top: false,
            reads_all: None,
            live: true,
            single_pass: true,
            join: false,
            keys: false,
        }
    }
}

/// How an emitted production's slots are linked: the slot count of each partial label
/// (before the first child, then after each), each step's link, and the finishing link.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Shape {
    partial: Vec<usize>,
    links: Vec<Link>,
    finish: Link,
}

/// The emitted grammar, with what naming needs.
pub struct Built {
    pub cfg: Cfg,
    pub start: NtId,
    /// What building it spent.
    pub stats: Stats,
    /// Per emitted production.
    shapes: Vec<Shape>,
    /// Slots of each emitted nonterminal's label.
    slots: Vec<usize>,
    /// Emitted nonterminals that spell their one slot's name.
    spelled: Vec<bool>,
}

/// A child option at one position: a token, or a label of the child nonterminal.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Opt<L> {
    Token,
    Label(L),
}

/// The best way found to a partial label: its size, and the step that made it.
type Back<L> = (u64, Option<(L, Opt<L>, Link)>);

struct Engine<'a, C: Context> {
    cfg: &'a Cfg,
    ctx: &'a C,
    options: Options,
    shapes: Vec<Vec<Item<'a>>>,
    /// Per nonterminal: each label and the size of its smallest tree.
    labels: Vec<BTreeMap<C::Label, u64>>,
    /// Per nonterminal: the productions with it on their right hand side.
    users: Vec<BTreeSet<ProdId>>,
    /// Per nonterminal: the facts still read above it, and the ones that doom a label.
    masks: Option<Vec<Masks>>,
    /// Per nonterminal: its labels in the order they were found, so a scan can tell new ones.
    order: Vec<Vec<C::Label>>,
    /// Per production: its partial labels so far, and how many of each child's labels they
    /// already combine.
    cache: RefCell<HashMap<ProdId, Kept<C::Label>>>,
    /// Per nonterminal, with `join`: labels a join replaced. Still valid, no longer pushed.
    subsumed: Vec<BTreeSet<C::Label>>,
    /// Per nonterminal, with `join`: the labels productions made that each live one stands for.
    parts: Vec<BTreeMap<C::Label, Vec<C::Label>>>,
    /// Per nonterminal, with `join`: the live labels by join key.
    keyed: Vec<BTreeMap<C::Label, Vec<C::Label>>>,
    /// When emission must stop, and whether a search inside it found it past that.
    until: std::cell::Cell<Option<Instant>>,
    expired: std::cell::Cell<bool>,
    stats: RefCell<Stats>,
}

/// A production's partial labels kept between scans.
struct Kept<L> {
    layers: Layers<L>,
    seen: Vec<usize>,
}

impl<'a, C: Context> Engine<'a, C> {
    fn new(cfg: &'a Cfg, ctx: &'a C, options: &Options) -> Self {
        let mut users = vec![BTreeSet::new(); cfg.nts.len()];
        for (p, prod) in cfg.prods.iter().enumerate() {
            for sym in &prod.rhs {
                if let Sym::Nt(c) = sym {
                    users[*c as usize].insert(p as ProdId);
                }
            }
        }
        let began = Instant::now();
        let masks = options.live.then(|| {
            let start = options.reads_all.unwrap_or(0);
            live::masks(cfg, &ctx.facts(), start, options.reads_all.is_some())
        });
        let mut stats = Stats::default();
        stats
            .phases
            .insert("live".into(), began.elapsed().as_nanos() as u64);
        Engine {
            cfg,
            ctx,
            options: options.clone(),
            shapes: cfg.prods.iter().map(|p| items_of(cfg, p)).collect(),
            labels: vec![BTreeMap::new(); cfg.nts.len()],
            users,
            masks,
            order: vec![Vec::new(); cfg.nts.len()],
            cache: RefCell::new(HashMap::new()),
            subsumed: vec![BTreeSet::new(); cfg.nts.len()],
            parts: vec![BTreeMap::new(); cfg.nts.len()],
            keyed: vec![BTreeMap::new(); cfg.nts.len()],
            until: std::cell::Cell::new(None),
            expired: std::cell::Cell::new(false),
            stats: RefCell::new(stats),
        }
    }

    /// Adds label `l` of `nt`, made by a production with a smallest tree of `size`; whether
    /// the labels of `nt` changed. With `join`, `l` joins a live label it can (answer
    /// subsumption): the joined label replaces both, standing for the labels made so far, and
    /// joins on while it can.
    fn add(&mut self, nt: usize, l: C::Label, size: u64) -> bool {
        if let Some(old) = self.labels[nt].get_mut(&l) {
            *old = (*old).min(size);
            return false;
        }
        let key = self.options.join.then(|| self.ctx.join_key(&l)).flatten();
        let Some(key) = key else {
            self.labels[nt].insert(l.clone(), size);
            self.order[nt].push(l);
            return true;
        };
        let ctx = self.ctx;
        let (mut cur, mut parts, mut size) = (l.clone(), vec![l], size);
        loop {
            let live = self.keyed[nt].entry(key.clone()).or_default();
            let found = live
                .iter()
                .enumerate()
                .find_map(|(i, m)| ctx.join(m, &cur).map(|j| (i, j)));
            let Some((i, j)) = found else { break };
            let m = live.remove(i);
            let m_size = self.labels[nt][&m];
            if j == m {
                // Already standing for these trees.
                self.keyed[nt].get_mut(&key).unwrap().insert(i, m.clone());
                let e = self.labels[nt].get_mut(&m).unwrap();
                *e = (*e).min(size);
                self.parts[nt].get_mut(&m).unwrap().extend(parts);
                self.stats.get_mut().joined += 1;
                return false;
            }
            self.subsumed[nt].insert(m.clone());
            // The subsumed label keeps its own parts: a kept layer may still hold it as the
            // option it was when scanned, and grounding it reads them.
            parts.extend(self.parts[nt].get(&m).cloned().unwrap_or_default());
            size = size.min(m_size);
            cur = j;
            self.stats.get_mut().joined += 1;
        }
        if self.labels[nt].contains_key(&cur) {
            // A label subsumed before, standing again: live once more.
            self.subsumed[nt].remove(&cur);
        }
        self.labels[nt].insert(cur.clone(), size);
        self.keyed[nt].entry(key).or_default().push(cur.clone());
        let own = self.parts[nt].entry(cur.clone()).or_default();
        own.extend(parts);
        own.sort();
        own.dedup();
        self.order[nt].push(cur);
        true
    }

    /// For measuring: over every production's kept layers, the options in back pointers that
    /// are labels a join replaced, and among them the ones with no `parts` entry (which
    /// grounding could only over-approximate).
    fn orphaned_options(&self) -> (usize, usize) {
        let (mut subsumed, mut orphaned) = (0, 0);
        let cache = self.cache.borrow();
        for (&p, kept) in cache.iter() {
            let rhs = &self.cfg.prods[p as usize].rhs;
            for (pos, layer) in kept.layers.iter().enumerate().skip(1) {
                let Sym::Nt(c) = rhs[pos - 1] else { continue };
                for (_, back) in layer.values() {
                    let Some((_, Opt::Label(l), _)) = back else { continue };
                    if !self.live(c as usize, l) {
                        subsumed += 1;
                        if !self.parts[c as usize].contains_key(l) {
                            orphaned += 1;
                        }
                    }
                }
            }
        }
        (subsumed, orphaned)
    }

    /// Whether label `l` of `nt` is still pushed (not replaced by a join).
    fn live(&self, nt: usize, l: &C::Label) -> bool {
        !self.subsumed[nt].contains(l)
    }

    /// The ground options option `o` at a position holding `sym` stands for: the grounds of
    /// the labels productions made that it joined. Not the joined label's own grounds: a label
    /// that asks nothing of a variable absorbs one that asks for a node (its trees fit
    /// anywhere), but the node's trees are other trees, and emission must still reach them.
    fn ground_options(&self, sym: Sym, o: &Opt<C::Label>) -> Vec<Opt<C::Label>> {
        let (Sym::Nt(c), Opt::Label(l)) = (sym, o) else {
            return vec![o.clone()];
        };
        let mut made: Vec<&C::Label> = match self.parts[c as usize].get(l) {
            Some(parts) => parts.iter().collect(),
            None => vec![l],
        };
        // Cheapest first: a walk that takes the first candidate with a witness then takes
        // the smallest tree, and a label absorbed by one asking less lists every label of
        // its key, hundreds at an expression, which label order would try in no useful
        // order.
        made.sort_by_key(|m| self.labels[c as usize].get(*m).copied().unwrap_or(u64::MAX));
        let mut seen = BTreeSet::new();
        let mut out = Vec::new();
        for m in made {
            for g in self.ctx.grounds(m) {
                if seen.insert(g.clone()) {
                    out.push(Opt::Label(g));
                }
            }
        }
        out
    }

    fn prod_stats<'s>(&self, stats: &'s mut Stats, p: ProdId) -> &'s mut ProdStats {
        stats.prods.entry(p).or_insert_with(|| ProdStats {
            describe: crate::describe(self.cfg, p),
            ..ProdStats::default()
        })
    }

    /// The rule's `finish` for production `p`, counted, each label then projected to what is
    /// still read above `p`'s left hand side.
    fn finish(&self, p: ProdId, node: &Node, partial: &C::Label) -> Vec<(C::Label, Link)> {
        let began = Instant::now();
        let mut out = self.ctx.finish(node, partial);
        let (mut projected, mut doomed) = (0, 0);
        if let Some(masks) = &self.masks {
            let m = masks[self.cfg.prods[p as usize].lhs as usize];
            out = out
                .into_iter()
                .filter_map(|(l, link)| match self.ctx.project(&l, m) {
                    Projection::Keep => Some((l, link)),
                    Projection::Reject => {
                        doomed += 1;
                        None
                    }
                    Projection::Replace(l2, by) => {
                        projected += 1;
                        // Slots of the partial label, through the finished one, into the
                        // projected one. Local slots of the finish step are numbered after
                        // the projection's own.
                        let (old, new) = (by.0.len() as Slot, self.ctx.slots(&l2) as Slot);
                        let next =
                            by.0.iter()
                                .flatten()
                                .filter(|&&t| t >= new)
                                .max()
                                .map_or(new, |t| t + 1);
                        let link = Link(
                            link.0
                                .iter()
                                .map(|s| {
                                    s.and_then(|s| {
                                        if s < old {
                                            by.0[s as usize]
                                        } else {
                                            Some(next + s - old)
                                        }
                                    })
                                })
                                .collect(),
                        );
                        Some((l2, link))
                    }
                })
                .collect();
            // Two labels may project to one: keep the first link for each.
            let mut seen = BTreeSet::new();
            out.retain(|(l, _)| seen.insert(l.clone()));
        }
        let mut stats = self.stats.borrow_mut();
        stats.projected += projected;
        stats.doomed += doomed;
        let d = stats.defs.entry(node.def.to_string()).or_default();
        d.finishes += 1;
        d.finished += out.len() as u64;
        d.finish_nanos += began.elapsed().as_nanos() as u64;
        out
    }
    fn node(&self, p: ProdId) -> Node<'_> {
        let lhs = &self.cfg.nts[self.cfg.prods[p as usize].lhs as usize];
        Node {
            def: &lhs.base,
            group: lhs.synthetic,
            items: &self.shapes[p as usize],
            text: None,
        }
    }

    /// The options at a right hand side position, with their sizes.
    fn options(&self, sym: Sym) -> Vec<(Opt<C::Label>, u64)> {
        match sym {
            Sym::Lit(_) => vec![(Opt::Token, 1)],
            Sym::Nt(c) => self.labels[c as usize]
                .iter()
                .filter(|(l, _)| self.live(c as usize, l))
                .map(|(l, &s)| (Opt::Label(l.clone()), s))
                .collect(),
        }
    }

    /// The rule's `push`, counted for production `p` and its definition. With `keys`, a pair
    /// the rule's keys rule out is skipped, not pushed.
    fn push(
        &self,
        p: ProdId,
        node: &Node,
        pos: usize,
        partial: &C::Label,
        o: &Opt<C::Label>,
    ) -> Vec<(C::Label, Link)> {
        if self.options.keys
            && let Opt::Label(child) = o
            && !self.ctx.compatible(
                node,
                pos,
                self.ctx.partial_key(node, pos, partial),
                self.ctx.child_key(node, pos, child),
            )
        {
            self.stats.borrow_mut().skipped += 1;
            return Vec::new();
        }
        let began = Instant::now();
        let out = match o {
            Opt::Token => self.ctx.push(node, pos, partial, None),
            Opt::Label(l) => self.ctx.push(node, pos, partial, Some(l)),
        };
        let nanos = began.elapsed().as_nanos() as u64;
        let mut stats = self.stats.borrow_mut();
        let d = stats.defs.entry(node.def.to_string()).or_default();
        d.pushes += 1;
        d.pushed += out.len() as u64;
        d.push_nanos += nanos;
        let ps = self.prod_stats(&mut stats, p);
        ps.pushes += 1;
        ps.pushed += out.len() as u64;
        out
    }

    /// `options` at `pos` of `node`, grouped by the rule's key.
    fn keyed(&self, node: &Node, pos: usize, options: Vec<(Opt<C::Label>, u64)>) -> Keyed<C::Label> {
        let len = options.len();
        let mut by = BTreeMap::<u64, Vec<_>>::new();
        for (o, size) in options {
            let key = match &o {
                Opt::Label(l) if self.options.keys => self.ctx.child_key(node, pos, l),
                _ => 0,
            };
            by.entry(key).or_default().push((o, size));
        }
        Keyed { by, len }
    }

    /// The key of `partial` before `pos`, if the options there are in more than one group.
    fn partial_key(&self, node: &Node, pos: usize, options: &Keyed<C::Label>, partial: &C::Label) -> u64 {
        if options.by.len() > 1 || options.by.keys().next().is_some_and(|k| *k != 0) {
            self.ctx.partial_key(node, pos, partial)
        } else {
            0
        }
    }

    /// Every partial label reachable after each position of `p`, with its smallest size and
    /// the step that reached it.
    fn layers(&self, p: ProdId) -> Vec<BTreeMap<C::Label, Back<C::Label>>> {
        let _span = tracing::debug_span!("layers", p).entered();
        let began = Instant::now();
        let node = self.node(p);
        let mut layers = vec![BTreeMap::from([(self.ctx.empty(&node), (1, None))])];
        for (pos, &sym) in self.cfg.prods[p as usize].rhs.iter().enumerate() {
            let options = self.keyed(&node, pos, self.options(sym));
            let mut next: BTreeMap<C::Label, Back<C::Label>> = BTreeMap::new();
            for (partial, (cost, _)) in &layers[pos] {
                let key = self.partial_key(&node, pos, &options, partial);
                for (o, size) in options.compatible(self.ctx, &node, pos, key) {
                    for (q, link) in self.push(p, &node, pos, partial, o) {
                        let c = cost + size;
                        if next.get(&q).is_none_or(|(old, _)| c < *old) {
                            next.insert(q, (c, Some((partial.clone(), o.clone(), link))));
                        }
                    }
                }
            }
            layers.push(next);
        }
        let mut stats = self.stats.borrow_mut();
        let ps = self.prod_stats(&mut stats, p);
        ps.scans += 1;
        ps.nanos += began.elapsed().as_nanos() as u64;
        for l in &layers {
            ps.partials_max = ps.partials_max.max(l.len());
            ps.partials_total += l.len() as u64;
        }
        layers
    }

    /// The labels `p` gives its left hand side that it may not have given before, with a size
    /// each. Semi-naive: `p`'s partial labels are kept between scans, and a scan builds only
    /// what involves a child label new since the last one (a new partial label with every
    /// option, an old one with the new options).
    fn scan(&self, p: ProdId) -> BTreeMap<C::Label, u64> {
        let _span = tracing::debug_span!("scan", p).entered();
        let began = Instant::now();
        let node = self.node(p);
        let rhs = &self.cfg.prods[p as usize].rhs;
        let mut cache = self.cache.borrow_mut();
        let first = !cache.contains_key(&p);
        let kept = cache.entry(p).or_insert_with(|| Kept {
            layers: vec![BTreeMap::from([(self.ctx.empty(&node), (1, None))])],
            seen: vec![0; rhs.len()],
        });
        let mut fresh: Vec<C::Label> = if first {
            kept.layers[0].keys().cloned().collect()
        } else {
            Vec::new()
        };
        for (pos, &sym) in rhs.iter().enumerate() {
            let all = self.options(sym);
            let new: Vec<(Opt<C::Label>, u64)> = match sym {
                Sym::Lit(_) if first => all.clone(),
                Sym::Lit(_) => Vec::new(),
                Sym::Nt(c) => self.order[c as usize][kept.seen[pos]..]
                    .iter()
                    .filter(|l| self.live(c as usize, l))
                    .map(|l| (Opt::Label(l.clone()), self.labels[c as usize][l]))
                    .collect(),
            };
            let (all, new) = (self.keyed(&node, pos, all), self.keyed(&node, pos, new));
            if let Sym::Nt(c) = sym {
                kept.seen[pos] = self.order[c as usize].len();
            }
            if kept.layers.len() == pos + 1 {
                kept.layers.push(BTreeMap::new());
            }
            let fresh_here: BTreeSet<&C::Label> = fresh.iter().collect();
            let old: Vec<(C::Label, u64)> = kept.layers[pos]
                .iter()
                .filter(|(l, _)| !fresh_here.contains(l))
                .map(|(l, (c, _))| (l.clone(), *c))
                .collect();
            let fresh_costs: Vec<(C::Label, u64)> = fresh
                .iter()
                .map(|l| (l.clone(), kept.layers[pos][l].0))
                .collect();
            let mut added = Vec::new();
            for (partials, options) in [(&fresh_costs, &all), (&old, &new)] {
                if options.len == 0 {
                    continue;
                }
                for (partial, cost) in partials {
                    let key = self.partial_key(&node, pos, options, partial);
                    for (o, size) in options.compatible(self.ctx, &node, pos, key) {
                        for (q, link) in self.push(p, &node, pos, partial, o) {
                            let c = cost + size;
                            let next = &mut kept.layers[pos + 1];
                            match next.get_mut(&q) {
                                None => {
                                    next.insert(
                                        q.clone(),
                                        (c, Some((partial.clone(), o.clone(), link))),
                                    );
                                    added.push(q);
                                }
                                Some(e) if c < e.0 => {
                                    *e = (c, Some((partial.clone(), o.clone(), link)))
                                }
                                Some(_) => {}
                            }
                        }
                    }
                }
            }
            fresh = added;
        }
        let mut out = BTreeMap::new();
        let last = kept.layers.last().unwrap();
        let ends: Vec<(C::Label, u64)> = fresh.iter().map(|q| (q.clone(), last[q].0)).collect();
        let partials: Vec<usize> = kept.layers.iter().map(BTreeMap::len).collect();
        drop(cache);
        for (partial, cost) in ends {
            for (l, _) in self.finish(p, &node, &partial) {
                let e = out.entry(l).or_insert(cost);
                *e = (*e).min(cost);
            }
        }
        let mut stats = self.stats.borrow_mut();
        let ps = self.prod_stats(&mut stats, p);
        ps.scans += 1;
        ps.nanos += began.elapsed().as_nanos() as u64;
        for n in partials {
            ps.partials_max = ps.partials_max.max(n);
            ps.partials_total += n as u64;
        }
        out
    }

    /// `p`'s partial labels as the fixed point left them, for emission.
    fn kept_layers(&self, p: ProdId) -> Layers<C::Label> {
        match self.cache.borrow_mut().remove(&p) {
            Some(k) if k.layers.len() == self.cfg.prods[p as usize].rhs.len() + 1 => k.layers,
            _ => self.layers(p),
        }
    }

    /// Live labels: the ones a join replaced are not counted.
    fn total(&self) -> usize {
        self.labels.iter().map(BTreeMap::len).sum::<usize>()
            - self.subsumed.iter().map(BTreeSet::len).sum::<usize>()
    }

    fn widest(&self) -> String {
        let (nt, labels) = self
            .labels
            .iter()
            .enumerate()
            .max_by_key(|(_, l)| l.len())
            .unwrap();
        let some: Vec<String> = labels.keys().take(4).map(|l| self.ctx.show(l)).collect();
        format!(
            "<{}> with {} labels ({}, ...)",
            self.cfg.nts[nt].name,
            labels.len(),
            some.join("; ")
        )
    }

    /// The nonterminals with the most labels, each with labels from across its set.
    fn census(&self) -> String {
        let mut by: Vec<(usize, &BTreeMap<C::Label, u64>)> =
            self.labels.iter().enumerate().collect();
        by.sort_by_key(|(_, l)| std::cmp::Reverse(l.len()));
        let mut out = String::new();
        for (nt, labels) in by.into_iter().take(12) {
            let step = (labels.len() / 4).max(1);
            let some: Vec<String> = labels
                .keys()
                .step_by(step)
                .take(4)
                .map(|l| self.ctx.show(l))
                .collect();
            out.push_str(&format!(
                "\n  {:>7}  <{}>  {}",
                labels.len(),
                self.cfg.nts[nt].name,
                some.join(" | ")
            ));
        }
        out
    }

    /// Labels per nonterminal, to the least fixed point.
    fn fixpoint(&mut self) -> Result<()> {
        let _span = tracing::info_span!("fixpoint").entered();
        let began = Instant::now();
        let mut said = Instant::now();
        let mut dirty: BTreeSet<ProdId> = (0..self.cfg.prods.len() as ProdId).collect();
        let mut round = 0;
        while !dirty.is_empty() {
            round += 1;
            let _round = tracing::info_span!("round", round, dirty = dirty.len()).entered();
            let round_began = Instant::now();
            let before = self.total();
            let scanned = dirty.len();
            let mut changed = BTreeSet::new();
            for p in std::mem::take(&mut dirty) {
                let lhs = self.cfg.prods[p as usize].lhs as usize;
                for (l, size) in self.scan(p) {
                    // Only a new label is news for the productions above: a smaller witness
                    // of a known one is kept, but rounds go by height, so the first is small.
                    if self.add(lhs, l, size) {
                        changed.insert(lhs);
                    }
                }
                if let Some(deadline) = self.options.deadline
                    && began.elapsed() > deadline
                {
                    self.record_labels();
                    bail!(
                        "{}: no fixed point after {deadline:?}, round {round}, {} labels; the widest:{}",
                        self.ctx.name(),
                        self.total(),
                        self.census()
                    );
                }
                if self.options.progress && said.elapsed() > Duration::from_secs(5) {
                    eprintln!(
                        "{}: round {round}, {} labels, {:?}; the widest is {}",
                        self.ctx.name(),
                        self.total(),
                        began.elapsed(),
                        self.widest()
                    );
                    said = Instant::now();
                }
            }
            for nt in changed {
                dirty.extend(self.users[nt].iter().copied());
            }
            let labels = self.total();
            self.stats.get_mut().rounds.push(RoundStats {
                round,
                scanned,
                new_labels: labels - before,
                labels,
                nanos: round_began.elapsed().as_nanos() as u64,
            });
        }
        self.record_labels();
        self.stats
            .get_mut()
            .phases
            .insert("fixpoint".into(), began.elapsed().as_nanos() as u64);
        Ok(())
    }

    /// Labels per nonterminal into the stats.
    fn record_labels(&mut self) {
        let labels = self
            .labels
            .iter()
            .enumerate()
            .filter(|(_, l)| !l.is_empty())
            .map(|(nt, l)| {
                let live = l.len() - self.subsumed[nt].len();
                (self.cfg.nts[nt].name.clone(), live)
            })
            .collect();
        self.stats.get_mut().labels = labels;
    }

    /// An instance from its steps (option, link, partial label after) and finishing link.
    fn instance(
        &self,
        node: &Node,
        steps: Vec<(Opt<C::Label>, Link, C::Label)>,
        finish: Link,
    ) -> Instance<C::Label> {
        let mut partial = vec![self.ctx.slots(&self.ctx.empty(node))];
        partial.extend(steps.iter().map(|(_, _, q)| self.ctx.slots(q)));
        let shape = Shape {
            partial,
            links: steps.iter().map(|(_, l, _)| l.clone()).collect(),
            finish,
        };
        (steps.into_iter().map(|(o, _, _)| o).collect(), shape)
    }

    /// The steps that reach partial label `at` after position `upto` of `layers`, smallest.
    fn back(
        layers: &Layers<C::Label>,
        upto: usize,
        mut at: C::Label,
    ) -> Vec<(Opt<C::Label>, Link, C::Label)> {
        let mut steps = Vec::new();
        for k in (0..upto).rev() {
            let (_, back) = &layers[k + 1][&at];
            let (prev, o, l) = back.clone().unwrap();
            steps.push((o, l, at));
            at = prev;
        }
        steps.reverse();
        steps
    }

    /// For each label `p` gives, the complete partial label of its smallest instance and the
    /// finishing link: computed once per production, so `smallest` is a lookup.
    fn ends(&self, p: ProdId, layers: &Layers<C::Label>) -> Ends<C::Label> {
        let node = self.node(p);
        let mut out: Ends<C::Label> = BTreeMap::new();
        for (q, (cost, _)) in layers.last().unwrap() {
            for (l, link) in self.finish(p, &node, q) {
                if out.get(&l).is_none_or(|(c, _, _)| cost < c) {
                    out.insert(l, (*cost, q.clone(), link));
                }
            }
        }
        out
    }

    /// The smallest instance of `p` that gives label `target`.
    fn smallest(
        &self,
        p: ProdId,
        layers: &Layers<C::Label>,
        ends: &Ends<C::Label>,
        target: &C::Label,
    ) -> Option<Instance<C::Label>> {
        let node = self.node(p);
        let (_, q, link) = ends.get(target)?;
        Some(self.instance(
            &node,
            Self::back(layers, layers.len() - 1, q.clone()),
            link.clone(),
        ))
    }

    /// With `join`: the smallest instance of `p` giving a label ground label `target` lies
    /// within, made ground (see [`Engine::ground`]).
    fn smallest_ground(
        &self,
        p: ProdId,
        layers: &Layers<C::Label>,
        ends: &Ends<C::Label>,
        target: &C::Label,
    ) -> Option<Instance<C::Label>> {
        let mut made: Vec<(u64, &C::Label)> = ends
            .iter()
            .filter(|(r, _)| self.ctx.within(target, r))
            .map(|(r, (cost, _, _))| (*cost, r))
            .collect();
        made.sort();
        made.into_iter().find_map(|(_, r)| {
            let instance = self.smallest(p, layers, ends, r)?;
            let (ground, _) = self.ground(
                p,
                &instance,
                None,
                &|l| self.ctx.within(target, l),
                &|_, _| true,
                Some(target),
                &[false, true],
            )?;
            Some(ground)
        })
    }

    /// `instance` of `p` with every child label one of its grounds (the option `fixed` names
    /// at its position, and only ones `child_ok` takes), linked as the instance is, giving a
    /// label `accept` takes; with that label. A joined label is valid for each of its grounds,
    /// but an emitted nonterminal must make one choice, or a tree could pair one child's
    /// choice with another's. `modes` says which searches to run: narrow (false, the
    /// instance's own options made ground), wide (true, every option at every position)
    fn ground(
        &self,
        p: ProdId,
        (opts, shape): &Instance<C::Label>,
        fixed: Option<(usize, &Opt<C::Label>)>,
        accept: &dyn Fn(&C::Label) -> bool,
        child_ok: &dyn Fn(usize, &Opt<C::Label>) -> bool,
        target: Option<&C::Label>,
        modes: &[bool],
    ) -> Option<(Instance<C::Label>, C::Label)> {
        let node = self.node(p);
        // First the instance's own options, made ground; failing that, any option at the
        // other positions: a choice may need another sibling (an edge's binder, not the
        // node's the instance had), not another ground of the same one.
        let began = Instant::now();
        let done = |kind: Option<bool>| {
            let mut stats = self.stats.borrow_mut();
            match kind {
                Some(false) => stats.emit.ground_narrow += 1,
                Some(true) => stats.emit.ground_wide += 1,
                None => stats.emit.ground_failed += 1,
            }
            stats.emit.ground_nanos += began.elapsed().as_nanos() as u64;
        };
        for &wide in modes {
            let walk = Walk {
                p,
                node: &node,
                opts,
                shape,
                fixed,
                accept,
                child_ok,
                target,
                wide,
                failed: RefCell::new(BTreeSet::new()),
                bad: RefCell::new(BTreeSet::new()),
                good: RefCell::new(BTreeSet::new()),
            };
            let mut chosen = Vec::with_capacity(opts.len());
            let mut steps = Vec::with_capacity(opts.len());
            let empty = self.ctx.empty(&node);
            if let Some((out, finish)) =
                self.ground_from(&walk, empty.clone(), &mut chosen, &mut steps)
            {
                let mut partial = vec![self.ctx.slots(&empty)];
                partial.extend(steps.iter().map(|(_, n)| *n));
                let shape = Shape {
                    partial,
                    links: steps.into_iter().map(|(l, _)| l).collect(),
                    finish,
                };
                done(Some(wide));
                return Some(((chosen, shape), out));
            }
        }
        done(None);
        None
    }

    /// One position of [`Engine::ground`]'s walk: `steps` holds each step's link and the
    /// slots of the partial label after it.
    fn ground_from(
        &self,
        w: &Walk<'_, C::Label>,
        partial: C::Label,
        chosen: &mut Vec<Opt<C::Label>>,
        steps: &mut Vec<(Link, usize)>,
    ) -> Option<(C::Label, Link)> {
        if self.until.get().is_some_and(|t| Instant::now() > t) {
            self.expired.set(true);
            return None;
        }
        let pos = chosen.len();
        if pos == w.opts.len() {
            let mut rejected = 0;
            let found = self
                .finish(w.p, w.node, &partial)
                .into_iter()
                .filter(|(_, link)| w.wide || *link == w.shape.finish)
                .find(|(l, _)| {
                    let ok = (w.accept)(l);
                    rejected += !ok as u64;
                    ok
                });
            self.stats.borrow_mut().emit.ground_accept_rejected += rejected;
            let found = found?;
            // A finished, accepted completion: now every chosen child needs a witness.
            for (i, candidate) in chosen.iter().enumerate() {
                let key = (i, candidate.clone());
                if w.good.borrow().contains(&key) {
                    continue;
                }
                if (w.child_ok)(i, candidate) {
                    w.good.borrow_mut().insert(key);
                } else {
                    self.stats.borrow_mut().emit.ground_child_rejected += 1;
                    w.bad.borrow_mut().insert(key);
                    return None;
                }
            }
            return Some(found);
        }
        if w.failed.borrow().contains(&(pos, partial.clone())) {
            return None;
        }
        let sym = self.cfg.prods[w.p as usize].rhs[pos];
        let candidates: Vec<Opt<C::Label>> = match w.fixed {
            Some((at, o)) if at == pos => vec![o.clone()],
            _ if w.wide => {
                let mut all = self.ground_options(sym, &w.opts[pos]);
                let mut options = self.options(sym);
                options.sort_by_key(|(_, size)| *size);
                for (o, _) in options {
                    all.extend(self.ground_options(sym, &o));
                }
                let mut seen = BTreeSet::new();
                all.retain(|o| seen.insert(o.clone()));
                all
            }
            _ => self.ground_options(sym, &w.opts[pos]),
        };
        for candidate in candidates {
            if w.bad.borrow().contains(&(pos, candidate.clone())) {
                continue;
            }
            self.stats.borrow_mut().emit.ground_candidates += 1;
            for (q, link) in self.push(w.p, w.node, pos, &partial, &candidate) {
                if !w.wide && link != w.shape.links[pos] {
                    continue;
                }
                let slots = self.ctx.slots(&q);
                // In a narrow walk the links ahead are the instance's: where each slot of
                // `q` ends up in the finished label is known, so a partial already past the
                // target is cut here.
                if let Some(target) = w.target
                    && !w.wide
                {
                    let width = self.ctx.slots(target);
                    let map: Vec<Option<Slot>> = (0..slots as Slot)
                        .map(|mut j| {
                            for k in pos + 1..w.opts.len() {
                                j = w.shape.links[k].0.get(j as usize).copied().flatten()?;
                                if j as usize >= w.shape.partial[k + 1] {
                                    return None;
                                }
                            }
                            let j = w.shape.finish.0.get(j as usize).copied().flatten()?;
                            ((j as usize) < width).then_some(j)
                        })
                        .collect();
                    if self.ctx.narrower(&q, &map, target) {
                        self.stats.borrow_mut().emit.ground_narrowed += 1;
                        continue;
                    }
                }
                chosen.push(candidate.clone());
                steps.push((link, slots));
                if let Some(found) = self.ground_from(w, q, chosen, steps) {
                    return Some(found);
                }
                chosen.pop();
                steps.pop();
            }
        }
        w.failed.borrow_mut().insert((pos, partial));
        None
    }

    /// For every position and every option there that `open` asks for, the smallest
    /// instance of `p` giving a label `target` accepts that takes it, with the label each
    /// gives.
    fn instances(
        &self,
        p: ProdId,
        layers: &Layers<C::Label>,
        target: impl Fn(&C::Label) -> bool,
        open: impl Fn(usize, &Opt<C::Label>) -> bool,
    ) -> Vec<Found<C::Label>> {
        let rhs = &self.cfg.prods[p as usize].rhs;
        let n = rhs.len();
        let wanted: Vec<Vec<(Opt<C::Label>, u64)>> = (0..n)
            .map(|pos| {
                self.options(rhs[pos])
                    .into_iter()
                    .filter(|(o, _)| open(pos, o))
                    .collect()
            })
            .collect();
        if wanted.iter().all(Vec::is_empty) {
            self.stats.borrow_mut().emit.backward_skipped += 1;
            return Vec::new();
        }
        self.stats.borrow_mut().emit.backward_runs += 1;
        let _span = tracing::debug_span!("instances", p).entered();
        let table = self.ahead(p, layers, target);
        let mut out = Vec::new();
        for (pos, options) in wanted.into_iter().enumerate() {
            for (o, size) in options {
                if let Some((end, instance)) = self.taking(p, layers, &table, pos, &o, size) {
                    out.push(((pos, o), end, instance));
                }
            }
        }
        out
    }

    /// The cheapest way from each partial label of `p` at each position to a finished label
    /// `target` takes, backwards; and the label each complete partial label ends in. One full
    /// product over the layers; keyed.
    fn ahead(
        &self,
        p: ProdId,
        layers: &Layers<C::Label>,
        target: impl Fn(&C::Label) -> bool,
    ) -> AheadTable<C::Label> {
        let node = self.node(p);
        let rhs = &self.cfg.prods[p as usize].rhs;
        let n = rhs.len();
        let mut ahead: Vec<Ahead<C::Label>> = vec![BTreeMap::new(); n + 1];
        let mut ends: BTreeMap<C::Label, C::Label> = BTreeMap::new();
        for q in layers[n].keys() {
            let end = self
                .finish(p, &node, q)
                .into_iter()
                .find(|(l, _)| target(l));
            if let Some((l, link)) = end {
                ahead[n].insert(q.clone(), (0, None, link));
                ends.insert(q.clone(), l);
            }
        }
        for pos in (0..n).rev() {
            let options = self.keyed(&node, pos, self.options(rhs[pos]));
            let mut here = BTreeMap::new();
            for partial in layers[pos].keys() {
                let key = self.partial_key(&node, pos, &options, partial);
                for (o, size) in options.compatible(self.ctx, &node, pos, key) {
                    for (q, link) in self.push(p, &node, pos, partial, o) {
                        let Some((rest, _, _)) = ahead[pos + 1].get(&q) else {
                            continue;
                        };
                        let c = size + rest;
                        let e = here.entry(partial.clone()).or_insert((
                            u64::MAX,
                            None,
                            Link::default(),
                        ));
                        if c < e.0 {
                            *e = (c, Some((o.clone(), q.clone(), link)), Link::default());
                        }
                    }
                }
            }
            ahead[pos] = here;
        }
        AheadTable { ahead, ends }
    }

    /// The cheapest instance of `p` taking option `o` (of size `size`) at `pos` and ending in
    /// a label `table` was built for, with that label: the partial labels before `pos` tried
    /// against `o`, the rest read off the table.
    fn taking(
        &self,
        p: ProdId,
        layers: &Layers<C::Label>,
        table: &AheadTable<C::Label>,
        pos: usize,
        o: &Opt<C::Label>,
        size: u64,
    ) -> Option<(C::Label, Instance<C::Label>)> {
        let node = self.node(p);
        let n = self.cfg.prods[p as usize].rhs.len();
        let key = match o {
            Opt::Label(l) if self.options.keys => self.ctx.child_key(&node, pos, l),
            _ => 0,
        };
        // The best (partial before, step) taking `o` here.
        let mut best: Option<(u64, C::Label, C::Label, Link)> = None;
        for (partial, (cost, _)) in &layers[pos] {
            if key != 0
                && !self.ctx.compatible(
                    &node,
                    pos,
                    self.ctx.partial_key(&node, pos, partial),
                    key,
                )
            {
                continue;
            }
            for (q, link) in self.push(p, &node, pos, partial, o) {
                let Some((rest, _, _)) = table.ahead[pos + 1].get(&q) else {
                    continue;
                };
                let c = cost + size + rest;
                if best.as_ref().is_none_or(|b| c < b.0) {
                    best = Some((c, partial.clone(), q, link));
                }
            }
        }
        let (_, before, after, link) = best?;
        // Back to the start along the smallest steps, then on to the end.
        let mut steps = Self::back(layers, pos, before);
        steps.push((o.clone(), link, after.clone()));
        let mut at = after;
        for layer in &table.ahead[pos + 1..n] {
            let (_, next, _) = &layer[&at];
            let (o, q, l) = next.clone().unwrap();
            steps.push((o, l, q.clone()));
            at = q;
        }
        let finish = table.ahead[n][&at].2.clone();
        let end = table.ends[&at].clone();
        Some((end, self.instance(&node, steps, finish)))
    }
}

/// Per partial label at a position: the cost of the cheapest completion, the step it takes
/// (option, partial label after, link), and at the last position the finishing link.
type Ahead<L> = BTreeMap<L, (u64, Option<(Opt<L>, L, Link)>, Link)>;

/// [`Engine::ahead`]'s result: the table per position, and the label each complete partial
/// label ends in.
struct AheadTable<L> {
    ahead: Vec<Ahead<L>>,
    ends: BTreeMap<L, L>,
}

/// The partial labels after each position of a production, with the step that reached each.
type Layers<L> = Vec<BTreeMap<L, Back<L>>>;

/// Per label a production gives: its smallest instance's size, complete partial label and
/// finishing link.
type Ends<L> = BTreeMap<L, (u64, L, Link)>;

/// An instance found for a position and option, with the label it gives.
type Found<L> = (Choice<L>, L, Instance<L>);

/// Per production, its layers and ends, kept for emission.
type Prepared<L> = BTreeMap<ProdId, (Layers<L>, Ends<L>)>;

/// Instances waiting for the label they give to be reached, per production and label.
type Pending<L> = BTreeMap<(ProdId, L), Vec<(Choice<L>, Instance<L>)>>;

/// A position and the option taken there.
type Choice<L> = (usize, Opt<L>);

/// The options an instance takes at each position, and how its slots link.
type Instance<L> = (Vec<Opt<L>>, Shape);

/// Reached labels of one nonterminal by join key, with their emitted ids.
type Keyed<'a, L> = BTreeMap<Option<L>, Vec<(&'a L, NtId)>>;

/// Whether ground option `g` is one of the choices option `o` leaves open.
fn opt_within<C: Context>(ctx: &C, g: &Opt<C::Label>, o: &Opt<C::Label>) -> bool {
    match (g, o) {
        (Opt::Token, Opt::Token) => true,
        (Opt::Label(a), Opt::Label(b)) => ctx.within(a, b),
        _ => false,
    }
}

/// What [`Engine::ground`] walks: an instance of production `p`, the option fixed at one
/// position, and what the label it gives must satisfy.
struct Walk<'w, L> {
    p: ProdId,
    node: &'w Node<'w>,
    opts: &'w [Opt<L>],
    shape: &'w Shape,
    fixed: Option<(usize, &'w Opt<L>)>,
    accept: &'w dyn Fn(&L) -> bool,
    /// Whether a ground candidate may be tried at a position at all (extraction: it has a
    /// witness). Decided per position, so the failure memo below stays valid.
    child_ok: &'w dyn Fn(usize, &Opt<L>) -> bool,
    /// The label the finished one must lie within, if the walk has one: partial labels that
    /// already ask more are cut ([`Context::narrower`]).
    target: Option<&'w L>,
    /// Any option at the other positions, not only the instance's, and any links.
    wide: bool,
    /// Partial labels at a position no completion was found from.
    failed: RefCell<BTreeSet<(usize, L)>>,
    /// Candidates at a position found to have no witness, and ones found to have one. A
    /// witness is looked for only once a completion has finished and been accepted: a
    /// candidate on a branch that never finishes is never searched for.
    bad: RefCell<BTreeSet<(usize, Opt<L>)>>,
    good: RefCell<BTreeSet<(usize, Opt<L>)>>,
}

/// The grammar whose derivation trees are, up to the names of variables, exactly `cfg`'s
/// that `ctx` accepts and that are reachable from `start`. `placeholder` spells every
/// variable until [`Built::name`] names them.
pub fn build<C: Context>(
    cfg: &Cfg,
    ctx: &C,
    start: NtId,
    placeholder: &str,
    options: &Options,
) -> Result<Built> {
    analyze(cfg, ctx, options)?.emit(start, placeholder)
}

/// The labels of every nonterminal, to the fixed point; [`Analyzed::emit`] makes the grammar.
pub fn analyze<'a, C: Context>(
    cfg: &'a Cfg,
    ctx: &'a C,
    options: &Options,
) -> Result<Analyzed<'a, C>> {
    let mut e = Engine::new(cfg, ctx, options);
    e.fixpoint()?;
    Ok(Analyzed { e })
}

/// The fixed point, kept for emission and for measuring single productions.
pub struct Analyzed<'a, C: Context> {
    e: Engine<'a, C>,
}

/// One production measured alone against the labels of its children: the partial labels
/// after each position, and what the run spent.
pub struct Profile {
    pub partials: Vec<usize>,
    pub children: Vec<usize>,
    pub stats: Stats,
}

impl<'a, C: Context> Analyzed<'a, C> {
    /// What the run has spent so far.
    pub fn stats(&self) -> Stats {
        self.e.stats.borrow().clone()
    }

    /// The labels nonterminal `nt` has at the fixed point.
    pub fn labels(&self, nt: NtId) -> impl Iterator<Item = &C::Label> {
        self.e.labels[nt as usize].keys()
    }

    /// With `join`: options held in kept layers that a join replaced, and among them the ones
    /// whose made labels are lost (must be none; see `Engine::add`).
    pub fn orphaned_options(&self) -> (usize, usize) {
        self.e.orphaned_options()
    }

    /// The labels productions of `nt` made, before any join: every live label's parts, and
    /// the labels that joined nothing.
    pub fn made(&self, nt: NtId) -> Vec<&C::Label> {
        let mut out: BTreeSet<&C::Label> = BTreeSet::new();
        for l in self.e.labels[nt as usize].keys() {
            match self.e.parts[nt as usize].get(l) {
                Some(parts) => out.extend(parts.iter()),
                None => {
                    out.insert(l);
                }
            }
        }
        out.into_iter().collect()
    }

    /// Scans production `p` once more, alone, with fresh counters.
    pub fn profile(&self, p: ProdId) -> Profile {
        let saved = self.e.stats.replace(Stats::default());
        let layers = self.e.layers(p);
        let stats = self.e.stats.replace(saved);
        Profile {
            partials: layers.iter().map(BTreeMap::len).collect(),
            children: self.e.cfg.prods[p as usize]
                .rhs
                .iter()
                .map(|s| match s {
                    Sym::Nt(c) => self.e.labels[*c as usize].len(),
                    Sym::Lit(_) => 1,
                })
                .collect(),
            stats,
        }
    }

    /// The grammar of the labels reachable from `start` (see [`build`]).
    pub fn emit(&self, start: NtId, placeholder: &str) -> Result<Built> {
        let _span = tracing::info_span!("emit").entered();
        let (cfg, ctx, e) = (self.e.cfg, self.e.ctx, &self.e);
        let join = e.options.join;
        if join && !e.options.single_pass {
            bail!("{}: emission from joined labels is single pass", ctx.name());
        }
        let tops: Vec<C::Label> = e.labels[start as usize]
            .keys()
            .filter(|l| e.live(start as usize, l))
            .filter(|l| e.options.any_top || ctx.top(l))
            .cloned()
            .collect();
        if tops.is_empty() || (tops.len() > 1 && !e.options.any_top) {
            bail!(
                "{}: <{}> has {} labels a whole sentence may have, not one",
                ctx.name(),
                cfg.name(start),
                tops.len()
            );
        }
        let top = &tops[0];

        // One nonterminal per label reachable from the start, breadth first.
        let mut out = Emit {
            cfg,
            ctx,
            placeholder,
            ids: BTreeMap::new(),
            queue: VecDeque::new(),
            nts: Vec::new(),
            slots: Vec::new(),
            spelled: Vec::new(),
            add_nanos: 0,
        };
        let root = out.intern(start, top);
        for t in &tops[1..] {
            out.intern(start, t);
        }
        let mut prods = Vec::new();
        let mut shapes = Vec::new();
        // Each label of a nonterminal at each position of each production it fills, taken by one
        // instance: every label usable there is reachable there, for cdrc and k-paths, while
        // the grammar stays linear in labels rather than in labels of parent times child.
        let mut taken: BTreeSet<(ProdId, Choice<C::Label>)> = BTreeSet::new();
        let mut layers: Prepared<C::Label> = BTreeMap::new();
        // One backward pass per production: every option's smallest instance, waiting under the
        // label it gives until that label is reached.
        let mut pending: Pending<C::Label> = BTreeMap::new();
        let mut choices: BTreeMap<ProdId, Vec<Choice<C::Label>>> = BTreeMap::new();
        // Per production: how many labels of its left hand side were reached at its last
        // fallback pass.
        let mut tried: BTreeMap<ProdId, usize> = BTreeMap::new();
        let began = Instant::now();
        let mut said = Instant::now();
        // Searches inside one expansion check the deadline themselves.
        e.until.set(e.options.deadline.map(|d| began + d));
        loop {
            while let Some((nt, l)) = out.queue.pop_front() {
                if e.options.progress && said.elapsed() > Duration::from_secs(5) {
                    eprintln!(
                        "{}: emitting, {} nonterminals ({} to expand), {} productions, {:?}",
                        ctx.name(),
                        out.nts.len(),
                        out.queue.len(),
                        prods.len(),
                        began.elapsed()
                    );
                    said = Instant::now();
                }
                if let Some(deadline) = e.options.deadline
                    && (began.elapsed() > deadline || e.expired.get())
                {
                    bail!(
                        "{}: emission not done after {deadline:?}\n{}",
                        ctx.name(),
                        self.stats().summary(12)
                    );
                }
                e.stats.borrow_mut().emit.expanded += 1;
                let lhs = out.ids[&(nt, l.clone())];
                for &p in &cfg.nts[nt as usize].prods {
                    let prod = &cfg.prods[p as usize];
                    let step_began = Instant::now();
                    let (pushes_before, runs_before) = {
                        let stats = e.stats.borrow();
                        (
                            stats.prods.get(&p).map_or(0, |s| s.pushes),
                            stats.emit.backward_runs,
                        )
                    };
                    let (layers, ends) = &*layers.entry(p).or_insert_with(|| {
                        let l = e.kept_layers(p);
                        let ends = e.ends(p, &l);
                        (l, ends)
                    });
                    // The smallest instance, so this label can always finish, and the ones that take
                    // an option no instance took yet.
                    let smallest = if join {
                        e.smallest_ground(p, layers, ends, &l)
                    } else {
                        e.smallest(p, layers, ends, &l)
                    };
                    let mut chosen: BTreeSet<Instance<C::Label>> = smallest.into_iter().collect();
                    if !chosen.is_empty() && e.options.single_pass {
                        if let std::collections::btree_map::Entry::Vacant(slot) = choices.entry(p) {
                            let all = e.instances(p, layers, |_| true, |_, _| true);
                            if join {
                                // Each ground of each option is a choice of its own, so every
                                // choice a joined label leaves open is taken somewhere.
                                let mut cs = Vec::new();
                                for ((pos, o), _, instance) in all {
                                    for g in e.ground_options(prod.rhs[pos], &o) {
                                        // With no ground instance at all, no tree takes
                                        // this choice here: it is no choice to cover.
                                        let Some((ground, made)) =
                                            e.ground(
                                                p,
                                                &instance,
                                                Some((pos, &g)),
                                                &|_| true,
                                                &|_, _| true,
                                                None,
                                                &[false, true],
                                            )
                                        else {
                                            continue;
                                        };
                                        cs.push((pos, g.clone()));
                                        for end in ctx.grounds(&made) {
                                            pending
                                                .entry((p, end))
                                                .or_default()
                                                .push(((pos, g.clone()), ground.clone()));
                                        }
                                    }
                                }
                                slot.insert(cs);
                            } else {
                                slot.insert(all.iter().map(|(c, _, _)| c.clone()).collect());
                                for (choice, end, instance) in all {
                                    pending
                                        .entry((p, end))
                                        .or_default()
                                        .push((choice, instance));
                                }
                            }
                        }
                        for (choice, instance) in
                            pending.remove(&(p, l.clone())).unwrap_or_default()
                        {
                            if taken.insert((p, choice)) {
                                chosen.insert(instance);
                            }
                        }
                    } else if !chosen.is_empty() {
                        let found = e.instances(
                            p,
                            layers,
                            |t| *t == l,
                            |pos, o| !taken.contains(&(p, (pos, o.clone()))),
                        );
                        for (choice, _, instance) in found {
                            if taken.insert((p, choice)) {
                                chosen.insert(instance);
                            }
                        }
                    }
                    {
                        let options_max = prod
                            .rhs
                            .iter()
                            .map(|s| match s {
                                Sym::Nt(c) => e.labels[*c as usize].len(),
                                Sym::Lit(_) => 1,
                            })
                            .max()
                            .unwrap_or(0);
                        let mut stats = e.stats.borrow_mut();
                        let pushes = stats.prods.get(&p).map_or(0, |s| s.pushes) - pushes_before;
                        let runs = stats.emit.backward_runs - runs_before;
                        let ep = stats
                            .emit
                            .prods
                            .entry(p)
                            .or_insert_with(|| stats::EmitProd {
                                describe: crate::describe(cfg, p),
                                ..stats::EmitProd::default()
                            });
                        ep.expansions += 1;
                        ep.backward_runs += runs;
                        ep.pushes += pushes;
                        ep.emitted += chosen.len() as u64;
                        ep.nanos += step_began.elapsed().as_nanos() as u64;
                        ep.options_max = options_max;
                    }
                    for instance in chosen {
                        out.add(&mut prods, &mut shapes, lhs, prod, instance);
                    }
                }
            }
            if !e.options.single_pass {
                break;
            }
            // An option whose smallest instance gives a label never reached: look for one that
            // gives a reached label instead.
            let fallback_began = Instant::now();
            let mut reached_by: BTreeMap<NtId, BTreeMap<C::Label, NtId>> = BTreeMap::new();
            for ((n, l), id) in &out.ids {
                reached_by.entry(*n).or_default().insert(l.clone(), *id);
            }
            for (&p, cs) in &choices {
                let mut open: BTreeSet<Choice<C::Label>> = cs
                    .iter()
                    .filter(|c| !taken.contains(&(p, (*c).clone())))
                    .cloned()
                    .collect();
                if open.is_empty() {
                    continue;
                }
                if e.options.progress && said.elapsed() > Duration::from_secs(5) {
                    let s = e.stats.borrow();
                    eprintln!(
                        "{}: emission fallback, production {p}, {} open choices, {} nonterminals, ground instances {} / {} wide / {} failed ({:.1} s), {:?}",
                        ctx.name(),
                        open.len(),
                        out.nts.len(),
                        s.emit.ground_narrow,
                        s.emit.ground_wide,
                        s.emit.ground_failed,
                        s.emit.ground_nanos as f64 / 1e9,
                        began.elapsed()
                    );
                    said = Instant::now();
                }
                if let Some(deadline) = e.options.deadline
                    && (began.elapsed() > deadline || e.expired.get())
                {
                    bail!(
                        "{}: emission not done after {deadline:?} (in the fallback)\n{}",
                        ctx.name(),
                        self.stats().summary(12)
                    );
                }
                // One pass to whichever reached label is cheapest, for every open option at once;
                // again only once more labels of its left hand side are reached.
                let prod = &cfg.prods[p as usize];
                let empty = BTreeMap::new();
                let reached = reached_by.get(&prod.lhs).unwrap_or(&empty);
                if tried.get(&p) == Some(&reached.len()) {
                    continue;
                }
                tried.insert(p, reached.len());
                e.stats.borrow_mut().emit.fallback_runs += 1;
                if join {
                    // The reached labels by join key: a label lies within another only if
                    // they share it.
                    let mut keyed: Keyed<'_, C::Label> = BTreeMap::new();
                    for (r, id) in reached {
                        keyed.entry(ctx.join_key(r)).or_default().push((r, *id));
                    }
                    let reached_within = |l: &C::Label| {
                        keyed
                            .get(&ctx.join_key(l))
                            .and_then(|rs| rs.iter().find(|(r, _)| ctx.within(r, l)))
                            .map(|(_, id)| *id)
                    };
                    let fits = |l: &C::Label| reached_within(l).is_some();
                    let found = e.instances(p, &layers[&p].0, fits, |pos, o| {
                        open.iter()
                            .any(|(at, g)| *at == pos && opt_within(ctx, g, o))
                    });
                    for ((pos, o), _, instance) in found {
                        let wanted: Vec<Opt<C::Label>> = open
                            .iter()
                            .filter(|(at, g)| *at == pos && opt_within(ctx, g, &o))
                            .map(|(_, g)| g.clone())
                            .collect();
                        for g in wanted {
                            let Some((ground, made)) =
                                e.ground(
                                    p,
                                    &instance,
                                    Some((pos, &g)),
                                    &fits,
                                    &|_, _| true,
                                    None,
                                    &[false, true],
                                )
                            else {
                                continue;
                            };
                            let Some(id) = reached_within(&made) else {
                                continue;
                            };
                            open.remove(&(pos, g.clone()));
                            if taken.insert((p, (pos, g))) {
                                e.stats.borrow_mut().emit.fallback_emitted += 1;
                                out.add(&mut prods, &mut shapes, id, prod, ground);
                            }
                        }
                    }
                    continue;
                }
                let found = e.instances(
                    p,
                    &layers[&p].0,
                    |l| reached.contains_key(l),
                    |pos, o| open.contains(&(pos, o.clone())),
                );
                for (choice, end, instance) in found {
                    open.remove(&choice);
                    if taken.insert((p, choice)) {
                        e.stats.borrow_mut().emit.fallback_emitted += 1;
                        out.add(&mut prods, &mut shapes, reached[&end], prod, instance);
                    }
                }
            }
            *e.stats
                .borrow_mut()
                .phases
                .entry("emit: fallback".into())
                .or_default() += fallback_began.elapsed().as_nanos() as u64;
            // What the fallback reached is expanded in turn.
            if out.queue.is_empty() {
                break;
            }
        }
        {
            let mut stats = e.stats.borrow_mut();
            stats.emit.productions = prods.len() as u64;
            stats.emit.nanos = began.elapsed().as_nanos() as u64;
            stats
                .phases
                .insert("emit".into(), began.elapsed().as_nanos() as u64);
            stats.phases.insert("emit: add".into(), out.add_nanos);
        }
        Ok(Built {
            cfg: Cfg::from_parts(out.nts, prods, cfg.lits.clone(), cfg.occs.clone()),
            start: root,
            stats: self.stats(),
            shapes,
            slots: out.slots,
            spelled: out.spelled,
        })
    }
}

/// The nonterminals emitted so far, and the labels still to expand.
struct Emit<'a, C: Context> {
    cfg: &'a Cfg,
    ctx: &'a C,
    placeholder: &'a str,
    ids: BTreeMap<(NtId, C::Label), NtId>,
    queue: VecDeque<(NtId, C::Label)>,
    nts: Vec<Nonterminal>,
    slots: Vec<usize>,
    spelled: Vec<bool>,
    /// Time spent adding productions and interning their child labels.
    add_nanos: u64,
}

impl<C: Context> Emit<'_, C> {
    /// Adds `instance` of `prod` as a production of emitted nonterminal `lhs`, interning the
    /// child labels it takes.
    fn add(
        &mut self,
        prods: &mut Vec<Production>,
        shapes: &mut Vec<Shape>,
        lhs: NtId,
        prod: &Production,
        (opts, shape): Instance<C::Label>,
    ) {
        let began = Instant::now();
        let rhs = prod
            .rhs
            .iter()
            .zip(&opts)
            .map(|(&sym, o)| match (sym, o) {
                (Sym::Nt(c), Opt::Label(cl)) => Sym::Nt(self.intern(c, cl)),
                _ => sym,
            })
            .collect();
        self.nts[lhs as usize].prods.push(prods.len() as ProdId);
        prods.push(Production {
            lhs,
            rhs,
            occ: prod.occ.clone(),
            unrefined: prod.unrefined,
            context: prod.context,
        });
        shapes.push(shape);
        self.add_nanos += began.elapsed().as_nanos() as u64;
    }

    fn intern(&mut self, nt: NtId, l: &C::Label) -> NtId {
        if let Some(&id) = self.ids.get(&(nt, l.clone())) {
            return id;
        }
        let id = self.nts.len() as NtId;
        let base = &self.cfg.nts[nt as usize];
        let spells = self.ctx.spells(&base.base, l);
        let shown = self.ctx.show(l);
        self.nts.push(Nonterminal {
            name: if shown.is_empty() {
                base.name.clone()
            } else {
                format!("{}@{shown}", base.name)
            },
            base: base.base.clone(),
            synthetic: base.synthetic,
            lexical: base.lexical,
            origin: base.origin.clone(),
            prods: Vec::new(),
            text: if spells {
                Some(self.placeholder.to_string())
            } else {
                base.text.clone()
            },
        });
        self.slots.push(self.ctx.slots(l));
        self.spelled.push(spells);
        self.ids.insert((nt, l.clone()), id);
        self.queue.push_back((nt, l.clone()));
        id
    }
}

impl Built {
    /// Names the variables of a tree of this grammar: one name per variable, in the order
    /// they first appear, `names` first and then numbered ones. `spell` derives a spelling
    /// nonterminal's subtree for a name.
    pub fn name(
        &self,
        root: &mut tree::Node,
        names: &[String],
        spell: impl Fn(NtId, &str) -> Option<tree::Node>,
    ) -> Result<()> {
        let linking = link_slots(&BuiltNode {
            built: self,
            node: root,
        })?;
        assign_names(root, linking, names, spell, |nt| self.cfg.name(nt).to_string())
    }
}

/// A node of a tree of the emitted grammar, with the tables its slots are read from.
struct BuiltNode<'a> {
    built: &'a Built,
    node: &'a tree::Node,
}

impl Linked for BuiltNode<'_> {
    fn slots(&self) -> usize {
        match self.node.sym {
            Sym::Nt(nt) => self.built.slots[nt as usize],
            Sym::Lit(_) => 0,
        }
    }

    fn spells(&self) -> bool {
        match self.node.sym {
            Sym::Nt(nt) => self.built.spelled[nt as usize],
            Sym::Lit(_) => false,
        }
    }

    fn shape(&self) -> Option<&Shape> {
        match (self.node.sym, self.node.prod) {
            (Sym::Nt(_), Some(p)) => Some(&self.built.shapes[p as usize]),
            _ => None,
        }
    }

    fn children(&self) -> Vec<Kid<'_, Self>> {
        self.node
            .children
            .iter()
            .map(|c| match c.sym {
                Sym::Lit(_) => Kid::Lit,
                Sym::Nt(_) => Kid::Node(BuiltNode {
                    built: self.built,
                    node: c,
                }),
            })
            .collect()
    }

    fn describe(&self) -> String {
        match self.node.sym {
            Sym::Nt(nt) => self.built.cfg.name(nt).to_string(),
            Sym::Lit(_) => "a literal".into(),
        }
    }
}

/// A node whose label's slots can be numbered and linked: a tree of the emitted grammar
/// ([`BuiltNode`]), or one extracted straight from the fixed point (`extract`).
pub(crate) trait Linked: Sized {
    /// The slots of the node's own label.
    fn slots(&self) -> usize;
    /// Whether the node spells its one slot's name.
    fn spells(&self) -> bool;
    /// How its production's steps link; `None` for a literal, which has no label.
    fn shape(&self) -> Option<&Shape>;
    /// Its children, one per right hand side position.
    fn children(&self) -> Vec<Kid<'_, Self>>;
    fn describe(&self) -> String;
}

/// A child of a [`Linked`] node.
pub(crate) enum Kid<'a, N> {
    Lit,
    Node(N),
    #[allow(dead_code)]
    Borrowed(&'a N),
}

/// Every slot of every partial and final label in a tree, linked as the steps say.
pub(crate) struct Linking {
    count: usize,
    pairs: Vec<(usize, usize)>,
    /// The path and own slot of every node that spells a name.
    spelling: Vec<(Vec<usize>, usize)>,
}

pub(crate) fn link_slots<N: Linked>(root: &N) -> Result<Linking> {
    let mut linking = Linking {
        count: 0,
        pairs: Vec::new(),
        spelling: Vec::new(),
    };
    walk_linked(root, &mut Vec::new(), &mut linking)?;
    Ok(linking)
}

/// Numbers the slots of `node`'s labels from `linking.count`, records which are linked and
/// which nodes spell a slot. Returns the first slot of `node`'s own label.
fn walk_linked<N: Linked>(node: &N, path: &mut Vec<usize>, linking: &mut Linking) -> Result<usize> {
    let Some(shape) = node.shape() else {
        return Ok(linking.count);
    };
    let own = linking.count;
    let slots = node.slots();
    linking.count += slots;
    if node.spells() {
        if slots != 1 {
            bail!("<{}> spells a name but has {slots} slots", node.describe());
        }
        linking.spelling.push((path.clone(), own));
        return Ok(own);
    }
    // The partial labels' slots.
    let mut partial = Vec::new();
    for &k in &shape.partial {
        partial.push(linking.count);
        linking.count += k;
    }
    for (i, child) in node.children().into_iter().enumerate() {
        path.push(i);
        let (first, child_slots) = match &child {
            Kid::Lit => (linking.count, 0),
            Kid::Node(c) => (walk_linked(c, path, linking)?, c.slots()),
            Kid::Borrowed(c) => (walk_linked(*c, path, linking)?, c.slots()),
        };
        path.pop();
        let before = shape.partial[i];
        let mut locals = BTreeMap::new();
        for (j, to) in shape.links[i].0.iter().enumerate() {
            let Some(to) = to else { continue };
            let from = if j < before {
                partial[i] + j
            } else {
                debug_assert!(j - before < child_slots);
                first + (j - before)
            };
            let to = slot_target(
                partial[i + 1],
                shape.partial[i + 1],
                *to,
                &mut locals,
                &mut linking.count,
            );
            linking.pairs.push((from, to));
        }
    }
    let last = *partial.last().unwrap();
    let mut locals = BTreeMap::new();
    for (j, to) in shape.finish.0.iter().enumerate() {
        if let Some(to) = to {
            let to = slot_target(own, slots, *to, &mut locals, &mut linking.count);
            linking.pairs.push((last + j, to));
        }
    }
    Ok(own)
}

/// Where a link's target slot is: one of the `size` slots from `base`, or a variable
/// closed in this step, numbered once per step.
fn slot_target(
    base: usize,
    size: usize,
    to: Slot,
    locals: &mut BTreeMap<Slot, usize>,
    count: &mut usize,
) -> usize {
    if (to as usize) < size {
        return base + to as usize;
    }
    *locals.entry(to).or_insert_with(|| {
        *count += 1;
        *count - 1
    })
}

/// One name per variable of `root`, in the order they first appear, `names` first and then
/// numbered ones; every spelling node is replaced by `spell` of its nonterminal and name.
pub(crate) fn assign_names(
    root: &mut tree::Node,
    linking: Linking,
    names: &[String],
    spell: impl Fn(NtId, &str) -> Option<tree::Node>,
    name_of: impl Fn(NtId) -> String,
) -> Result<()> {
    let mut sets = UnionFind::<usize>::new(linking.count);
    for (a, b) in linking.pairs {
        sets.union(a, b);
    }
    let mut given: BTreeMap<usize, String> = BTreeMap::new();
    for (path, slot) in &linking.spelling {
        let class = sets.find(*slot);
        let k = given.len();
        let name = given
            .entry(class)
            .or_insert_with(|| fresh(names, k))
            .clone();
        let mut node = &mut *root;
        for &i in path {
            node = &mut node.children[i];
        }
        let Sym::Nt(nt) = node.sym else {
            unreachable!()
        };
        let Some(spelt) = spell(nt, &name) else {
            bail!("{name:?} does not derive from <{}>", name_of(nt));
        };
        *node = spelt;
    }
    Ok(())
}

/// The `k`th name: from `names`, then numbered.
fn fresh(names: &[String], k: usize) -> String {
    match names.get(k) {
        Some(n) => n.clone(),
        None => format!("{}{}", names.first().map_or("v", String::as_str), k),
    }
}

/// Runs `ctx` over a given tree, its names deciding which slots are one variable: the node
/// where it rejects, if any.
pub fn accepts<C: Context>(ctx: &C, tree: &Plain) -> Result<(), String> {
    let (states, _) = run(ctx, tree)?;
    if states.iter().any(|(l, _)| ctx.top(l)) {
        Ok(())
    } else {
        Err(format!("{} at the top", ctx.name()))
    }
}

type Named<L> = (L, Vec<Option<String>>);

/// Applies `link` to the names of its inputs: `None` if two slots that are one variable have
/// different names, or two variables share one. Two surviving slots may share a name in a
/// partial label (a YIELD item or a WHERE beside the declaration it names: one variable the
/// finish makes one slot), not in a `finished` one, and a closed variable never shares its
/// name with one that goes on.
fn relink(
    link: &Link,
    inputs: &[Option<String>],
    slots: usize,
    finished: bool,
) -> Option<Vec<Option<String>>> {
    // Local slots, past the label's, are variables closed in this step: checked, then dropped.
    let size = link
        .0
        .iter()
        .flatten()
        .map(|s| *s as usize + 1)
        .max()
        .unwrap_or(0)
        .max(slots);
    let mut out: Vec<Option<String>> = vec![None; size];
    for (j, to) in link.0.iter().enumerate() {
        let (Some(to), Some(Some(name))) = (to, inputs.get(j)) else {
            continue;
        };
        match &out[*to as usize] {
            Some(n) if n != name => return None,
            _ => out[*to as usize] = Some(name.clone()),
        }
    }
    let surviving: BTreeSet<&String> = out[..slots].iter().flatten().collect();
    if out[slots..].iter().flatten().any(|n| surviving.contains(n)) {
        return None;
    }
    if finished && surviving.len() != out[..slots].iter().flatten().count() {
        return None;
    }
    out.truncate(slots);
    Some(out)
}

/// A node's possible labels, each with its slots' names, and the text it spells.
type Run<L> = (Vec<Named<L>>, String);

/// One option for a child in `accepts`: its label (none for a token) and its slots' names.
type Child<'a, L> = (Option<&'a L>, &'a [Option<String>]);

fn run<C: Context>(ctx: &C, node: &Plain) -> Result<Run<C::Label>, String> {
    let Plain::Def {
        name,
        synthetic,
        children,
    } = node
    else {
        return Ok((Vec::new(), node.text()));
    };
    let items: Vec<Item> = children
        .iter()
        .map(|c| match c {
            Plain::Def {
                name,
                synthetic: true,
                ..
            } => Item::Group(name),
            Plain::Def { name, .. } => Item::Def(name),
            Plain::Kw(t) | Plain::Term(t) => Item::Token(t),
            Plain::Leaf { def, .. } => Item::Prose(def),
        })
        .collect();
    let mut kids = Vec::with_capacity(children.len());
    let mut text = String::new();
    for child in children {
        let (states, t) = run(ctx, child)?;
        kids.push(states);
        text.push_str(&t);
    }
    let node = Node {
        def: name,
        group: *synthetic,
        items: &items,
        text: Some(&text),
    };
    let empty = ctx.empty(&node);
    let mut partial: Vec<Named<C::Label>> = vec![(empty.clone(), vec![None; ctx.slots(&empty)])];
    for (pos, child) in children.iter().enumerate() {
        let mut next = BTreeSet::new();
        for (l, names) in &partial {
            let options: Vec<Child<C::Label>> = match child {
                Plain::Def { .. } => kids[pos]
                    .iter()
                    .map(|(cl, cn)| (Some(cl), &cn[..]))
                    .collect(),
                _ => vec![(None, &[][..])],
            };
            for (cl, cn) in options {
                for (q, link) in ctx.push(&node, pos, l, cl) {
                    let inputs: Vec<Option<String>> = names.iter().chain(cn).cloned().collect();
                    if let Some(out) = relink(&link, &inputs, ctx.slots(&q), false) {
                        next.insert((q, out));
                    }
                }
            }
        }
        partial = next.into_iter().collect();
    }
    let mut out = BTreeSet::new();
    for (l, names) in &partial {
        for (f, link) in ctx.finish(&node, l) {
            let Some(mut named) = relink(&link, names, ctx.slots(&f), true) else {
                continue;
            };
            if ctx.spells(name, &f) && named.len() == 1 {
                named[0] = Some(text.clone());
            }
            out.insert((f, named));
        }
    }
    tracing::trace!(
        node = name.as_str(),
        text = text.as_str(),
        labels = ?out.iter().map(|(l, n)| format!("{} {n:?}", ctx.show(l))).collect::<Vec<_>>(),
        "accepts"
    );
    if out.is_empty() {
        return Err(format!("{} at <{name}>", ctx.name()));
    }
    Ok((out.into_iter().collect(), text))
}

/// No context at all: every tree accepted, one label per nonterminal. What the engine itself
/// costs.
pub struct Nothing;

impl Context for Nothing {
    type Label = ();

    fn name(&self) -> &str {
        "nothing"
    }

    fn slots(&self, _: &()) -> usize {
        0
    }

    fn empty(&self, _: &Node) {}

    fn push(&self, _: &Node, _: usize, _: &(), _: Option<&()>) -> Vec<((), Link)> {
        vec![((), Link::default())]
    }

    fn finish(&self, _: &Node, _: &()) -> Vec<((), Link)> {
        vec![((), Link::default())]
    }

    fn top(&self, _: &()) -> bool {
        true
    }

    fn spells(&self, _: &str, _: &()) -> bool {
        false
    }

    fn show(&self, _: &()) -> String {
        String::new()
    }
}
