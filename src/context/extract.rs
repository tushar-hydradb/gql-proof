//! One ground tree per coverage target, read out of the fixed point. No grammar is emitted.
//!
//! The totality argument (`research/totality-2026-10-21.md`) needs, per target, one valid
//! tree or the fact that none exists at the cap. Emission answered a bigger question (an
//! instance for every reachable label in every position, made ground) so that purdom could
//! run on the result; at three variables that was the wall. Here a target's tree is found by
//! one search: a ground tree for its node ([`Extractor::witness`], bottom up) and a ground
//! context from that node to the top ([`Extractor::up`], parent by parent), both memoised per
//! (nonterminal, ground label) and shared across targets. Ground reachability is computed
//! only for the ground labels the targets' searches touch.
//!
//! A ground label has every variable's set a single class. With joins off every label is
//! ground, `within` is equality and `grounds` is identity, and the searches are back-pointer
//! walks. With joins on, the fixed point's labels are live (joined) or made (a production's
//! finish output): `ends` and `smallest` speak made labels, options in layers speak live
//! labels, `parts` maps a live label to its made labels, and the searches ground lazily.
//!
//! The search is complete: at every level the wide completion enumeration of
//! `Engine::ground` is exhaustive over ground candidates and `users` lists every parent, so
//! a target with no tree found has none at the cap, by exhaustion.

use super::{
    AheadTable, Context, Ends, Engine, Instance, Kid, Layers, Linked, Opt, Shape,
    assign_names, link_slots,
};
use crate::cfg::{Cfg, Lit, NtId, OccId, ProdId, Sym};
use crate::coverage::{self, Criteria, ROOT, Target};
use crate::leaf::LeafProvider;
use crate::tree;
use anyhow::Result;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use std::cell::{Cell, OnceCell, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;
use std::time::Instant;

/// A production's tables: its kept partial layers, the labels it makes, and on first use
/// the backward table of cheapest completions.
struct Prepared<L> {
    layers: Layers<L>,
    ends: Ends<L>,
    ahead: OnceCell<AheadTable<L>>,
}

/// A node of an extracted tree: its production, its ground label, how its instance's slots
/// link, and its children.
pub struct XNode<L> {
    pub prod: ProdId,
    pub label: L,
    shape: Shape,
    pub children: Vec<XChild<L>>,
}

pub enum XChild<L> {
    Lit,
    Node(Rc<XNode<L>>),
}

/// A ground context: the chain of parents from a node up to the top, each a ground instance
/// with the level below at position `j`.
enum Ctx<L> {
    Top,
    Under {
        q: ProdId,
        j: usize,
        instance: Instance<L>,
        out: L,
        above: Rc<Ctx<L>>,
    },
}

/// What the searches spent.
#[derive(Debug, Clone, Default)]
pub struct ExtractStats {
    pub witness_searches: u64,
    pub context_searches: u64,
    pub witness_failed: u64,
    pub context_failed: u64,
    /// Per nonterminal: failed witness and context searches.
    pub failed_by_nt: BTreeMap<NtId, (u64, u64)>,
    pub ahead_tables: u64,
    pub ahead_nanos: u64,
    pub search_nanos: u64,
}

/// The outcome for one kind of target.
#[derive(Debug, Clone, Default)]
pub struct Kind {
    pub total: usize,
    pub covered: usize,
    /// Targets no tree exists for at the cap.
    pub never: Vec<String>,
}

/// What `cover` found: the trees, one per target it was extracted for, and the tally.
pub struct Covered {
    pub trees: Vec<(tree::Node, String)>,
    pub productions: Kind,
    pub cdrc: Kind,
    pub stats: ExtractStats,
}

pub struct Extractor<'e, 'a, C: Context> {
    e: &'e Engine<'a, C>,
    start: NtId,
    prepared: Vec<Prepared<C::Label>>,
    /// Per production: whether the leaf provider fills every prose leaf on its right hand
    /// side. The others are never used, as purdom never uses them.
    fillable: Vec<bool>,
    /// Per nonterminal: each made label and the productions that make it.
    makers: Vec<BTreeMap<C::Label, Vec<ProdId>>>,
    witnesses: RefCell<BTreeMap<(NtId, C::Label), Option<Rc<XNode<C::Label>>>>>,
    contexts: RefCell<BTreeMap<(NtId, C::Label), Option<Rc<Ctx<C::Label>>>>>,
    /// The searches in progress (true for a context search), and the shallowest one the
    /// current search ran into: a failure that depended on one is conditional on it.
    stack: RefCell<Vec<Key<C::Label>>>,
    lowest: Cell<usize>,
    /// For progress lines: when the extractor was made, and when it last reported.
    began: Instant,
    said: Cell<Option<Instant>>,
    /// Failures conditional on a search in progress: the depth of the shallowest one they
    /// ran into and the search that was there. While it is still there they fail again; when
    /// it fails they are settled; when it succeeds they are forgotten.
    conditional: RefCell<BTreeMap<Key<C::Label>, (usize, Key<C::Label>)>>,
    by_depth: RefCell<BTreeMap<usize, Vec<Key<C::Label>>>>,
    stats: RefCell<ExtractStats>,
}

type Key<L> = (bool, NtId, L);

impl<'e, 'a, C: Context> Extractor<'e, 'a, C> {
    pub(super) fn new(e: &'e Engine<'a, C>, start: NtId, leaf: &dyn LeafProvider) -> Self {
        let began = Instant::now();
        let cfg = e.cfg;
        let fillable: Vec<bool> = cfg
            .prods
            .iter()
            .map(|prod| {
                prod.rhs.iter().all(|sym| match sym {
                    Sym::Lit(l) => match &cfg.lits[*l as usize] {
                        Lit::Opaque(name) => leaf.supports(name),
                        _ => true,
                    },
                    Sym::Nt(_) => true,
                })
            })
            .collect();
        let prepared: Vec<Prepared<C::Label>> = (0..cfg.prods.len() as ProdId)
            .map(|p| {
                let layers = e.kept_layers(p);
                let ends = e.ends(p, &layers);
                Prepared {
                    layers,
                    ends,
                    ahead: OnceCell::new(),
                }
            })
            .collect();
        let mut makers: Vec<BTreeMap<C::Label, Vec<ProdId>>> = vec![BTreeMap::new(); cfg.nts.len()];
        for (p, pre) in prepared.iter().enumerate() {
            let lhs = cfg.prods[p].lhs as usize;
            for r in pre.ends.keys() {
                makers[lhs].entry(r.clone()).or_default().push(p as ProdId);
            }
        }
        if e.options.progress {
            eprintln!(
                "extraction: layers and made labels of {} productions ({} made labels) in {:?}",
                prepared.len(),
                prepared.iter().map(|p| p.ends.len()).sum::<usize>(),
                began.elapsed()
            );
        }
        Extractor {
            e,
            start,
            prepared,
            fillable,
            makers,
            witnesses: RefCell::new(BTreeMap::new()),
            contexts: RefCell::new(BTreeMap::new()),
            stack: RefCell::new(Vec::new()),
            lowest: Cell::new(usize::MAX),
            began: Instant::now(),
            said: Cell::new(None),
            conditional: RefCell::new(BTreeMap::new()),
            by_depth: RefCell::new(BTreeMap::new()),
            stats: RefCell::new(ExtractStats::default()),
        }
    }

    fn cfg(&self) -> &'a Cfg {
        self.e.cfg
    }

    fn ahead(&self, p: ProdId) -> &AheadTable<C::Label> {
        let pre = &self.prepared[p as usize];
        pre.ahead.get_or_init(|| {
            let began = Instant::now();
            let table = self.e.ahead(p, &pre.layers, |_| true);
            let mut stats = self.stats.borrow_mut();
            stats.ahead_tables += 1;
            stats.ahead_nanos += began.elapsed().as_nanos() as u64;
            table
        })
    }

    /// A memoised search for `(nt, g)`: the memo's value if there is one; `None` without
    /// recording when the same search is already in progress (a tree through a repeated
    /// label is never the smallest, so for this search it is a dead end), or when it failed
    /// before conditionally on a search still in progress; else `compute`. A success is
    /// recorded. A failure is recorded if it ran into no search in progress above this one;
    /// otherwise it is conditional on the shallowest it ran into. When a search fails having
    /// run into nothing above itself, every failure conditional on it or on anything deeper
    /// is settled; when it succeeds, they are forgotten (Tarjan's strongly connected
    /// components, found as the search goes).
    fn search<T: Clone>(
        &self,
        memo: &RefCell<BTreeMap<(NtId, C::Label), Option<T>>>,
        context: bool,
        nt: NtId,
        g: &C::Label,
        compute: impl FnOnce() -> Option<T>,
    ) -> Option<T> {
        if let Some(v) = memo.borrow().get(&(nt, g.clone())) {
            return v.clone();
        }
        if let Some(said) = self.said.get()
            && said.elapsed().as_secs() >= 5
        {
            let s = self.stats.borrow();
            let g = self.e.stats.borrow().emit.clone();
            let mut worst: Vec<(&NtId, &(u64, u64))> = s.failed_by_nt.iter().collect();
            worst.sort_by_key(|(_, (w, c))| std::cmp::Reverse(w + c));
            let worst: Vec<String> = worst
                .iter()
                .take(5)
                .map(|(nt, (w, c))| format!("<{}> {w}w/{c}c", self.cfg().name(**nt)))
                .collect();
            eprintln!(
                "searching: witness {} ({} failed), context {} ({} failed), {} in progress, {} ahead tables; ground {} narrow / {} wide / {} failed, candidates {} ({} no witness, {} no context, {} narrowed), {:?}\n  failing most: {}",
                s.witness_searches,
                s.witness_failed,
                s.context_searches,
                s.context_failed,
                self.stack.borrow().len(),
                s.ahead_tables,
                g.ground_narrow,
                g.ground_wide,
                g.ground_failed,
                g.ground_candidates,
                g.ground_child_rejected,
                g.ground_accept_rejected,
                g.ground_narrowed,
                self.began.elapsed(),
                worst.join(", ")
            );
            self.said.set(Some(Instant::now()));
        }
        let key = (context, nt, g.clone());
        let depth = {
            let stack = self.stack.borrow();
            if let Some(i) = stack.iter().position(|k| *k == key) {
                self.lowest.set(self.lowest.get().min(i));
                return None;
            }
            if let Some((h, k)) = self.conditional.borrow().get(&key)
                && stack.get(*h) == Some(k)
            {
                self.lowest.set(self.lowest.get().min(*h));
                return None;
            }
            stack.len()
        };
        self.stack.borrow_mut().push(key.clone());
        if depth == 200 && std::env::var("GQL_DEBUG_STACK").is_ok() {
            // Once: what a deep chain is made of, as runs of nonterminals.
            let stack = self.stack.borrow();
            let mut runs: Vec<(String, usize, bool)> = Vec::new();
            for (c, n, g) in stack.iter().take(40) {
                let name = format!("{} [{}]", self.cfg().name(*n), self.e.ctx.show(g));
                match runs.last_mut() {
                    Some((last, count, lc)) if *last == name && *lc == *c => *count += 1,
                    _ => runs.push((name, 1, *c)),
                }
            }
            let shown: Vec<String> = runs
                .iter()
                .map(|(n, k, c)| format!("{}{n}×{k}", if *c { "ctx " } else { "" }))
                .collect();
            eprintln!("stack at depth 200:\n  {}", shown.join("\n  "));
        }
        let saved = self.lowest.replace(usize::MAX);
        let v = compute();
        self.stack.borrow_mut().pop();
        if v.is_none() {
            let mut s = self.stats.borrow_mut();
            let failed = s.witness_failed + s.context_failed;
            if std::env::var("GQL_DEBUG_FAILS")
                .ok()
                .and_then(|n| n.parse::<u64>().ok())
                .is_some_and(|n| failed < n)
            {
                eprintln!(
                    "failed {} search #{failed}: <{}> [{}] (hit {}, depth {})",
                    if context { "context" } else { "witness" },
                    self.cfg().name(nt),
                    self.e.ctx.show(g),
                    self.lowest.get(),
                    self.stack.borrow().len()
                );
            }
            if context {
                s.context_failed += 1;
            } else {
                s.witness_failed += 1;
            }
            let by = s.failed_by_nt.entry(nt).or_default();
            if context {
                by.1 += 1;
            } else {
                by.0 += 1;
            }
        }
        let hit = self.lowest.get();
        if v.is_some() || hit >= depth {
            memo.borrow_mut().insert((nt, g.clone()), v.clone());
            // Failures conditional on this search or on deeper ones, all finished now.
            let settled = self.by_depth.borrow_mut().split_off(&depth);
            let settled: Vec<Key<C::Label>> = {
                let mut conditional = self.conditional.borrow_mut();
                settled
                    .into_values()
                    .flatten()
                    .filter(|k| conditional.remove(k).is_some())
                    .collect()
            };
            if v.is_none() {
                for (c, n, l) in settled {
                    if c {
                        self.contexts.borrow_mut().insert((n, l), None);
                    } else {
                        self.witnesses.borrow_mut().insert((n, l), None);
                    }
                }
            }
        } else {
            let at = self.stack.borrow()[hit].clone();
            self.conditional.borrow_mut().insert(key.clone(), (hit, at));
            self.by_depth.borrow_mut().entry(hit).or_default().push(key);
        }
        // A hit into this search is settled here; one into a search above is theirs.
        self.lowest
            .set(saved.min(if hit < depth { hit } else { usize::MAX }));
        v
    }

    /// The smallest ground tree of `nt` whose label `g` lies within.
    pub fn witness(&self, nt: NtId, g: &C::Label) -> Option<Rc<XNode<C::Label>>> {
        self.search(&self.witnesses, false, nt, g, || {
            self.stats.borrow_mut().witness_searches += 1;
            let mut candidates: Vec<(u64, ProdId, &C::Label)> = Vec::new();
            for &p in &self.cfg().nts[nt as usize].prods {
                if !self.fillable[p as usize] {
                    continue;
                }
                for (r, (cost, _, _)) in &self.prepared[p as usize].ends {
                    if self.e.ctx.within(g, r) {
                        candidates.push((*cost, p, r));
                    }
                }
            }
            candidates.sort_by(|a, b| a.0.cmp(&b.0).then(a.1.cmp(&b.1)));
            let debug = std::env::var("GQL_DEBUG_NT").is_ok_and(|n| n == self.cfg().name(nt));
            let shown: Vec<String> = if debug {
                candidates
                    .iter()
                    .map(|(c, p, r)| {
                        let pre = &self.prepared[*p as usize];
                        let opts = self
                            .e
                            .smallest(*p, &pre.layers, &pre.ends, r)
                            .map(|(opts, _)| {
                                opts.iter()
                                    .map(|o| match o {
                                        Opt::Token => "tok".to_string(),
                                        Opt::Label(l) => format!("[{}]", self.e.ctx.show(l)),
                                    })
                                    .collect::<Vec<_>>()
                                    .join(" ")
                            })
                            .unwrap_or_default();
                        format!("{c} {} [{}]\n      from {opts}", crate::describe(self.cfg(), *p), self.e.ctx.show(r))
                    })
                    .collect()
            } else {
                Vec::new()
            };
            let found = candidates
                .into_iter()
                .find_map(|(_, p, r)| self.witness_with(p, r, g));
            if debug && found.is_none() {
                eprintln!(
                    "no witness for <{}> within [{}]; made labels tried:\n  {}",
                    self.cfg().name(nt),
                    self.e.ctx.show(g),
                    shown.join("\n  ")
                );
            }
            found
        })
    }

    /// A ground tree of production `p` from its made label `r`, with a label `g` lies within.
    fn witness_with(&self, p: ProdId, r: &C::Label, g: &C::Label) -> Option<Rc<XNode<C::Label>>> {
        if !self.fillable[p as usize] {
            return None;
        }
        let pre = &self.prepared[p as usize];
        let instance = self.e.smallest(p, &pre.layers, &pre.ends, r)?;
        let (ground, out) = self.e.ground(
            p,
            &instance,
            None,
            &|l| self.e.ctx.within(g, l),
            &|pos, o| self.child_ok(p, pos, o),
            Some(g),
            &[false, true],
        )?;
        Some(self.node_of(p, ground, out, None))
    }

    /// Whether ground option `o` at `pos` of `p` has a witness (a token always does).
    fn child_ok(&self, p: ProdId, pos: usize, o: &Opt<C::Label>) -> bool {
        match o {
            Opt::Token => true,
            Opt::Label(l) => {
                let Sym::Nt(c) = self.cfg().prods[p as usize].rhs[pos] else {
                    unreachable!()
                };
                self.witness(c, l).is_some()
            }
        }
    }

    /// The node of a ground instance of `p`: its children are their witnesses, except the one
    /// `at` gives.
    fn node_of(
        &self,
        p: ProdId,
        (opts, shape): Instance<C::Label>,
        out: C::Label,
        at: Option<(usize, Rc<XNode<C::Label>>)>,
    ) -> Rc<XNode<C::Label>> {
        let rhs = &self.cfg().prods[p as usize].rhs;
        let children = opts
            .iter()
            .enumerate()
            .map(|(i, o)| match o {
                Opt::Token => XChild::Lit,
                Opt::Label(l) => {
                    if let Some((j, node)) = &at
                        && *j == i
                    {
                        return XChild::Node(node.clone());
                    }
                    let Sym::Nt(c) = rhs[i] else { unreachable!() };
                    XChild::Node(self.witness(c, l).expect("checked when the instance was made ground"))
                }
            })
            .collect();
        Rc::new(XNode {
            prod: p,
            label: out,
            shape,
            children,
        })
    }

    /// A ground context from a node of `nt` with label `g` to the top.
    fn up(&self, nt: NtId, g: &C::Label) -> Option<Rc<Ctx<C::Label>>> {
        self.search(&self.contexts, true, nt, g, || {
            self.stats.borrow_mut().context_searches += 1;
            if nt == self.start && (self.e.options.any_top || self.e.ctx.top(g)) {
                return Some(Rc::new(Ctx::Top));
            }
            let cfg = self.cfg();
            for &q in &self.e.users[nt as usize] {
                let prod = &cfg.prods[q as usize];
                for (j, sym) in prod.rhs.iter().enumerate() {
                    if *sym != Sym::Nt(nt) {
                        continue;
                    }
                    if let Some(ctx) = self.under(q, j, g, None) {
                        return Some(ctx);
                    }
                }
            }
            None
        })
    }

    /// A ground instance of `q` taking ground label `g` at `j` (and `child` there, if given,
    /// which the tree keeps), whose label has a context to the top: the context, with that
    /// instance at the bottom. Narrow first, each live option `g` lies within seeding the
    /// instance's own siblings; then wide, any siblings.
    fn under(
        &self,
        q: ProdId,
        j: usize,
        g: &C::Label,
        only: Option<&dyn Fn(&C::Label) -> bool>,
    ) -> Option<Rc<Ctx<C::Label>>> {
        if !self.fillable[q as usize] {
            return None;
        }
        let cfg = self.cfg();
        let prod = &cfg.prods[q as usize];
        let lhs = prod.lhs;
        let pre = &self.prepared[q as usize];
        let table = self.ahead(q);
        let accept = |out: &C::Label| self.up(lhs, out).is_some();
        let child_ok = |pos: usize, o: &Opt<C::Label>| pos == j || self.child_ok(q, pos, o);
        let fixed = Opt::Label(g.clone());
        let found = |ground: Instance<C::Label>, out: C::Label| {
            let above = self.up(lhs, &out).expect("accepted");
            Rc::new(Ctx::Under {
                q,
                j,
                instance: ground,
                out,
                above,
            })
        };
        let mut seed = None;
        for (o, size) in self.e.options(prod.rhs[j]) {
            let Opt::Label(l) = &o else { continue };
            if !self.e.ctx.within(g, l) || only.is_some_and(|f| !f(l)) {
                continue;
            }
            let Some((_, instance)) = self.e.taking(q, &pre.layers, table, j, &o, size) else {
                continue;
            };
            if let Some((ground, out)) =
                self.e
                    .ground(q, &instance, Some((j, &fixed)), &accept, &child_ok, None, &[false])
            {
                return Some(found(ground, out));
            }
            seed.get_or_insert(instance);
        }
        let seed = seed.or_else(|| {
            let (r, _) = pre.ends.iter().min_by_key(|(_, (c, _, _))| *c)?;
            self.e.smallest(q, &pre.layers, &pre.ends, r)
        })?;
        let (ground, out) = self.e.ground(q, &seed, Some((j, &fixed)), &accept, &child_ok, None, &[true])?;
        Some(found(ground, out))
    }

    /// The tree a context and the node below it make.
    fn assemble(&self, ctx: &Ctx<C::Label>, below: Rc<XNode<C::Label>>) -> Rc<XNode<C::Label>> {
        match ctx {
            Ctx::Top => below,
            Ctx::Under {
                q,
                j,
                instance,
                out,
                above,
            } => {
                let node = self.node_of(*q, instance.clone(), out.clone(), Some((*j, below)));
                self.assemble(above, node)
            }
        }
    }

    /// A tree using production `p`, if any exists at the cap.
    pub fn production_tree(&self, p: ProdId) -> Option<Rc<XNode<C::Label>>> {
        let nt = self.cfg().prods[p as usize].lhs;
        let pre = &self.prepared[p as usize];
        let mut made: Vec<(u64, &C::Label)> = pre.ends.iter().map(|(r, (c, _, _))| (*c, r)).collect();
        made.sort_by(|a, b| a.0.cmp(&b.0));
        for (_, r) in made {
            for g in self.e.ctx.grounds(r) {
                let Some(node) = self.witness_with(p, r, &g) else {
                    continue;
                };
                let Some(ctx) = self.up(nt, &node.label) else {
                    continue;
                };
                return Some(self.assemble(&ctx, node));
            }
        }
        None
    }

    /// A tree using production `p2` as the child at position `i` of production `q`, if any.
    pub fn cdrc_tree(&self, q: ProdId, i: usize, p2: ProdId) -> Option<Rc<XNode<C::Label>>> {
        let cfg = self.cfg();
        let Sym::Nt(c) = cfg.prods[q as usize].rhs[i] else {
            return None;
        };
        let pre2 = &self.prepared[p2 as usize];
        let mut made: Vec<(u64, &C::Label)> = pre2.ends.iter().map(|(r, (k, _, _))| (*k, r)).collect();
        made.sort_by(|a, b| a.0.cmp(&b.0));
        for (_, r) in made {
            for g in self.e.ctx.grounds(r) {
                let Some(child) = self.witness_with(p2, r, &g) else {
                    continue;
                };
                // Only options with a part `p2` makes seed the search; the wide search takes
                // any.
                let only = |l: &C::Label| {
                    let parts = self.e.parts[c as usize].get(l);
                    let made = parts.map_or(std::slice::from_ref(l), Vec::as_slice);
                    made.iter().any(|m| {
                        self.makers[c as usize]
                            .get(m)
                            .is_some_and(|ps| ps.contains(&p2))
                    })
                };
                let Some(ctx) = self.under(q, i, &child.label, Some(&only)) else {
                    continue;
                };
                let Ctx::Under {
                    instance, out, above, ..
                } = &*ctx
                else {
                    unreachable!()
                };
                let node = self.node_of(q, instance.clone(), out.clone(), Some((i, child)));
                return Some(self.assemble(above, node));
            }
        }
        None
    }

    /// `x` as a tree of the grammar, literals filled: keywords and terms by their text, prose
    /// leaves by `leaf` with the definitions above them; a nonterminal `template` fixes (the
    /// date and time strings, derived from their fixed text) by that derivation.
    pub fn to_tree(
        &self,
        x: &XNode<C::Label>,
        leaf: &mut dyn LeafProvider,
        template: &dyn Fn(NtId) -> Option<tree::Node>,
        rng: &mut ChaCha8Rng,
    ) -> tree::Node {
        self.to_tree_in(x, leaf, template, rng, &mut Vec::new())
    }

    fn to_tree_in(
        &self,
        x: &XNode<C::Label>,
        leaf: &mut dyn LeafProvider,
        template: &dyn Fn(NtId) -> Option<tree::Node>,
        rng: &mut ChaCha8Rng,
        above: &mut Vec<NtId>,
    ) -> tree::Node {
        let cfg = self.cfg();
        let prod = &cfg.prods[x.prod as usize];
        if let Some(fixed) = template(prod.lhs) {
            return fixed;
        }
        above.push(prod.lhs);
        let children = prod
            .rhs
            .iter()
            .zip(&x.children)
            .map(|(sym, child)| match (sym, child) {
                (Sym::Lit(l), XChild::Lit) => {
                    let text = match &cfg.lits[*l as usize] {
                        Lit::Kw(k) => k.clone(),
                        Lit::Term(t) => t.clone(),
                        Lit::Opaque(name) => {
                            let ctx: Vec<&str> = above.iter().map(|&nt| cfg.base(nt)).collect();
                            leaf.leaf(name, &ctx, rng)
                        }
                    };
                    tree::Node {
                        sym: *sym,
                        prod: None,
                        text: Some(text),
                        children: Vec::new(),
                    }
                }
                (Sym::Nt(_), XChild::Node(n)) => self.to_tree_in(n, leaf, template, rng, above),
                _ => unreachable!("a child per position"),
            })
            .collect();
        above.pop();
        tree::Node {
            sym: Sym::Nt(prod.lhs),
            prod: Some(x.prod),
            text: None,
            children,
        }
    }

    /// Names the variables of `root`, the tree of `x`, as [`super::Built::name`] does.
    pub fn name(
        &self,
        x: &XNode<C::Label>,
        root: &mut tree::Node,
        names: &[String],
        spell: impl Fn(NtId, &str) -> Option<tree::Node>,
    ) -> Result<()> {
        let linking = link_slots(&XView { x, e: self.e })?;
        assign_names(root, linking, names, spell, |nt| self.cfg().name(nt).to_string())
    }

    pub fn stats(&self) -> ExtractStats {
        self.stats.borrow().clone()
    }

    /// One tree per target not yet covered, cdrc pairs first (they cover productions on the
    /// way), each named, with what it was extracted for.
    pub fn cover(
        &self,
        criteria: Criteria,
        names: &[String],
        spell: impl Fn(NtId, &str) -> Option<tree::Node>,
        template: &dyn Fn(NtId) -> Option<tree::Node>,
        leaf: &mut dyn LeafProvider,
        seed: u64,
        progress: bool,
    ) -> Covered {
        let began = Instant::now();
        if progress {
            self.said.set(Some(Instant::now()));
        }
        let cfg = self.cfg();
        let mut rng = ChaCha8Rng::seed_from_u64(seed);
        let mut trees = Vec::new();
        let mut seen: BTreeSet<Target> = BTreeSet::new();
        let mut prods_seen: BTreeSet<ProdId> = BTreeSet::new();
        let mut said = Instant::now();
        let mut extract = |t: Option<Rc<XNode<C::Label>>>, covers: String, trees: &mut Vec<(tree::Node, String)>, seen: &mut BTreeSet<Target>, prods_seen: &mut BTreeSet<ProdId>| -> bool {
            let Some(x) = t else { return false };
            let mut root = self.to_tree(&x, leaf, template, &mut rng);
            if let Err(err) = self.name(&x, &mut root, names, &spell) {
                panic!("naming an extracted tree: {err}");
            }
            seen.extend(coverage::observe(cfg, &root, criteria));
            let mut ps = Vec::new();
            root.prods(&mut ps);
            prods_seen.extend(ps);
            trees.push((root, covers));
            true
        };
        // cdrc pairs, longest first in the sense the targeted generator uses: by target order.
        let mut cdrc = Kind::default();
        if criteria.cdrc {
            let positions = positions(cfg);
            let targets: Vec<Target> = coverage::targets(cfg, self.start, criteria)
                .into_iter()
                .filter(|t| matches!(t, Target::Cdrc(..)))
                .collect();
            cdrc.total = targets.len();
            for (n, t) in targets.iter().enumerate() {
                if progress && said.elapsed().as_secs() >= 5 {
                    eprintln!(
                        "extracting: cdrc {n} of {}, {} trees, {:?}",
                        targets.len(),
                        trees.len(),
                        began.elapsed()
                    );
                    said = Instant::now();
                }
                if seen.contains(t) {
                    continue;
                }
                let Target::Cdrc(occ, p2) = t else { unreachable!() };
                let found = if *occ == ROOT {
                    extract(
                        self.production_tree(*p2),
                        coverage::describe_target(cfg, t),
                        &mut trees,
                        &mut seen,
                        &mut prods_seen,
                    )
                } else {
                    positions
                        .get(occ)
                        .into_iter()
                        .flatten()
                        .any(|&(q, i)| {
                            extract(
                                self.cdrc_tree(q, i, *p2),
                                coverage::describe_target(cfg, t),
                                &mut trees,
                                &mut seen,
                                &mut prods_seen,
                            )
                        })
                };
                if !found {
                    cdrc.never.push(coverage::describe_target(cfg, t));
                }
            }
            cdrc.covered = targets.iter().filter(|t| seen.contains(t)).count();
        }
        // Productions.
        let reachable = reachable(cfg, self.start);
        let mut productions = Kind {
            total: reachable.len(),
            ..Kind::default()
        };
        for (n, &p) in reachable.iter().enumerate() {
            if progress && said.elapsed().as_secs() >= 5 {
                let s = self.stats.borrow();
                eprintln!(
                    "extracting: production {n} of {} ({}), {} trees, {} witness searches, {} context searches, {} ahead tables, {:?}",
                    reachable.len(),
                    crate::describe(cfg, p),
                    trees.len(),
                    s.witness_searches,
                    s.context_searches,
                    s.ahead_tables,
                    began.elapsed()
                );
                said = Instant::now();
            }
            if prods_seen.contains(&p) {
                continue;
            }
            if !extract(
                self.production_tree(p),
                crate::describe(cfg, p),
                &mut trees,
                &mut seen,
                &mut prods_seen,
            ) {
                productions.never.push(crate::describe(cfg, p));
            }
        }
        productions.covered = reachable.iter().filter(|p| prods_seen.contains(p)).count();
        let mut stats = self.stats();
        stats.search_nanos = began.elapsed().as_nanos() as u64;
        Covered {
            trees,
            productions,
            cdrc,
            stats,
        }
    }
}

/// Every (production, position) carrying each occurrence.
fn positions(cfg: &Cfg) -> BTreeMap<OccId, Vec<(ProdId, usize)>> {
    let mut out: BTreeMap<OccId, Vec<(ProdId, usize)>> = BTreeMap::new();
    for (p, prod) in cfg.prods.iter().enumerate() {
        for (i, &occ) in prod.occ.iter().enumerate() {
            if matches!(prod.rhs[i], Sym::Nt(_)) {
                out.entry(occ).or_default().push((p as ProdId, i));
            }
        }
    }
    out
}

/// The productions reachable from `start`, in id order.
fn reachable(cfg: &Cfg, start: NtId) -> Vec<ProdId> {
    let mut seen = vec![false; cfg.nts.len()];
    let mut stack = vec![start];
    let mut out = Vec::new();
    while let Some(nt) = stack.pop() {
        if std::mem::replace(&mut seen[nt as usize], true) {
            continue;
        }
        for &p in &cfg.nts[nt as usize].prods {
            out.push(p);
            for sym in &cfg.prods[p as usize].rhs {
                if let Sym::Nt(c) = sym {
                    stack.push(*c);
                }
            }
        }
    }
    out.sort_unstable();
    out
}

/// An extracted node as [`Linked`] sees it.
struct XView<'x, 'e, 'a, C: Context> {
    x: &'x XNode<C::Label>,
    e: &'e Engine<'a, C>,
}

impl<C: Context> Linked for XView<'_, '_, '_, C> {
    fn slots(&self) -> usize {
        self.e.ctx.slots(&self.x.label)
    }

    fn spells(&self) -> bool {
        let lhs = self.e.cfg.prods[self.x.prod as usize].lhs;
        self.e.ctx.spells(self.e.cfg.base(lhs), &self.x.label)
    }

    fn shape(&self) -> Option<&Shape> {
        Some(&self.x.shape)
    }

    fn children(&self) -> Vec<Kid<'_, Self>> {
        self.x
            .children
            .iter()
            .map(|c| match c {
                XChild::Lit => Kid::Lit,
                XChild::Node(n) => Kid::Node(XView { x: n, e: self.e }),
            })
            .collect()
    }

    fn describe(&self) -> String {
        let lhs = self.e.cfg.prods[self.x.prod as usize].lhs;
        self.e.cfg.name(lhs).to_string()
    }
}

impl<'a, C: Context> super::Analyzed<'a, C> {
    /// Per-target extraction over this fixed point (see [`Extractor`]).
    pub fn extractor(&self, start: NtId, leaf: &dyn LeafProvider) -> Extractor<'_, 'a, C> {
        Extractor::new(&self.e, start, leaf)
    }
}
