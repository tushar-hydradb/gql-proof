//! Compiles Syntax Rules that a grammar could express into the grammar itself.
//!
//! Some Syntax Rules are not about binding or typing at all: they forbid combinations a
//! context-free grammar could rule out but ISO chose to state in prose. Each one here is a
//! deterministic tree automaton over derivation trees with two passes: an inherited state
//! flows from a node to its children, and a synthesized state from its children to it. A rule
//! may reject a node outright. The derivation trees of a context-free grammar intersected with
//! such an automaton are again the derivation trees of a context-free grammar, so `refine`
//! builds that grammar: one copy of each nonterminal per reachable pair of states, one
//! production per combination of child states the rules accept. The generator runs on it
//! unchanged and every query it builds satisfies the rules by construction.
//!
//! Nothing here is trusted. `verify` checks each rule again, directly from its text, and a
//! test makes the two agree.
//!
//! A child's inherited state may also read the synthesized states of the children left of
//! it, which is how what one statement binds reaches the next (an L-attributed grammar,
//! still finite state, still context-free once multiplied out). A rule may allow a node
//! several synthesized states, so it can choose, and fix the text of a copy: a copy of
//! `<binding variable>` is one name.
//!
//! A state is a set of facts. Each rule owns some facts: producer nodes add them, consumer
//! nodes read and remove them, so nothing leaks past the construct it belongs to. A grouping
//! node from desugaring is stepped too, with `Node::group` set; rules that do not care about
//! groups pass its children's union through.
//!
//! Reading: 16.4 SR 6 and 14 say "contain", which in ISO is transitive and would let an outer
//! graph pattern's rules reach into subqueries nested in it. We read them per depth of graph
//! pattern matching (the notion 16.4 SR 2 introduces), so each `<graph pattern>` checks and
//! clears its own facts. 13.1 SR 5 is read along the statement sequence, see
//! `DataModifyingModifies`.

use crate::MatchModeDefault;
use crate::cfg::{Cfg, Lit, Nonterminal, NtId, ProdId, Production, Sym};
use crate::verify::Plain;
use anyhow::{Result, bail};
use std::collections::{BTreeMap, BTreeSet};

/// A fact a rule tracks about a subtree or its context.
pub type Fact = u32;

/// A set of facts.
#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct State(BTreeSet<Fact>);

impl State {
    pub fn has(&self, f: Fact) -> bool {
        self.0.contains(&f)
    }

    pub fn with(mut self, f: Fact) -> State {
        self.0.insert(f);
        self
    }

    pub fn without(mut self, f: Fact) -> State {
        self.0.remove(&f);
        self
    }

    pub fn without_all(mut self, fs: &[Fact]) -> State {
        for f in fs {
            self.0.remove(f);
        }
        self
    }

    pub fn set(&mut self, f: Fact, on: bool) {
        if on {
            self.0.insert(f);
        } else {
            self.0.remove(&f);
        }
    }

    pub fn union(&self, other: &State) -> State {
        State(self.0.union(&other.0).copied().collect())
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn facts(&self) -> impl Iterator<Item = Fact> + '_ {
        self.0.iter().copied()
    }
}

/// One right hand side position, as the rules see it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Item<'a> {
    /// A reference to an ISO definition, by name.
    Def(&'a str),
    /// A desugaring group, by its synthetic name.
    Group(&'a str),
    /// A keyword or terminal, by its text.
    Token(&'a str),
    /// A prose leaf of the named definition.
    Prose(&'a str),
}

/// The node a rule is asked about: an ISO definition or a desugaring group, and its right
/// hand side.
#[derive(Debug, Clone, Copy)]
pub struct Node<'a> {
    pub def: &'a str,
    pub group: bool,
    pub items: &'a [Item<'a>],
    /// The text the subtree spells, when checking a given tree; `None` while refining, where
    /// a rule that cares chooses instead.
    pub text: Option<&'a str>,
}

pub trait Rule {
    fn name(&self) -> &str;
    fn cite(&self) -> &str;
    /// The facts this rule owns, with a label for naming refined nonterminals.
    fn labels(&self) -> Vec<(Fact, String)>;
    /// Whether this rule's facts only serve to enforce it: the states they tell apart are not
    /// contexts worth covering separately.
    fn bookkeeping(&self) -> bool {
        false
    }
    /// Adds to `out` the inherited facts of the child at `pos`, given this node's and the
    /// synthesized states of the children left of it (`left`): what a statement binds is in
    /// scope for the statements after it.
    fn down(&self, _node: &Node, _inh: &State, _pos: usize, _left: &[State], _out: &mut State) {}
    /// Whether `step` rejects `node` in this inherited context whatever its children are.
    /// Refinement then does not look below it at all.
    fn rejects(&self, _node: &Node, _inh: &State) -> bool {
        false
    }
    /// The synthesized state of `node`, from its inherited state, each position's synthesized
    /// state (empty for tokens) and `syn`: the union of those, as earlier rules left it.
    /// `None` rejects the node.
    fn step(&self, _node: &Node, _inh: &State, _children: &[State], syn: State) -> Option<State> {
        Some(syn)
    }
    /// Every synthesized state `node` may take: a rule that chooses (which name a variable
    /// is) gives several, refinement keeps a copy for each. Empty rejects the node.
    fn steps(&self, node: &Node, inh: &State, children: &[State], syn: State) -> Vec<State> {
        self.step(node, inh, children, syn).into_iter().collect()
    }
    /// The text every tree of a copy of `def` with synthesized state `syn` spells, if this
    /// rule fixes it.
    fn text(&self, _def: &str, _syn: &State) -> Option<String> {
        None
    }
}

/// Every syntax rule, in the order they apply.
pub fn all_rules(id086: MatchModeDefault) -> Vec<Box<dyn Rule>> {
    vec![
        Box::new(UnboundedNeedsGuard { id086 }),
        Box::new(KeepWithoutSearch),
        Box::new(DataModifyingModifies),
    ]
}

/// Facts at or above this are free for rules built at run time, such as feature claims.
pub const FIRST_FREE_FACT: Fact = 12;

/// 16.4 SR 14: every unbounded quantifier needs a guard.
pub struct UnboundedNeedsGuard {
    pub id086: MatchModeDefault,
}

const UNGUARDED: Fact = 0;
const UPPER: Fact = 1;
const RESTRICTIVE: Fact = 2;
const SELECTIVE: Fact = 3;
const PREFIX_GUARDS: Fact = 4;
const KEEP_GUARDS: Fact = 5;
const DIFFERENT: Fact = 6;
const MATCH_MODE: Fact = 7;
const SR14: [Fact; 8] = [
    UNGUARDED,
    UPPER,
    RESTRICTIVE,
    SELECTIVE,
    PREFIX_GUARDS,
    KEEP_GUARDS,
    DIFFERENT,
    MATCH_MODE,
];

fn labels(facts: &[(Fact, &str)]) -> Vec<(Fact, String)> {
    facts.iter().map(|&(f, l)| (f, l.to_string())).collect()
}

impl Rule for UnboundedNeedsGuard {
    fn name(&self) -> &str {
        "unbounded quantifier needs a guard"
    }

    fn cite(&self) -> &str {
        "16.4 SR 14: an unbounded quantifier is bounded, inside a restrictive path mode, inside a selective path pattern, or under DIFFERENT EDGES"
    }

    fn labels(&self) -> Vec<(Fact, String)> {
        labels(&[
            (UNGUARDED, "unguarded"),
            (UPPER, "upper"),
            (RESTRICTIVE, "restrictive"),
            (SELECTIVE, "selective"),
            (PREFIX_GUARDS, "prefix-guards"),
            (KEEP_GUARDS, "keep-guards"),
            (DIFFERENT, "different"),
            (MATCH_MODE, "match-mode"),
        ])
    }

    fn step(&self, node: &Node, _inh: &State, _children: &[State], s: State) -> Option<State> {
        if node.group {
            return Some(s);
        }
        let rhs = node.items;
        Some(match node.def {
            "upper bound" => s.with(UPPER),
            "general quantifier" if !s.has(UPPER) => s.with(UNGUARDED),
            "general quantifier" => s.without(UPPER),
            "graph pattern quantifier"
                if matches!(rhs, [Item::Def("asterisk")] | [Item::Def("plus sign")]) =>
            {
                s.with(UNGUARDED)
            }
            "path mode"
                if matches!(
                    rhs,
                    [Item::Token("TRAIL")] | [Item::Token("SIMPLE")] | [Item::Token("ACYCLIC")]
                ) =>
            {
                s.with(RESTRICTIVE)
            }
            "path search prefix" => {
                let s = if rhs == [Item::Def("all path search")] {
                    s
                } else {
                    s.with(SELECTIVE)
                };
                guards(s)
            }
            "path mode prefix" => guards(s),
            // SR 7 puts every prefix's path mode in parentheses around its expression, so a
            // guarding prefix guards everything under it.
            "parenthesized path pattern expression" | "path pattern" => {
                let s = if s.has(PREFIX_GUARDS) {
                    s.without(UNGUARDED)
                } else {
                    s
                };
                s.without(PREFIX_GUARDS)
            }
            // SR 6 applies the KEEP prefix to every path pattern of this graph pattern.
            "keep clause" if s.has(PREFIX_GUARDS) => s.without(PREFIX_GUARDS).with(KEEP_GUARDS),
            "different edges match mode" => s.with(DIFFERENT),
            "match mode" => s.with(MATCH_MODE),
            "graph pattern" => {
                let default = !s.has(MATCH_MODE) && self.id086 == MatchModeDefault::DifferentEdges;
                let guarded = s.has(DIFFERENT) || s.has(KEEP_GUARDS) || default;
                if s.has(UNGUARDED) && !guarded {
                    return None;
                }
                s.without_all(&SR14)
            }
            _ => s,
        })
    }
}

/// A path mode or search prefix that guards: restrictive or selective.
fn guards(s: State) -> State {
    let guard = s.has(RESTRICTIVE) || s.has(SELECTIVE);
    let mut s = s.without(RESTRICTIVE).without(SELECTIVE);
    s.set(PREFIX_GUARDS, guard);
    s
}

/// 16.4 SR 6: with a KEEP clause, no path pattern has its own path search prefix.
pub struct KeepWithoutSearch;

const SEARCH_HERE: Fact = 8;
const PATTERN_SEARCH: Fact = 9;
const KEEP: Fact = 10;
const SR6: [Fact; 3] = [SEARCH_HERE, PATTERN_SEARCH, KEEP];

impl Rule for KeepWithoutSearch {
    fn name(&self) -> &str {
        "no search prefix under KEEP"
    }

    fn cite(&self) -> &str {
        "16.4 SR 6: with a <keep clause>, no <path pattern> contains a <path search prefix>"
    }

    fn labels(&self) -> Vec<(Fact, String)> {
        labels(&[
            (SEARCH_HERE, "search-here"),
            (PATTERN_SEARCH, "pattern-search"),
            (KEEP, "keep"),
        ])
    }

    fn step(&self, node: &Node, _inh: &State, _children: &[State], s: State) -> Option<State> {
        if node.group {
            return Some(s);
        }
        Some(match node.def {
            "path search prefix" => s.with(SEARCH_HERE),
            "path pattern" if s.has(SEARCH_HERE) => s.without(SEARCH_HERE).with(PATTERN_SEARCH),
            // The KEEP clause's own prefix is the one allowed search prefix.
            "keep clause" => s.without(SEARCH_HERE).with(KEEP),
            "graph pattern" => {
                if s.has(KEEP) && s.has(PATTERN_SEARCH) {
                    return None;
                }
                s.without_all(&SR6)
            }
            _ => s,
        })
    }
}

/// 13.1 SR 5: a linear data-modifying statement modifies something.
///
/// Reading: the statement sequence has an element that is a simple data-modifying statement,
/// or is a nested `{ ... }` data-modifying procedure that satisfies this itself (13.1's
/// Function: "a linear composition of at least one <simple data-modifying statement>").
/// A data-modifying statement buried in a subquery somewhere else does not count, so the fact
/// only travels up this statement spine and is cleared everywhere else.
pub struct DataModifyingModifies;

const SPINE: &[&str] = &[
    "simple data-accessing statement",
    "simple linear data-accessing statement",
    "ambient linear data-modifying statement body",
    "focused linear data-modifying statement body",
    "ambient linear data-modifying statement",
    "focused linear data-modifying statement",
    "focused nested data-modifying procedure specification",
    "nested data-modifying procedure specification",
    "data-modifying procedure specification",
    "procedure body",
    "statement block",
    "next statement",
    "statement",
];

const MODIFIES: Fact = 11;

impl Rule for DataModifyingModifies {
    fn name(&self) -> &str {
        "data-modifying statement modifies"
    }

    fn cite(&self) -> &str {
        "13.1 SR 5: a <linear data-modifying statement> contains a <simple data-modifying statement>"
    }

    fn labels(&self) -> Vec<(Fact, String)> {
        labels(&[(MODIFIES, "modifies")])
    }

    fn step(&self, node: &Node, _inh: &State, _children: &[State], s: State) -> Option<State> {
        if node.group {
            return Some(s);
        }
        match node.def {
            "simple data-modifying statement" => Some(s.with(MODIFIES)),
            "linear data-modifying statement" if !s.has(MODIFIES) => None,
            // Passed on so an enclosing statement whose element is a nested procedure sees it.
            "linear data-modifying statement" => Some(s),
            d if SPINE.contains(&d) => Some(s),
            _ => Some(s.without(MODIFIES)),
        }
    }
}

fn down_all(
    rules: &[Box<dyn Rule>],
    node: &Node,
    inh: &State,
    pos: usize,
    left: &[State],
) -> State {
    let mut out = State::default();
    for r in rules {
        r.down(node, inh, pos, left, &mut out);
    }
    out
}

/// Every synthesized state the rules allow `node`, each rule applied to every state the
/// rules before it left.
fn step_all(
    rules: &[Box<dyn Rule>],
    node: &Node,
    inh: &State,
    children: &[State],
) -> BTreeSet<State> {
    let union = children.iter().fold(State::default(), |a, c| a.union(c));
    let mut states = BTreeSet::from([union]);
    for r in rules {
        states = states
            .into_iter()
            .flat_map(|s| r.steps(node, inh, children, s))
            .collect();
    }
    states
}

/// Above this many child-state combinations for one production, refinement gives up rather
/// than build an unreasonable grammar.
const MAX_TUPLES: usize = 1 << 20;

/// The refined grammar and its start symbol.
pub struct Refined {
    pub cfg: Cfg,
    pub start: NtId,
}

/// A nonterminal of the grammar being refined, in one inherited context.
type Ctx = (NtId, State);

/// One refinement under way: the contexts found so far, the productions each keeps, the
/// synthesized states found so far, and which productions read each context.
struct Refiner<'c, 'r> {
    cfg: &'c Cfg,
    rules: &'r [Box<dyn Rule>],
    items: Vec<Vec<Item<'c>>>,
    /// The start symbol, when nothing uses it: its synthesized state is never consumed, so
    /// it is forgotten, which keeps one start.
    forget: Option<NtId>,
    index: BTreeMap<Ctx, usize>,
    contexts: Vec<Ctx>,
    prods: Vec<Vec<ProdId>>,
    states: Vec<BTreeSet<State>>,
    users: Vec<BTreeSet<(usize, usize)>>,
    work: Vec<(usize, usize)>,
    queued: BTreeSet<(usize, usize)>,
}

/// A production's children in one context: the context of each nonterminal position, and
/// the synthesized state each takes.
type Tuple = (Vec<Option<usize>>, Vec<State>);

impl<'c, 'r> Refiner<'c, 'r> {
    fn new(cfg: &'c Cfg, rules: &'r [Box<dyn Rule>], start: NtId) -> Self {
        let used = cfg.prods.iter().any(|p| p.rhs.contains(&Sym::Nt(start)));
        Refiner {
            cfg,
            rules,
            items: cfg.prods.iter().map(|p| items_of(cfg, p)).collect(),
            forget: (!used).then_some(start),
            index: BTreeMap::new(),
            contexts: Vec::new(),
            prods: Vec::new(),
            states: Vec::new(),
            users: Vec::new(),
            work: Vec::new(),
            queued: BTreeSet::new(),
        }
    }

    fn node(&self, p: ProdId) -> Node<'_> {
        let lhs = &self.cfg.nts[self.cfg.prods[p as usize].lhs as usize];
        Node {
            def: &lhs.base,
            group: lhs.synthetic,
            items: &self.items[p as usize],
            text: None,
        }
    }

    /// The context's index, adding it, with the productions no rule rejects in it, and
    /// queueing them, if it is new.
    fn intern(&mut self, ctx: Ctx) -> usize {
        if let Some(&x) = self.index.get(&ctx) {
            return x;
        }
        let (nt, inh) = &ctx;
        let kept: Vec<ProdId> = self.cfg.nts[*nt as usize]
            .prods
            .iter()
            .copied()
            .filter(|&p| !self.rules.iter().any(|r| r.rejects(&self.node(p), inh)))
            .collect();
        let x = self.contexts.len();
        for slot in 0..kept.len() {
            self.queued.insert((x, slot));
            self.work.push((x, slot));
        }
        self.index.insert(ctx.clone(), x);
        self.contexts.push(ctx);
        self.prods.push(kept);
        self.states.push(BTreeSet::new());
        self.users.push(BTreeSet::new());
        x
    }

    /// Every combination of child states production `slot` of context `x` can take with the
    /// states found so far, left to right, each child in the context its left siblings give
    /// it. Registers `(x, slot)` as a reader of every context it looks at. Ordered with the
    /// first position varying fastest.
    fn tuples(&mut self, x: usize, slot: usize) -> Result<Vec<Tuple>> {
        let p = self.prods[x][slot];
        let inh = self.contexts[x].1.clone();
        let rhs = self.cfg.prods[p as usize].rhs.clone();
        // Each partial tuple keeps the index of every state in its context's set, to order by.
        let mut partial: Vec<(Vec<Option<usize>>, Vec<State>, Vec<usize>)> =
            vec![(Vec::new(), Vec::new(), Vec::new())];
        for (pos, sym) in rhs.iter().enumerate() {
            let mut next = Vec::new();
            for (kids, states, order) in partial {
                match *sym {
                    Sym::Lit(_) => {
                        let mut t = (kids, states, order);
                        t.0.push(None);
                        t.1.push(State::default());
                        t.2.push(0);
                        next.push(t);
                    }
                    Sym::Nt(c) => {
                        let inh_c = down_all(self.rules, &self.node(p), &inh, pos, &states);
                        let k = self.intern((c, inh_c));
                        self.users[k].insert((x, slot));
                        for (i, s) in self.states[k].iter().enumerate() {
                            let mut t = (kids.clone(), states.clone(), order.clone());
                            t.0.push(Some(k));
                            t.1.push(s.clone());
                            t.2.push(i);
                            next.push(t);
                        }
                    }
                }
            }
            if next.len() > MAX_TUPLES {
                bail!(
                    "refinement would need more than {MAX_TUPLES} child-state combinations in {}",
                    crate::describe(self.cfg, p)
                );
            }
            partial = next;
        }
        partial.sort_by(|a, b| a.2.iter().rev().cmp(b.2.iter().rev()));
        Ok(partial.into_iter().map(|(k, s, _)| (k, s)).collect())
    }

    fn state_of(&self, p: ProdId, inh: &State, children: &[State]) -> BTreeSet<State> {
        let states = step_all(self.rules, &self.node(p), inh, children);
        if self.forget == Some(self.cfg.prods[p as usize].lhs) && !states.is_empty() {
            BTreeSet::from([State::default()])
        } else {
            states
        }
    }
}

/// The grammar whose derivation trees are exactly `cfg`'s that every rule accepts.
pub fn refine(cfg: &Cfg, rules: &[Box<dyn Rule>], start: NtId) -> Result<Refined> {
    let mut r = Refiner::new(cfg, rules, start);
    // Every nonterminal is a root with nothing inherited, so the parts of the grammar the
    // start does not reach keep a copy, as without rules.
    for nt in 0..cfg.nts.len() as NtId {
        r.intern((nt, State::default()));
    }
    let root = r.index[&(start, State::default())];

    // Synthesized states per context: a least fixed point, bottom-up, revisiting a production
    // only when a context it reads gained a state. A child's context depends on the states of
    // the children left of it, so contexts are found along the way.
    while let Some((x, slot)) = r.work.pop() {
        r.queued.remove(&(x, slot));
        let p = r.prods[x][slot];
        let found = r.tuples(x, slot)?;
        let mut grew = false;
        for (_, children) in found {
            for s in r.state_of(p, &r.contexts[x].1.clone(), &children) {
                grew |= r.states[x].insert(s);
            }
        }
        if grew {
            for &u in &r.users[x].clone() {
                if r.queued.insert(u) {
                    r.work.push(u);
                }
            }
        }
    }

    let labels: BTreeMap<Fact, String> = rules.iter().flat_map(|r| r.labels()).collect();
    let mut ids: BTreeMap<(usize, State), NtId> = BTreeMap::new();
    let mut nts = Vec::new();
    for (x, (nt, inh)) in r.contexts.iter().enumerate() {
        let nt = &cfg.nts[*nt as usize];
        for syn in &r.states[x] {
            ids.insert((x, syn.clone()), nts.len() as NtId);
            nts.push(Nonterminal {
                name: copy_name(&nt.name, inh, syn, &labels),
                base: nt.base.clone(),
                synthetic: nt.synthetic,
                lexical: nt.lexical,
                origin: nt.origin.clone(),
                prods: Vec::new(),
                text: rules
                    .iter()
                    .find_map(|r| r.text(&nt.base, syn))
                    .or_else(|| nt.text.clone()),
            });
        }
    }
    // A production's context: its own, and the states around it with bookkeeping facts left
    // out, so copies that only carry bookkeeping count as one for coverage.
    let bookkeeping: BTreeSet<Fact> = rules
        .iter()
        .filter(|r| r.bookkeeping())
        .flat_map(|r| r.labels().into_iter().map(|(f, _)| f))
        .collect();
    let visible =
        |s: &State| -> Vec<Fact> { s.facts().filter(|f| !bookkeeping.contains(f)).collect() };
    // (the production's context, inherited, synthesized, the children's), all visible only
    type Key = (u32, Vec<Fact>, Vec<Fact>, Vec<Vec<Fact>>);
    let mut classes: BTreeMap<Key, u32> = BTreeMap::new();
    let mut prods = Vec::new();
    for x in 0..r.contexts.len() {
        let inh = r.contexts[x].1.clone();
        for slot in 0..r.prods[x].len() {
            let p = r.prods[x][slot];
            let prod = &cfg.prods[p as usize];
            for (kids, children) in r.tuples(x, slot)? {
                for s in r.state_of(p, &inh, &children) {
                    let key = (
                        prod.context,
                        visible(&inh),
                        visible(&s),
                        children.iter().map(visible).collect(),
                    );
                    let next = classes.len() as u32;
                    let context = *classes.entry(key).or_insert(next);
                    let lhs = ids[&(x, s)];
                    let rhs = prod
                        .rhs
                        .iter()
                        .zip(&kids)
                        .zip(&children)
                        .map(|((&sym, k), cs)| match k {
                            Some(k) => Sym::Nt(ids[&(*k, cs.clone())]),
                            None => sym,
                        })
                        .collect();
                    nts[lhs as usize].prods.push(prods.len() as ProdId);
                    prods.push(Production {
                        lhs,
                        rhs,
                        occ: prod.occ.clone(),
                        unrefined: prod.unrefined,
                        context,
                    });
                }
            }
        }
    }
    let Some(first) = r.states[root].iter().next() else {
        bail!("the rules reject every tree from <{}>", cfg.name(start));
    };
    if r.states[root].len() > 1 {
        bail!(
            "<{}> is recursive and ends in several states",
            cfg.name(start)
        );
    }
    Ok(Refined {
        start: ids[&(root, first.clone())],
        cfg: Cfg::from_parts(nts, prods, cfg.lits.clone(), cfg.occs.clone()),
    })
}

fn items_of<'c>(cfg: &'c Cfg, p: &Production) -> Vec<Item<'c>> {
    p.rhs
        .iter()
        .map(|&sym| match sym {
            Sym::Nt(c) if cfg.nts[c as usize].synthetic => Item::Group(cfg.base(c)),
            Sym::Nt(c) => Item::Def(cfg.base(c)),
            Sym::Lit(l) => match &cfg.lits[l as usize] {
                Lit::Kw(t) | Lit::Term(t) => Item::Token(t),
                Lit::Opaque(d) => Item::Prose(d),
            },
        })
        .collect()
}

fn copy_name(name: &str, inh: &State, syn: &State, labels: &BTreeMap<Fact, String>) -> String {
    let set = |s: &State| -> Vec<&str> {
        s.facts()
            .map(|f| labels.get(&f).map_or("?", String::as_str))
            .collect()
    };
    let mut out = name.to_string();
    if !syn.is_empty() {
        out = format!("{out}@{}", set(syn).join("+"));
    }
    if !inh.is_empty() {
        out = format!("{out}^{}", set(inh).join("+"));
    }
    out
}

/// Runs the rules over one tree: the first rule to reject a node, if any.
pub fn accepts(rules: &[Box<dyn Rule>], tree: &Plain) -> Result<(), String> {
    run(rules, tree, &State::default()).map(|_| ())
}

/// The synthesized state of `node` and the text it spells. Where a rule allows several
/// states, the text decides (a rule that chooses a name reads it), and the first is kept.
fn run(rules: &[Box<dyn Rule>], node: &Plain, inh: &State) -> Result<(State, String), String> {
    let Plain::Def {
        name,
        synthetic,
        children,
    } = node
    else {
        return Ok((State::default(), node.text()));
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
    let mut here = Node {
        def: name,
        group: *synthetic,
        items: &items,
        text: None,
    };
    let mut states = Vec::with_capacity(children.len());
    let mut text = String::new();
    for (pos, child) in children.iter().enumerate() {
        let (s, t) = run(rules, child, &down_all(rules, &here, inh, pos, &states))?;
        states.push(s);
        text.push_str(&t);
    }
    here.text = Some(&text);
    let mut s = states.iter().fold(State::default(), |a, c| a.union(c));
    for rule in rules {
        s = rule
            .steps(&here, inh, &states, s)
            .into_iter()
            .next()
            .ok_or_else(|| format!("{} at <{name}>", rule.name()))?;
    }
    Ok((s, text))
}
