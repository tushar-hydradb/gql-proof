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
use anyhow::{Context, Result, bail};
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
}

pub trait Rule {
    fn name(&self) -> &str;
    fn cite(&self) -> &str;
    /// The facts this rule owns, with a label for naming refined nonterminals.
    fn labels(&self) -> Vec<(Fact, String)>;
    /// Adds to `out` the inherited facts of the child at `pos`, given this node's.
    fn down(&self, _node: &Node, _inh: &State, _pos: usize, _out: &mut State) {}
    /// The synthesized state of `node`, from its inherited state, each position's synthesized
    /// state (empty for tokens) and `syn`: the union of those, as earlier rules left it.
    /// `None` rejects the node.
    fn step(&self, node: &Node, inh: &State, children: &[State], syn: State) -> Option<State>;
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

fn down_all(rules: &[Box<dyn Rule>], node: &Node, inh: &State, pos: usize) -> State {
    let mut out = State::default();
    for r in rules {
        r.down(node, inh, pos, &mut out);
    }
    out
}

fn step_all(
    rules: &[Box<dyn Rule>],
    node: &Node,
    inh: &State,
    children: &[State],
) -> Option<State> {
    let union = children.iter().fold(State::default(), |a, c| a.union(c));
    rules
        .iter()
        .try_fold(union, |s, r| r.step(node, inh, children, s))
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

/// The grammar whose derivation trees are exactly `cfg`'s that every rule accepts.
pub fn refine(cfg: &Cfg, rules: &[Box<dyn Rule>], start: NtId) -> Result<Refined> {
    let items: Vec<Vec<Item>> = cfg.prods.iter().map(|p| items_of(cfg, p)).collect();
    let node = |p: ProdId| {
        let lhs = &cfg.nts[cfg.prods[p as usize].lhs as usize];
        Node {
            def: &lhs.base,
            group: lhs.synthetic,
            items: &items[p as usize],
        }
    };
    // Inherited contexts, top-down. Every nonterminal is a root with nothing inherited, so
    // the parts of the grammar the start does not reach keep a copy, as without rules. Each
    // context's productions, with the context of every nonterminal position.
    let root: Ctx = (start, State::default());
    let mut index: BTreeMap<Ctx, usize> = BTreeMap::new();
    let mut contexts: Vec<Ctx> = Vec::new();
    let mut expansions: Vec<Vec<(ProdId, Vec<Option<usize>>)>> = Vec::new();
    let mut intern = |ctx: Ctx, contexts: &mut Vec<Ctx>| -> usize {
        *index.entry(ctx.clone()).or_insert_with(|| {
            contexts.push(ctx);
            contexts.len() - 1
        })
    };
    for nt in 0..cfg.nts.len() as NtId {
        intern((nt, State::default()), &mut contexts);
    }
    let mut next = 0;
    while next < contexts.len() {
        let (nt, inh) = contexts[next].clone();
        let mut prods = Vec::new();
        for &p in &cfg.nts[nt as usize].prods {
            let here = node(p);
            let kids = cfg.prods[p as usize]
                .rhs
                .iter()
                .enumerate()
                .map(|(pos, &sym)| match sym {
                    Sym::Nt(c) => Some(intern(
                        (c, down_all(rules, &here, &inh, pos)),
                        &mut contexts,
                    )),
                    Sym::Lit(_) => None,
                })
                .collect();
            prods.push((p, kids));
        }
        expansions.push(prods);
        next += 1;
    }
    let mut users: Vec<Vec<(usize, usize)>> = vec![Vec::new(); contexts.len()];
    for (x, prods) in expansions.iter().enumerate() {
        for (slot, (_, kids)) in prods.iter().enumerate() {
            for &k in kids.iter().flatten() {
                users[k].push((x, slot));
            }
        }
    }

    // The start symbol's synthesized state is never consumed, so it is forgotten, which keeps
    // one start.
    let forget_at_start = !cfg.prods.iter().any(|p| p.rhs.contains(&Sym::Nt(start)));
    let state_of = |p: ProdId, inh: &State, children: &[State]| -> Option<State> {
        let s = step_all(rules, &node(p), inh, children)?;
        let lhs = cfg.prods[p as usize].lhs;
        Some(if forget_at_start && lhs == start {
            State::default()
        } else {
            s
        })
    };
    let empty: BTreeSet<State> = BTreeSet::from([State::default()]);
    let options = |kids: &[Option<usize>], states: &[BTreeSet<State>]| -> Vec<Vec<State>> {
        kids.iter()
            .map(|k| match k {
                Some(k) => states[*k].iter().cloned().collect(),
                None => empty.iter().cloned().collect(),
            })
            .collect()
    };

    // Synthesized states per context: a least fixed point, bottom-up, revisiting a production
    // only when one of its children gained a state.
    let mut states: Vec<BTreeSet<State>> = vec![BTreeSet::new(); contexts.len()];
    let mut queued: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut work: Vec<(usize, usize)> = Vec::new();
    for (x, prods) in expansions.iter().enumerate() {
        for slot in 0..prods.len() {
            queued.insert((x, slot));
            work.push((x, slot));
        }
    }
    while let Some((x, slot)) = work.pop() {
        queued.remove(&(x, slot));
        let (p, kids) = &expansions[x][slot];
        let inh = &contexts[x].1;
        let opts = options(kids, &states);
        let mut found = Vec::new();
        for_each_tuple(&opts, &mut |tuple| {
            let children: Vec<State> = tuple.iter().map(|s| (*s).clone()).collect();
            if let Some(s) = state_of(*p, inh, &children) {
                found.push(s);
            }
        })
        .with_context(|| {
            let sizes: Vec<String> = opts.iter().map(|o| o.len().to_string()).collect();
            format!(
                "in {} (states per position: {})",
                crate::describe(cfg, *p),
                sizes.join(" x ")
            )
        })?;
        let mut grew = false;
        for s in found {
            grew |= states[x].insert(s);
        }
        if grew {
            for &u in &users[x] {
                if queued.insert(u) {
                    work.push(u);
                }
            }
        }
    }

    let labels: BTreeMap<Fact, String> = rules.iter().flat_map(|r| r.labels()).collect();
    let mut ids: BTreeMap<(usize, State), NtId> = BTreeMap::new();
    let mut nts = Vec::new();
    for (x, (nt, inh)) in contexts.iter().enumerate() {
        let nt = &cfg.nts[*nt as usize];
        for syn in &states[x] {
            ids.insert((x, syn.clone()), nts.len() as NtId);
            nts.push(Nonterminal {
                name: copy_name(&nt.name, inh, syn, &labels),
                base: nt.base.clone(),
                synthetic: nt.synthetic,
                lexical: nt.lexical,
                origin: nt.origin.clone(),
                prods: Vec::new(),
            });
        }
    }
    let mut prods = Vec::new();
    for (x, expansion) in expansions.iter().enumerate() {
        let inh = &contexts[x].1;
        for (p, kids) in expansion {
            let prod = &cfg.prods[*p as usize];
            let opts = options(kids, &states);
            for_each_tuple(&opts, &mut |tuple| {
                let children: Vec<State> = tuple.iter().map(|s| (*s).clone()).collect();
                let Some(s) = state_of(*p, inh, &children) else {
                    return;
                };
                let lhs = ids[&(x, s)];
                let rhs = prod
                    .rhs
                    .iter()
                    .zip(kids)
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
                });
            })?;
        }
    }
    let r = contexts
        .iter()
        .position(|c| *c == root)
        .expect("every nonterminal has a root context");
    let Some(first) = states[r].iter().next() else {
        bail!("the rules reject every tree from <{}>", cfg.name(start));
    };
    if states[r].len() > 1 {
        bail!(
            "<{}> is recursive and ends in several states",
            cfg.name(start)
        );
    }
    Ok(Refined {
        start: ids[&(r, first.clone())],
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

fn for_each_tuple<T>(options: &[Vec<T>], f: &mut dyn FnMut(&[&T])) -> Result<()> {
    let total = options.iter().map(Vec::len).product::<usize>();
    if total > MAX_TUPLES {
        bail!("refinement would need {total} child-state combinations for one production");
    }
    let mut index = vec![0; options.len()];
    let mut tuple: Vec<&T> = Vec::with_capacity(options.len());
    for _ in 0..total {
        tuple.clear();
        tuple.extend(index.iter().enumerate().map(|(i, &c)| &options[i][c]));
        f(&tuple);
        for (i, choice) in index.iter_mut().enumerate() {
            *choice += 1;
            if *choice < options[i].len() {
                break;
            }
            *choice = 0;
        }
    }
    Ok(())
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

fn run(rules: &[Box<dyn Rule>], node: &Plain, inh: &State) -> Result<State, String> {
    let Plain::Def {
        name,
        synthetic,
        children,
    } = node
    else {
        return Ok(State::default());
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
    let here = Node {
        def: name,
        group: *synthetic,
        items: &items,
    };
    let mut states = Vec::with_capacity(children.len());
    for (pos, child) in children.iter().enumerate() {
        states.push(run(rules, child, &down_all(rules, &here, inh, pos))?);
    }
    let mut s = states.iter().fold(State::default(), |a, c| a.union(c));
    for rule in rules {
        s = rule
            .step(&here, inh, &states, s)
            .ok_or_else(|| format!("{} at <{name}>", rule.name()))?;
    }
    Ok(s)
}
