//! Compiles Syntax Rules that a grammar could express into the grammar itself.
//!
//! Some Syntax Rules are not about binding or typing at all: they forbid combinations a
//! context-free grammar could rule out but ISO chose to state in prose. Each one here is a
//! deterministic bottom-up tree automaton over derivation trees: a node's state is computed
//! from its children's, and a rule may reject a node outright. The derivation trees of a
//! context-free grammar intersected with a tree automaton are again the derivation trees of a
//! context-free grammar, so `refine` builds that grammar: one copy of each nonterminal per
//! reachable state, one production per combination of child states the rules accept. The
//! generator runs on it unchanged and every query it builds satisfies the rules by
//! construction.
//!
//! Nothing here is trusted. `verify` checks each rule again, directly from its text, and a
//! test makes the two agree.
//!
//! States are bitsets. Each rule owns some bits: producer nodes set them, consumer nodes read
//! and clear them, so nothing leaks past the construct it belongs to. A grouping node from
//! desugaring has the union of its children's state.
//!
//! Reading: 16.4 SR 6 and 14 say "contain", which in ISO is transitive and would let an outer
//! graph pattern's rules reach into subqueries nested in it. We read them per depth of graph
//! pattern matching (the notion 16.4 SR 2 introduces), so each `<graph pattern>` checks and
//! clears its own bits. 13.1 SR 5 is read along the statement sequence, see
//! `DataModifyingModifies`.

use crate::MatchModeDefault;
use crate::cfg::{Cfg, Lit, Nonterminal, NtId, ProdId, Production, Sym};
use crate::verify::Plain;
use anyhow::{Result, bail};
use std::collections::{BTreeMap, BTreeSet};

pub type State = u32;

pub trait Rule {
    fn name(&self) -> &'static str;
    fn cite(&self) -> &'static str;
    /// The bits this rule owns, with a label for naming refined nonterminals.
    fn bits(&self) -> &'static [(State, &'static str)];
    /// The state of a node of ISO definition `def` whose production's right hand side reads
    /// `rhs` (definitions by name, keywords and terminals by text) and whose children's states
    /// union to `state`. `None` rejects the node.
    fn step(&self, def: &str, rhs: &[&str], state: State) -> Option<State>;
}

/// Every rule, in the order they apply.
pub fn all_rules(id086: MatchModeDefault) -> Vec<Box<dyn Rule>> {
    vec![
        Box::new(UnboundedNeedsGuard { id086 }),
        Box::new(KeepWithoutSearch),
        Box::new(DataModifyingModifies),
    ]
}

/// 16.4 SR 14: every unbounded quantifier needs a guard.
pub struct UnboundedNeedsGuard {
    pub id086: MatchModeDefault,
}

const UNGUARDED: State = 1 << 0;
const UPPER: State = 1 << 1;
const RESTRICTIVE: State = 1 << 2;
const SELECTIVE: State = 1 << 3;
const PREFIX_GUARDS: State = 1 << 4;
const KEEP_GUARDS: State = 1 << 5;
const DIFFERENT: State = 1 << 6;
const MATCH_MODE: State = 1 << 7;
const SR14: State = (1 << 8) - 1;

impl Rule for UnboundedNeedsGuard {
    fn name(&self) -> &'static str {
        "unbounded quantifier needs a guard"
    }

    fn cite(&self) -> &'static str {
        "16.4 SR 14: an unbounded quantifier is bounded, inside a restrictive path mode, inside a selective path pattern, or under DIFFERENT EDGES"
    }

    fn bits(&self) -> &'static [(State, &'static str)] {
        &[
            (UNGUARDED, "unguarded"),
            (UPPER, "upper"),
            (RESTRICTIVE, "restrictive"),
            (SELECTIVE, "selective"),
            (PREFIX_GUARDS, "prefix-guards"),
            (KEEP_GUARDS, "keep-guards"),
            (DIFFERENT, "different"),
            (MATCH_MODE, "match-mode"),
        ]
    }

    fn step(&self, def: &str, rhs: &[&str], s: State) -> Option<State> {
        Some(match def {
            "upper bound" => s | UPPER,
            "general quantifier" if s & UPPER == 0 => s | UNGUARDED,
            "general quantifier" => s & !UPPER,
            "graph pattern quantifier" if matches!(rhs, ["asterisk"] | ["plus sign"]) => {
                s | UNGUARDED
            }
            "path mode" if matches!(rhs, ["TRAIL"] | ["SIMPLE"] | ["ACYCLIC"]) => s | RESTRICTIVE,
            "path search prefix" => {
                let selective = if rhs == ["all path search"] {
                    0
                } else {
                    SELECTIVE
                };
                guards(s | selective)
            }
            "path mode prefix" => guards(s),
            // SR 7 puts every prefix's path mode in parentheses around its expression, so a
            // guarding prefix guards everything under it.
            "parenthesized path pattern expression" | "path pattern" => {
                let s = if s & PREFIX_GUARDS != 0 {
                    s & !UNGUARDED
                } else {
                    s
                };
                s & !PREFIX_GUARDS
            }
            // SR 6 applies the KEEP prefix to every path pattern of this graph pattern.
            "keep clause" if s & PREFIX_GUARDS != 0 => (s & !PREFIX_GUARDS) | KEEP_GUARDS,
            "different edges match mode" => s | DIFFERENT,
            "match mode" => s | MATCH_MODE,
            "graph pattern" => {
                let default = s & MATCH_MODE == 0 && self.id086 == MatchModeDefault::DifferentEdges;
                let guarded = s & (DIFFERENT | KEEP_GUARDS) != 0 || default;
                if s & UNGUARDED != 0 && !guarded {
                    return None;
                }
                s & !SR14
            }
            _ => s,
        })
    }
}

/// A path mode or search prefix that guards: restrictive or selective.
fn guards(s: State) -> State {
    let guard = if s & (RESTRICTIVE | SELECTIVE) != 0 {
        PREFIX_GUARDS
    } else {
        0
    };
    (s & !(RESTRICTIVE | SELECTIVE)) | guard
}

/// 16.4 SR 6: with a KEEP clause, no path pattern has its own path search prefix.
pub struct KeepWithoutSearch;

const SEARCH_HERE: State = 1 << 8;
const PATTERN_SEARCH: State = 1 << 9;
const KEEP: State = 1 << 10;
const SR6: State = SEARCH_HERE | PATTERN_SEARCH | KEEP;

impl Rule for KeepWithoutSearch {
    fn name(&self) -> &'static str {
        "no search prefix under KEEP"
    }

    fn cite(&self) -> &'static str {
        "16.4 SR 6: with a <keep clause>, no <path pattern> contains a <path search prefix>"
    }

    fn bits(&self) -> &'static [(State, &'static str)] {
        &[
            (SEARCH_HERE, "search-here"),
            (PATTERN_SEARCH, "pattern-search"),
            (KEEP, "keep"),
        ]
    }

    fn step(&self, def: &str, _rhs: &[&str], s: State) -> Option<State> {
        Some(match def {
            "path search prefix" => s | SEARCH_HERE,
            "path pattern" if s & SEARCH_HERE != 0 => (s & !SEARCH_HERE) | PATTERN_SEARCH,
            // The KEEP clause's own prefix is the one allowed search prefix.
            "keep clause" => (s & !SEARCH_HERE) | KEEP,
            "graph pattern" => {
                if s & KEEP != 0 && s & PATTERN_SEARCH != 0 {
                    return None;
                }
                s & !SR6
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
/// A data-modifying statement buried in a subquery somewhere else does not count, so the bit
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

const MODIFIES: State = 1 << 11;

impl Rule for DataModifyingModifies {
    fn name(&self) -> &'static str {
        "data-modifying statement modifies"
    }

    fn cite(&self) -> &'static str {
        "13.1 SR 5: a <linear data-modifying statement> contains a <simple data-modifying statement>"
    }

    fn bits(&self) -> &'static [(State, &'static str)] {
        &[(MODIFIES, "modifies")]
    }

    fn step(&self, def: &str, _rhs: &[&str], s: State) -> Option<State> {
        match def {
            "simple data-modifying statement" => Some(s | MODIFIES),
            "linear data-modifying statement" if s & MODIFIES == 0 => None,
            // Passed on so an enclosing statement whose element is a nested procedure sees it.
            "linear data-modifying statement" => Some(s),
            d if SPINE.contains(&d) => Some(s),
            _ => Some(s & !MODIFIES),
        }
    }
}

fn step_all(rules: &[Box<dyn Rule>], def: &str, rhs: &[&str], s: State) -> Option<State> {
    rules.iter().try_fold(s, |s, r| r.step(def, rhs, s))
}

/// Above this many child-state combinations for one production, refinement gives up rather
/// than build an unreasonable grammar.
const MAX_TUPLES: usize = 1 << 16;

/// The refined grammar and its start symbol.
pub struct Refined {
    pub cfg: Cfg,
    pub start: NtId,
}

/// The grammar whose derivation trees are exactly `cfg`'s that every rule accepts.
pub fn refine(cfg: &Cfg, rules: &[Box<dyn Rule>], start: NtId) -> Result<Refined> {
    let rhs_names: Vec<Vec<&str>> = cfg
        .prods
        .iter()
        .map(|p| p.rhs.iter().map(|&s| sym_name(cfg, s)).collect())
        .collect();
    // The start symbol's state is never consumed, so it is forgotten, which keeps one start.
    let forget_at_start = !cfg.prods.iter().any(|p| p.rhs.contains(&Sym::Nt(start)));
    let state_of = |p: ProdId, union: State| -> Option<State> {
        let lhs = cfg.prods[p as usize].lhs;
        let nt = &cfg.nts[lhs as usize];
        let s = match nt.synthetic {
            true => union,
            false => step_all(rules, &nt.base, &rhs_names[p as usize], union)?,
        };
        Some(if forget_at_start && lhs == start {
            0
        } else {
            s
        })
    };

    // Reachable states per nonterminal: a least fixed point, bottom-up.
    let mut states: Vec<BTreeSet<State>> = vec![BTreeSet::new(); cfg.nts.len()];
    let mut changed = true;
    while changed {
        changed = false;
        for (p, prod) in cfg.prods.iter().enumerate() {
            let options = child_options(cfg, prod, &states);
            for_each_tuple(&options, &mut |tuple| {
                let union = tuple.iter().fold(0, |a, &s| a | s);
                if let Some(s) = state_of(p as ProdId, union) {
                    changed |= states[prod.lhs as usize].insert(s);
                }
            })?;
        }
    }

    let labels: Vec<(State, &str)> = rules
        .iter()
        .flat_map(|r| r.bits().iter().copied())
        .collect();
    let mut ids: BTreeMap<(NtId, State), NtId> = BTreeMap::new();
    let mut nts = Vec::new();
    for (x, nt) in cfg.nts.iter().enumerate() {
        for &s in &states[x] {
            ids.insert((x as NtId, s), nts.len() as NtId);
            nts.push(Nonterminal {
                name: copy_name(&nt.name, s, &labels),
                base: nt.base.clone(),
                synthetic: nt.synthetic,
                lexical: nt.lexical,
                origin: nt.origin.clone(),
                prods: Vec::new(),
            });
        }
    }
    let mut prods = Vec::new();
    for (p, prod) in cfg.prods.iter().enumerate() {
        let options = child_options(cfg, prod, &states);
        for_each_tuple(&options, &mut |tuple| {
            let union = tuple.iter().fold(0, |a, &s| a | s);
            let Some(s) = state_of(p as ProdId, union) else {
                return;
            };
            let lhs = ids[&(prod.lhs, s)];
            let rhs = prod
                .rhs
                .iter()
                .zip(tuple)
                .map(|(&sym, &cs)| match sym {
                    Sym::Nt(c) => Sym::Nt(ids[&(c, cs)]),
                    lit => lit,
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
    let Some(&start) = states[start as usize]
        .iter()
        .next()
        .map(|s| &ids[&(start, *s)])
    else {
        bail!("the rules reject every tree from <{}>", cfg.name(start));
    };
    if !forget_at_start && states[start as usize].len() > 1 {
        bail!(
            "<{}> is recursive and ends in several states",
            cfg.name(start)
        );
    }
    Ok(Refined {
        cfg: Cfg::from_parts(nts, prods, cfg.lits.clone(), cfg.occs.clone()),
        start,
    })
}

fn sym_name(cfg: &Cfg, sym: Sym) -> &str {
    match sym {
        Sym::Nt(nt) => cfg.base(nt),
        Sym::Lit(l) => match &cfg.lits[l as usize] {
            Lit::Kw(t) | Lit::Term(t) | Lit::Opaque(t) => t,
        },
    }
}

/// The states each right hand side position can be in: a literal is always 0.
fn child_options(cfg: &Cfg, prod: &Production, states: &[BTreeSet<State>]) -> Vec<Vec<State>> {
    let _ = cfg;
    prod.rhs
        .iter()
        .map(|&sym| match sym {
            Sym::Nt(c) => states[c as usize].iter().copied().collect(),
            Sym::Lit(_) => vec![0],
        })
        .collect()
}

fn for_each_tuple(options: &[Vec<State>], f: &mut dyn FnMut(&[State])) -> Result<()> {
    let total = options.iter().map(Vec::len).product::<usize>();
    if total > MAX_TUPLES {
        bail!("refinement would need {total} child-state combinations for one production");
    }
    let mut tuple = vec![0; options.len()];
    let mut index = vec![0; options.len()];
    for _ in 0..total {
        for (i, choice) in index.iter().enumerate() {
            tuple[i] = options[i][*choice];
        }
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

fn copy_name(name: &str, s: State, labels: &[(State, &str)]) -> String {
    if s == 0 {
        return name.to_string();
    }
    let set: Vec<&str> = labels
        .iter()
        .filter(|(b, _)| s & b != 0)
        .map(|(_, l)| *l)
        .collect();
    format!("{name}@{}", set.join("+"))
}

/// Runs the rules over one tree: the first rule to reject a node, if any.
pub fn accepts(rules: &[Box<dyn Rule>], tree: &Plain) -> Result<(), String> {
    run(rules, tree).map(|_| ())
}

fn run(rules: &[Box<dyn Rule>], node: &Plain) -> Result<State, String> {
    let Plain::Def {
        name,
        synthetic,
        children,
    } = node
    else {
        return Ok(0);
    };
    let mut union = 0;
    for child in children {
        union |= run(rules, child)?;
    }
    if *synthetic {
        return Ok(union);
    }
    let rhs: Vec<&str> = children
        .iter()
        .map(|c| match c {
            Plain::Def { name, .. } => name.as_str(),
            Plain::Kw(t) | Plain::Term(t) => t.as_str(),
            Plain::Leaf { def, .. } => def.as_str(),
        })
        .collect();
    let mut s = union;
    for rule in rules {
        s = rule
            .step(name, &rhs, s)
            .ok_or_else(|| format!("{} at <{name}>", rule.name()))?;
    }
    Ok(s)
}
