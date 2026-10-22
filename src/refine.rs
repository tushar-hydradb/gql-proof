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
use std::collections::{BTreeMap, BTreeSet, HashMap};

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
        Box::new(PathMinimums),
        Box::new(SimplifiedShape),
        Box::new(SelectiveAlone { id086 }),
    ]
}

/// Facts at or above this are free for rules built at run time, such as feature claims.
pub const FIRST_FREE_FACT: Fact = 32;

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

/// 16.7 SR 8, 16 and 20: a path pattern matches at least one node, so does a parenthesized
/// expression with a subpath variable, and what a quantifier or `?` repeats has a positive
/// minimum path length.
///
/// The minimums of 16.7 SR 7 and 15 only matter as "at least one", so each path node ends in
/// one of NODES / NO_NODES and one of LEN / NO_LEN, exhaustive so that a union's "every
/// operand" reads as "no child has NO_NODES" under the union of children, and a
/// concatenation's "some operand" as "a child has NODES". Computed after SR 14's transform: an
/// edge pattern under a quantifier or `?` is parenthesized, and a bare edge pattern in a path
/// term gets implicit node patterns on both sides, so a bare `<-` counts two nodes and `(<-)?`
/// none. A simplified expression is read through 16.12 SR 5-6: a label, negation, conjunction
/// or direction override is one edge pattern, a concatenation two in one term, a union or
/// alternation one per operand, a quantifier or `?` applies to the parenthesized edge.
///
/// A quantifier's lower bound (16.11 SR 2: `*` 0, `+` 1, `{n}` n, a missing bound 0) is zero or
/// not, read off the digit tokens of the `<unsigned integer>`; an `<other digit>` counts as
/// nonzero (the generator spells U+0663). The integer subtree carries that fact only where a
/// bound asks for it (inherited WANT), so numbers elsewhere are not copied. 16.11 SR 3 a i (an
/// upper bound is not 0) rides on the same fact; SR 3 a ii (upper below lower) does not.
pub struct PathMinimums;

const NODES: Fact = 12;
const NO_NODES: Fact = 13;
const LEN: Fact = 14;
const NO_LEN: Fact = 15;
/// A bare edge pattern, still to get its implicit node patterns or its parentheses.
const EDGE: Fact = 16;
const SUBPATH: Fact = 17;
const LB_ZERO: Fact = 18;
const LB_PRESENT: Fact = 19;
const NONZERO: Fact = 20;
/// Inherited: this integer is a quantifier bound, say whether it is zero.
const WANT: Fact = 21;
const MINIMUMS: [Fact; 9] = [
    NODES, NO_NODES, LEN, NO_LEN, EDGE, SUBPATH, LB_ZERO, LB_PRESENT, NONZERO,
];

/// The state with exactly these minimums.
fn minima(s: State, nodes: bool, len: bool) -> State {
    let mut s = s.without_all(&[NODES, NO_NODES, LEN, NO_LEN]);
    s.set(if nodes { NODES } else { NO_NODES }, true);
    s.set(if len { LEN } else { NO_LEN }, true);
    s
}

const BOUNDS: [&str; 3] = ["lower bound", "upper bound", "fixed quantifier"];
/// The integer subtree a bound's WANT reaches into, and no further.
const INTEGERS: [&str; 10] = [
    "unsigned integer",
    "unsigned decimal integer",
    "unsigned hexadecimal integer",
    "unsigned octal integer",
    "unsigned binary integer",
    "digit",
    "standard digit",
    "hex digit",
    "octal digit",
    "binary digit",
];

/// The definition an item names, a group by its owner.
fn owner_of<'a>(item: &Item<'a>) -> Option<&'a str> {
    match item {
        Item::Def(d) => Some(d),
        Item::Group(g) => g.split('/').next(),
        _ => None,
    }
}
const UNIONS: [&str; 4] = [
    "path pattern union",
    "path multiset alternation",
    "simplified path union",
    "simplified multiset alternation",
];

impl Rule for PathMinimums {
    fn name(&self) -> &str {
        "path pattern minimums"
    }

    fn cite(&self) -> &str {
        "16.7 SR 8, 16, 20: a quantified or questioned primary has a positive minimum path length, a path pattern and a named subpath a positive minimum node count; 16.11 SR 3: an upper bound is not 0"
    }

    fn labels(&self) -> Vec<(Fact, String)> {
        labels(&[
            (NODES, "nodes"),
            (NO_NODES, "no-nodes"),
            (LEN, "len"),
            (NO_LEN, "no-len"),
            (EDGE, "edge"),
            (SUBPATH, "subpath"),
            (LB_ZERO, "lb-zero"),
            (LB_PRESENT, "lb"),
            (NONZERO, "nonzero"),
            (WANT, "want"),
        ])
    }

    fn bookkeeping(&self) -> bool {
        true
    }

    fn down(&self, node: &Node, inh: &State, pos: usize, _left: &[State], out: &mut State) {
        let child = owner_of(&node.items[pos]);
        let asks = BOUNDS.contains(&node.def) && child == Some("unsigned integer");
        let within = inh.has(WANT) && child.is_some_and(|c| INTEGERS.contains(&c));
        if asks || within {
            out.set(WANT, true);
        }
    }

    fn step(&self, node: &Node, inh: &State, _children: &[State], s: State) -> Option<State> {
        if inh.has(WANT) {
            // Inside a bound's integer: a digit token other than 0, or a non-ASCII digit.
            let nonzero = node.items.iter().any(|i| match i {
                Item::Token(t) => {
                    t.len() == 1 && *t != "0" && t.chars().all(|c| c.is_ascii_alphanumeric())
                }
                Item::Prose("other digit") => true,
                _ => false,
            });
            return Some(if nonzero { s.with(NONZERO) } else { s });
        }
        if node.group {
            // A union's or alternation's repeated operands fold as they come (the minimum is
            // associative), so the group holds one of four states, not a subset of them.
            let owner = node.def.split('/').next().unwrap_or("");
            return Some(if UNIONS.contains(&owner) {
                let (nodes, len) = (!s.has(NO_NODES), !s.has(NO_LEN));
                minima(s, nodes, len)
            } else {
                s
            });
        }
        let rhs = node.items;
        Some(match node.def {
            // --- the bound's value, consumed by the quantifier ---
            "lower bound" => {
                let zero = !s.has(NONZERO);
                let s = s.without(NONZERO).with(LB_PRESENT);
                if zero { s.with(LB_ZERO) } else { s }
            }
            "fixed quantifier" => {
                let zero = !s.has(NONZERO);
                let s = s.without(NONZERO);
                if zero { s.with(LB_ZERO) } else { s }
            }
            "upper bound" => {
                if !s.has(NONZERO) {
                    return None;
                }
                s.without(NONZERO)
            }
            "general quantifier" => {
                let zero = !s.has(LB_PRESENT) || s.has(LB_ZERO);
                let mut s = s.without(LB_PRESENT);
                s.set(LB_ZERO, zero);
                s
            }
            "graph pattern quantifier" if rhs == [Item::Def("asterisk")] => s.with(LB_ZERO),
            // --- element patterns and factors ---
            "node pattern" => minima(s.without(EDGE), true, false),
            "edge pattern" => minima(s, false, true).with(EDGE),
            // SR 14 c-d: a bare edge in a term gets a node pattern on each side.
            "path factor" if rhs == [Item::Def("path primary")] && s.has(EDGE) => {
                minima(s.without(EDGE), true, true)
            }
            // SR 14 a parenthesizes an edge first, so it brings its implicit nodes along.
            "quantified path primary" | "simplified quantified" => {
                if !s.has(LEN) {
                    return None;
                }
                let positive = !s.has(LB_ZERO);
                let nodes = (s.has(NODES) || s.has(EDGE)) && positive;
                minima(s.without(EDGE).without(LB_ZERO), nodes, positive)
            }
            "questioned path primary" | "simplified questioned" => {
                if !s.has(LEN) {
                    return None;
                }
                minima(s.without(EDGE), false, false)
            }
            "path concatenation" | "simplified concatenation" => {
                let (nodes, len) = (s.has(NODES), s.has(LEN));
                minima(s, nodes, len)
            }
            d if UNIONS.contains(&d) => {
                let (nodes, len) = (!s.has(NO_NODES), !s.has(NO_LEN));
                minima(s, nodes, len)
            }
            "subpath variable declaration" => s.with(SUBPATH),
            "parenthesized path pattern expression" => {
                if s.has(SUBPATH) && !s.has(NODES) {
                    return None;
                }
                s.without(SUBPATH).without(EDGE)
            }
            // 16.12 SR 6: one edge pattern, in a term that gives it its implicit nodes.
            "simplified primary" if rhs == [Item::Def("label name")] => minima(s, true, true),
            "simplified negation" | "simplified conjunction" | "simplified direction override" => {
                minima(s, true, true)
            }
            "path pattern" => {
                if !s.has(NODES) {
                    return None;
                }
                s.without_all(&MINIMUMS)
            }
            // Nothing crosses a WHERE, a filler or a depth of matching.
            "element pattern filler"
            | "parenthesized path pattern where clause"
            | "graph pattern" => s.without_all(&MINIMUMS),
            // A number that is not a bound carries nothing.
            _ => s.without(NONZERO),
        })
    }
}

/// 16.12 SR 1-4: a simplified negation, conjunction or direction override holds no
/// concatenation, quantifier, `?` or multiset alternation, and an override no other override.
///
/// Inherited, not synthesized: being below one of those is a context, and the four forbidden
/// nodes are refused in it outright. That keeps the simplified nonterminals' states to their
/// minimums, so a union of them stays a few productions.
pub struct SimplifiedShape;

/// Inherited: below a negation, conjunction or direction override.
const INSIDE: Fact = 22;
/// Inherited: below a direction override.
const IN_OVERRIDE: Fact = 23;
const COMPLEX: [&str; 4] = [
    "simplified concatenation",
    "simplified quantified",
    "simplified questioned",
    "simplified multiset alternation",
];

impl SimplifiedShape {
    fn breaks(def: &str, inh: &State) -> bool {
        (inh.has(INSIDE) && COMPLEX.contains(&def))
            || (inh.has(IN_OVERRIDE) && def == "simplified direction override")
    }
}

impl Rule for SimplifiedShape {
    fn name(&self) -> &str {
        "simplified pattern shape"
    }

    fn cite(&self) -> &str {
        "16.12 SR 1-4: a <simplified negation>, <simplified direction override> or <simplified conjunction> contains no concatenation, quantifier, ? or multiset alternation; an override no override"
    }

    fn labels(&self) -> Vec<(Fact, String)> {
        labels(&[(INSIDE, "inside"), (IN_OVERRIDE, "in-override")])
    }

    fn bookkeeping(&self) -> bool {
        true
    }

    fn down(&self, node: &Node, inh: &State, pos: usize, _left: &[State], out: &mut State) {
        // The context reaches simplified nodes only, not the label names inside them.
        if !owner_of(&node.items[pos]).is_some_and(|c| c.starts_with("simplified ")) {
            return;
        }
        let opens = matches!(
            node.def,
            "simplified negation" | "simplified conjunction" | "simplified direction override"
        );
        if inh.has(INSIDE) || opens {
            out.set(INSIDE, true);
        }
        if inh.has(IN_OVERRIDE) || node.def == "simplified direction override" {
            out.set(IN_OVERRIDE, true);
        }
    }

    fn rejects(&self, node: &Node, inh: &State) -> bool {
        Self::breaks(node.def, inh)
    }

    fn step(&self, node: &Node, inh: &State, _children: &[State], s: State) -> Option<State> {
        if Self::breaks(node.def, inh) {
            return None;
        }
        Some(s)
    }
}

/// 16.4 SR 12: under DIFFERENT EDGES, a selective path pattern is alone in its list.
///
/// Reading: 16.6 SR 4 makes a path pattern selective by the search prefix it simply contains,
/// so a KEEP clause's prefix does not count here.
pub struct SelectiveAlone {
    pub id086: MatchModeDefault,
}

const SEARCH: Fact = 24;
const SELECTIVE_PATTERN: Fact = 25;
const ONE: Fact = 26;
const MANY: Fact = 27;
const DIFF: Fact = 28;
const MODE: Fact = 29;
const SR12: [Fact; 6] = [SEARCH, SELECTIVE_PATTERN, ONE, MANY, DIFF, MODE];

impl Rule for SelectiveAlone {
    fn name(&self) -> &str {
        "selective path pattern alone under DIFFERENT EDGES"
    }

    fn cite(&self) -> &str {
        "16.4 SR 12: under <different edges match mode>, a selective <path pattern> is the only one in its <path pattern list>"
    }

    fn labels(&self) -> Vec<(Fact, String)> {
        labels(&[
            (SEARCH, "search"),
            (SELECTIVE_PATTERN, "selective-pattern"),
            (ONE, "one"),
            (MANY, "many"),
            (DIFF, "diff"),
            (MODE, "mode"),
        ])
    }

    fn bookkeeping(&self) -> bool {
        true
    }

    fn step(&self, node: &Node, _inh: &State, children: &[State], s: State) -> Option<State> {
        if node.group {
            return Some(s);
        }
        Some(match node.def {
            "path search prefix" if node.items != [Item::Def("all path search")] => s.with(SEARCH),
            "keep clause" => s.without(SEARCH),
            "path pattern" => {
                let selective = s.has(SEARCH);
                let mut s = s.without(SEARCH).with(ONE);
                s.set(SELECTIVE_PATTERN, selective);
                s
            }
            "path pattern list" => {
                let many = children.iter().filter(|c| c.has(ONE)).count() >= 2;
                let mut s = s.without(ONE);
                s.set(MANY, many);
                s
            }
            "different edges match mode" => s.with(DIFF),
            "match mode" => s.with(MODE),
            "graph pattern" => {
                let default = !s.has(MODE) && self.id086 == MatchModeDefault::DifferentEdges;
                if (s.has(DIFF) || default) && s.has(SELECTIVE_PATTERN) && s.has(MANY) {
                    return None;
                }
                s.without_all(&SR12)
            }
            _ => s,
        })
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
    /// The same states in the order they were found.
    found: Vec<Vec<State>>,
    users: Vec<BTreeSet<(usize, usize)>>,
    work: Vec<(usize, usize)>,
    queued: BTreeSet<(usize, usize)>,
    /// For each production in a context, how many states of each child context it has
    /// already combined: a revisit only builds the combinations with a newer one
    /// (semi-naive evaluation).
    seen: HashMap<(usize, usize), HashMap<usize, usize>>,
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
            found: Vec::new(),
            users: Vec::new(),
            work: Vec::new(),
            queued: BTreeSet::new(),
            seen: HashMap::new(),
        }
    }

    fn add_state(&mut self, x: usize, s: State) -> bool {
        let new = self.states[x].insert(s.clone());
        if new {
            self.found[x].push(s);
        }
        new
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
        self.found.push(Vec::new());
        self.users.push(BTreeSet::new());
        x
    }

    /// Every combination of child states production `slot` of context `x` can take with the
    /// states found so far, left to right, each child in the context its left siblings give
    /// it; with `fresh`, only those holding a state it has not combined yet. Registers
    /// `(x, slot)` as a reader of every context it looks at. Ordered with the first position
    /// varying fastest.
    fn tuples(&mut self, x: usize, slot: usize, fresh: bool) -> Result<Vec<Tuple>> {
        let p = self.prods[x][slot];
        let inh = self.contexts[x].1.clone();
        let rhs = self.cfg.prods[p as usize].rhs.clone();
        // A first visit is all new, children or not.
        let first = !self.seen.contains_key(&(x, slot));
        let old = if fresh {
            self.seen.remove(&(x, slot)).unwrap_or_default()
        } else {
            HashMap::new()
        };
        let mut now: HashMap<usize, usize> = HashMap::new();
        let last = rhs.iter().rposition(|s| matches!(s, Sym::Nt(_)));
        // Each partial tuple keeps the index of every state in the order its context found
        // them, to order by, and whether it holds a new one.
        type Partial = (Vec<Option<usize>>, Vec<State>, Vec<usize>, bool);
        let mut partial: Vec<Partial> = vec![(Vec::new(), Vec::new(), Vec::new(), !fresh || first)];
        for (pos, sym) in rhs.iter().enumerate() {
            let mut next = Vec::new();
            for (kids, states, order, new) in partial {
                match *sym {
                    Sym::Lit(_) => {
                        let mut t = (kids, states, order, new);
                        t.0.push(None);
                        t.1.push(State::default());
                        t.2.push(0);
                        next.push(t);
                    }
                    Sym::Nt(c) => {
                        let inh_c = down_all(self.rules, &self.node(p), &inh, pos, &states);
                        let k = self.intern((c, inh_c));
                        self.users[k].insert((x, slot));
                        now.insert(k, self.found[k].len());
                        let seen = old.get(&k).copied().unwrap_or(0);
                        // At the last child, a tuple with nothing new yet takes a new state.
                        let from = if Some(pos) == last && !new { seen } else { 0 };
                        for (i, s) in self.found[k].iter().enumerate().skip(from) {
                            let mut t = (
                                kids.clone(),
                                states.clone(),
                                order.clone(),
                                new || i >= seen,
                            );
                            t.0.push(Some(k));
                            t.1.push(s.clone());
                            t.2.push(i);
                            next.push(t);
                        }
                    }
                }
            }
            if next.len() > MAX_TUPLES {
                // The states of each position for the first tuple, and the facts that tell
                // the most numerous position's states apart.
                let first = &next[0];
                let sizes: Vec<String> = first
                    .0
                    .iter()
                    .map(|k| k.map_or(1, |k| self.states[k].len()).to_string())
                    .collect();
                let widest = first
                    .0
                    .iter()
                    .flatten()
                    .max_by_key(|&&k| self.states[k].len())
                    .copied();
                let varying: BTreeSet<Fact> = widest.map_or_else(BTreeSet::new, |k| {
                    let all: Vec<&State> = self.states[k].iter().collect();
                    all.iter()
                        .flat_map(|s| s.facts())
                        .filter(|f| !all.iter().all(|s| s.has(*f)))
                        .collect()
                });
                let labels: BTreeMap<Fact, String> =
                    self.rules.iter().flat_map(|r| r.labels()).collect();
                let varying: Vec<&str> = varying
                    .iter()
                    .map(|f| labels.get(f).map_or("?", String::as_str))
                    .collect();
                bail!(
                    "refinement would need more than {MAX_TUPLES} child-state combinations in {} (states per position: {}; facts that vary: {})",
                    crate::describe(self.cfg, p),
                    sizes.join(" x "),
                    varying.join(", ")
                );
            }
            partial = next;
        }
        if fresh {
            self.seen.insert((x, slot), now);
        }
        partial.retain(|t| t.3);
        partial.sort_by(|a, b| a.2.iter().rev().cmp(b.2.iter().rev()));
        Ok(partial.into_iter().map(|(k, s, _, _)| (k, s)).collect())
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
        let found = r.tuples(x, slot, true)?;
        let mut grew = false;
        for (_, children) in found {
            for s in r.state_of(p, &r.contexts[x].1.clone(), &children) {
                grew |= r.add_state(x, s);
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
            for (kids, children) in r.tuples(x, slot, false)? {
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

/// A production's right hand side as the rules see it.
pub fn items_of<'c>(cfg: &'c Cfg, p: &Production) -> Vec<Item<'c>> {
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
