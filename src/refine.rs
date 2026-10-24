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
        Box::new(TrimOperands),
        Box::new(DelimitedNotEmpty),
        Box::new(ElementTypeShape),
        Box::new(OneAccessMode),
        Box::new(IntegerCount),
        Box::new(StatementKinds),
        Box::new(ParentSolidus),
        Box::new(PropertyValueTypes),
        Box::new(ClosedInitializerTypes),
        Box::new(UnionNullability),
    ]
}

/// Facts at or above this are free for rules built at run time, such as feature claims.
pub const FIRST_FREE_FACT: Fact = 128;

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
/// nonzero, which rests on the leaf provider spelling U+0663 (`leaf::StubProvider`): the
/// checker reads the digit's real value (`verify::digit_value`), so a provider spelling an
/// Nd zero would be caught there. The integer subtree carries that fact only where a
/// bound asks for it (inherited WANT), so numbers elsewhere are not copied. 16.11 SR 3 a i (an
/// upper bound is not 0, and `{0}` is `{0,0}`) rides on the same fact; SR 3 a ii (upper below
/// lower) does not. 16.7 SR 9 (no quantified primary directly under a quantified primary)
/// is an inherited context like 16.12's, refused outright.
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
/// Inherited: under a quantified primary at this depth of matching (16.7 SR 9).
const IN_QUANT: Fact = 30;
const MINIMUMS: [Fact; 9] = [
    NODES, NO_NODES, LEN, NO_LEN, EDGE, SUBPATH, LB_ZERO, LB_PRESENT, NONZERO,
];
/// Where a depth of graph pattern matching ends: a nested graph pattern starts its own.
const DEPTH_ENDS: [&str; 3] = [
    "graph pattern",
    "element pattern filler",
    "parenthesized path pattern where clause",
];
const QUANTIFIED: [&str; 2] = ["quantified path primary", "simplified quantified"];

/// The state with exactly these minimums.
fn minima(s: State, nodes: bool, len: bool) -> State {
    let mut s = s.without_all(&[NODES, NO_NODES, LEN, NO_LEN]);
    s.set(if nodes { NODES } else { NO_NODES }, true);
    s.set(if len { LEN } else { NO_LEN }, true);
    s
}

const BOUNDS: [&str; 3] = ["lower bound", "upper bound", "fixed quantifier"];
/// The integer subtree a bound's WANT reaches into, and no further.
const INTEGERS: [&str; 11] = [
    "unsigned integer",
    "unsigned decimal integer",
    "unsigned hexadecimal integer",
    "unsigned octal integer",
    "unsigned binary integer",
    "digit",
    "standard digit",
    "other digit",
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
        "16.7 SR 8, 9, 16, 20: a quantified or questioned primary has a positive minimum path length and no quantified primary inside, a path pattern and a named subpath a positive minimum node count; 16.11 SR 3: an upper bound is not 0"
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
            (IN_QUANT, "in-quant"),
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
        // 16.7 SR 9: what a quantifier repeats, to the end of this depth of matching.
        let repeats = QUANTIFIED.contains(&node.def)
            && matches!(child, Some("path primary" | "simplified tertiary"));
        let below = inh.has(IN_QUANT) && !child.is_some_and(|c| DEPTH_ENDS.contains(&c));
        if repeats || below {
            out.set(IN_QUANT, true);
        }
    }

    fn rejects(&self, node: &Node, inh: &State) -> bool {
        inh.has(IN_QUANT) && QUANTIFIED.contains(&node.def)
    }

    fn step(&self, node: &Node, inh: &State, _children: &[State], s: State) -> Option<State> {
        if self.rejects(node, inh) {
            return None;
        }
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
            // 16.11 SR 2 c and 3 a i: `{0}` is `{0,0}`, an upper bound of 0.
            "fixed quantifier" => {
                if !s.has(NONZERO) {
                    return None;
                }
                s.without(NONZERO)
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
/// Reading: SR 6 turns a negation or conjunction into a label expression (NOTE 255, 257), so
/// a direction override inside one is a non-label construct and is refused too, as it is
/// inside an override (SR 2).
///
/// Inherited, not synthesized: being below one of those is a context, and the forbidden
/// nodes are refused in it outright. That keeps the simplified nonterminals' states to their
/// minimums, so a union of them stays a few productions.
pub struct SimplifiedShape;

/// Inherited: below a negation, conjunction or direction override.
const INSIDE: Fact = 22;
const COMPLEX: [&str; 5] = [
    "simplified concatenation",
    "simplified quantified",
    "simplified questioned",
    "simplified multiset alternation",
    "simplified direction override",
];

impl SimplifiedShape {
    fn breaks(def: &str, inh: &State) -> bool {
        inh.has(INSIDE) && COMPLEX.contains(&def)
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
        labels(&[(INSIDE, "inside")])
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

/// 20.24 SR 3 b i 1: FROM in a single-character TRIM needs a <trim specification> or a <trim
/// character string> before it.
///
/// Reading: 20.25 has no twin for <byte string trim operands>, but its General Rule 2 b reads
/// the <trim byte string> as if present, so a bare FROM is refused there too.
pub struct TrimOperands;

/// Synthesized: a trim specification or trim string below, up to the operands.
const TRIMMING: Fact = 23;
const TRIM_OPERANDS: [&str; 2] = ["trim operands", "byte string trim operands"];

impl Rule for TrimOperands {
    fn name(&self) -> &str {
        "TRIM's FROM follows a specification or a trim string"
    }

    fn cite(&self) -> &str {
        "20.24 SR 3: a single-character trim function with FROM has a <trim specification> or a <trim character string> (byte strings alike)"
    }

    fn labels(&self) -> Vec<(Fact, String)> {
        labels(&[(TRIMMING, "trimming")])
    }

    fn bookkeeping(&self) -> bool {
        true
    }

    fn step(&self, node: &Node, _inh: &State, _children: &[State], s: State) -> Option<State> {
        let owner = node.def.split('/').next().unwrap_or(node.def);
        match node.def {
            "trim specification" | "trim character string" | "trim byte string" => {
                return Some(s.with(TRIMMING));
            }
            // BTRIM(x, y): a trim string with no FROM.
            "multi-character trim function" => return Some(s.without(TRIMMING)),
            _ => {}
        }
        if TRIM_OPERANDS.contains(&owner) {
            let from = node.items.iter().any(|i| *i == Item::Token("FROM"));
            if from && !s.has(TRIMMING) {
                return None;
            }
            if !node.group {
                return Some(s.without(TRIMMING));
            }
        }
        Some(s)
    }
}

/// 21.3 SR 4: a <delimited identifier> is not the zero-length string: `""` and ` `` ` are
/// refused (the empty alternative of the optional inside the accent quotes has no valid
/// witness, so its targets are never covered). `""` as a <character string literal> is the
/// same <double quoted character sequence> and stays.
pub struct DelimitedNotEmpty;

/// Synthesized: a character representation below, up to the quoted sequence.
const QUOTED: Fact = 31;

impl Rule for DelimitedNotEmpty {
    fn name(&self) -> &str {
        "delimited identifier not empty"
    }

    fn cite(&self) -> &str {
        "21.3 SR 4: the representative form of a <delimited identifier> is not the zero-length character string"
    }

    fn labels(&self) -> Vec<(Fact, String)> {
        labels(&[(QUOTED, "quoted")])
    }

    fn bookkeeping(&self) -> bool {
        true
    }

    fn step(&self, node: &Node, _inh: &State, _children: &[State], s: State) -> Option<State> {
        match node.def {
            "double quoted character representation" | "accent quoted character representation" => {
                Some(s.with(QUOTED))
            }
            // The sequences are shared with <character string literal>, where `""` is the
            // empty string: the fact is judged at the identifier and dropped at the literal.
            "delimited identifier" => {
                if s.has(QUOTED) { Some(s.without(QUOTED)) } else { None }
            }
            "character string literal" => Some(s.without(QUOTED)),
            _ => Some(s),
        }
    }
}

/// 18.2 SR 2, 3 and 18.3 SR 2, 3, 4: the shape of a node or edge type specification.
///
/// - inside a closed node reference value type (`NODE TYPE { }` as a type, not in a graph
///   type body), a node type specification has no local alias, key label set or type name
///   (18.2 SR 2); an edge type specification inside a closed edge reference value type has no
///   key label set, type name or endpoint aliases, and no key label set in an endpoint (18.3
///   SR 2)
/// - a node type specification with a type name has no key label set and no alias (18.2 SR
///   3); an edge type specification with a type name has no key label set (18.3 SR 3)
/// - an edge type specification saying DIRECTED has a directed shape (an endpoint pair or a
///   pattern), one saying UNDIRECTED an undirected shape (18.3 SR 4)
///
/// "Simply contains" is read as the standard defines it: without an intervening instance of
/// the container's own definition. Every fact is synthesized: what a specification holds
/// rises to it and on to its parent, which is the closed reference value type (rejecting) or
/// the element type specification of a graph type body (consuming), the only two places a
/// specification occurs. A specification nested in a property's type is consumed at its own
/// parent, so nothing crosses one, and nothing is inherited: the grammar below a type is not
/// copied. (A key label set in an edge type's endpoint reaching an enclosing node type would
/// be the letter of 18.2 SR 3; it is consumed at the edge type's closed reference value type,
/// which 18.3 SR 2 refuses anyway.)
///
/// Reading of 18.3 SR 4: it constrains an edge type specification that says DIRECTED or
/// UNDIRECTED; a pattern with no edge kind (`( ) -[ ]-> ( )`) is not constrained (its "otherwise"
/// case presumes UNDIRECTED is present).
pub struct ElementTypeShape;

const NAMED: Fact = 32;
const KEYED: Fact = 33;
const ALIASED: Fact = 34;
const EDGE_NAMED: Fact = 35;
const EDGE_KEYED: Fact = 36;
const SOURCE_ALIASED: Fact = 37;
const DESTINATION_ALIASED: Fact = 38;
const DIRECTED_KW: Fact = 39;
const UNDIRECTED_KW: Fact = 40;
const DIRECTED_SHAPE: Fact = 41;
const UNDIRECTED_SHAPE: Fact = 42;
/// What a node type specification tells its parent.
const NODE_SHAPE: [Fact; 3] = [NAMED, KEYED, ALIASED];
/// What an edge type specification tells its parent: a node type key label set in it sits in
/// an endpoint reference (18.3 SR 2 c, d).
const EDGE_SHAPE: [Fact; 5] = [EDGE_NAMED, EDGE_KEYED, SOURCE_ALIASED, DESTINATION_ALIASED, KEYED];
/// What an edge type specification settles itself.
const EDGE_KIND: [Fact; 4] = [DIRECTED_KW, UNDIRECTED_KW, DIRECTED_SHAPE, UNDIRECTED_SHAPE];

impl Rule for ElementTypeShape {
    fn name(&self) -> &str {
        "element type specification shape"
    }

    fn cite(&self) -> &str {
        "18.2 SR 2, 3 and 18.3 SR 2, 3, 4: a node or edge type specification in a closed reference value type has no alias, key label set or type name; a named one no key label set or alias; DIRECTED or UNDIRECTED matches the shape"
    }

    fn labels(&self) -> Vec<(Fact, String)> {
        labels(&[
            (NAMED, "named"),
            (KEYED, "keyed"),
            (ALIASED, "aliased"),
            (EDGE_NAMED, "edge-named"),
            (EDGE_KEYED, "edge-keyed"),
            (SOURCE_ALIASED, "source-aliased"),
            (DESTINATION_ALIASED, "destination-aliased"),
            (DIRECTED_KW, "directed-kw"),
            (UNDIRECTED_KW, "undirected-kw"),
            (DIRECTED_SHAPE, "directed-shape"),
            (UNDIRECTED_SHAPE, "undirected-shape"),
        ])
    }

    fn bookkeeping(&self) -> bool {
        true
    }

    fn step(&self, node: &Node, _inh: &State, _children: &[State], s: State) -> Option<State> {
        if node.group {
            return Some(s);
        }
        Some(match node.def {
            "node type name" => s.with(NAMED),
            "node type key label set" => s.with(KEYED),
            "local node type alias" => s.with(ALIASED),
            "edge type name" => s.with(EDGE_NAMED),
            "edge type key label set" => s.with(EDGE_KEYED),
            "source node type alias" => s.with(SOURCE_ALIASED),
            "destination node type alias" => s.with(DESTINATION_ALIASED),
            "edge kind" if node.items == [Item::Token("DIRECTED")] => s.with(DIRECTED_KW),
            "edge kind" => s.with(UNDIRECTED_KW),
            "endpoint pair directed" | "edge type pattern directed" => s.with(DIRECTED_SHAPE),
            "endpoint pair undirected" | "edge type pattern undirected" => s.with(UNDIRECTED_SHAPE),
            // 18.2 SR 3; the shape goes on to the parent.
            "node type specification" => {
                if s.has(NAMED) && (s.has(KEYED) || s.has(ALIASED)) {
                    return None;
                }
                s
            }
            // 18.3 SR 3, 4; the shape goes on to the parent.
            "edge type specification" => {
                if (s.has(EDGE_NAMED) && s.has(EDGE_KEYED))
                    || (s.has(DIRECTED_KW) && !s.has(DIRECTED_SHAPE))
                    || (s.has(UNDIRECTED_KW) && !s.has(UNDIRECTED_SHAPE))
                {
                    return None;
                }
                s.without_all(&EDGE_KIND)
            }
            // 18.2 SR 2, 18.3 SR 2.
            "closed node reference value type" => {
                if NODE_SHAPE.iter().any(|f| s.has(*f)) {
                    return None;
                }
                s
            }
            "closed edge reference value type" => {
                if EDGE_SHAPE.iter().any(|f| s.has(*f)) {
                    return None;
                }
                s
            }
            "element type specification" => s.without_all(&NODE_SHAPE).without_all(&EDGE_SHAPE),
            _ => s,
        })
    }
}

/// 8.2 SR 2: transaction characteristics hold exactly one <transaction access mode>.
///
/// Counted, not unioned: a list of modes folds its items as they come (the repetition's group
/// node sees each operand's state), so the characteristics end in one of none, one or many.
/// An <implementation-defined access mode> is not a <transaction access mode> and counts for
/// nothing; the leaf is excluded from generation anyway (8.2 SR 3, `tokens::EXCLUDED`).
pub struct OneAccessMode;

const MODE_ONE: Fact = 43;
const MODE_MANY: Fact = 44;

/// How many access modes the children hold: one per child with one, two for a child with many.
fn modes(children: &[State]) -> usize {
    children
        .iter()
        .map(|c| if c.has(MODE_MANY) { 2 } else { usize::from(c.has(MODE_ONE)) })
        .sum()
}

fn counted(s: State, n: usize) -> State {
    let mut s = s.without(MODE_ONE).without(MODE_MANY);
    match n {
        0 => {}
        1 => s = s.with(MODE_ONE),
        _ => s = s.with(MODE_MANY),
    }
    s
}

impl Rule for OneAccessMode {
    fn name(&self) -> &str {
        "one transaction access mode"
    }

    fn cite(&self) -> &str {
        "8.2 SR 2: <transaction characteristics> contain exactly one <transaction access mode>"
    }

    fn labels(&self) -> Vec<(Fact, String)> {
        labels(&[(MODE_ONE, "mode"), (MODE_MANY, "modes")])
    }

    fn bookkeeping(&self) -> bool {
        true
    }

    fn step(&self, node: &Node, _inh: &State, children: &[State], s: State) -> Option<State> {
        let owner = node.def.split('/').next().unwrap_or(node.def);
        if owner != "transaction characteristics" {
            return Some(if node.def == "transaction access mode" {
                s.with(MODE_ONE)
            } else {
                s
            });
        }
        let n = modes(children);
        if node.group {
            return Some(counted(s, n));
        }
        if n != 1 {
            return None;
        }
        Some(counted(s, 0))
    }
}

/// 20.16 SR 1 a: TRIM's list count is an exact number of scale 0.
///
/// Reading: the engine's classes carry no scale, and a variable's scale is not followed, so
/// the count is kept to forms whose scale is 0 by their shape alone: an <unsigned integer>
/// literal, a dynamic parameter (its type is the request's, hypothesis H), a length or
/// cardinality expression (scale 0, 20.22 SR 1, 3), with signs, parentheses, `+`, `-` and `*`
/// over them (20.21 SR 1 b ii, iii: scale max(S1, S2) and S1 + S2). Everything else is refused
/// in that position: a decimal or approximate literal, `/`, a NULL (21.2 SR 67 b leaves its
/// type to the implementation, IA014), a variable, any other function. The types checker
/// (`verify::types`) checks the type itself; `verify::syntax_rules` checks this shape.
pub struct IntegerCount;

/// Inherited: inside TRIM's list count, down to the integer forms.
const IN_COUNT: Fact = 45;

/// Whether `node` may stand inside the count: its definition and, for some, its alternative.
pub fn integer_count_shape(def: &str, items: &[Item]) -> bool {
    let only = |d: &str| items == [Item::Def(d)];
    match def {
        "numeric value expression" | "factor" | "numeric primary" | "value expression primary"
        | "parenthesized value expression" | "sign" | "plus sign" | "minus sign"
        | "asterisk" | "left paren" | "right paren" | "unsigned integer"
        | "length expression" | "cardinality expression" | "dynamic parameter specification" => true,
        "term" => !items.contains(&Item::Def("solidus")),
        "value expression" => only("common value expression"),
        "common value expression" => only("numeric value expression"),
        "numeric value function" => only("length expression") || only("cardinality expression"),
        "non-parenthesized value expression primary" => {
            only("non-parenthesized value expression primary special case")
        }
        "non-parenthesized value expression primary special case" => {
            only("unsigned value specification")
        }
        "unsigned value specification" => {
            only("unsigned literal") || only("general value specification")
        }
        "general value specification" => only("dynamic parameter specification"),
        "unsigned literal" => only("unsigned numeric literal"),
        "unsigned numeric literal" => only("exact numeric literal"),
        "exact numeric literal" => only("unsigned integer"),
        _ => false,
    }
}

/// Where the count's shape stops mattering: what is below is an integer, an argument or a
/// parameter name.
const COUNT_STOPS: [&str; 4] = [
    "unsigned integer",
    "length expression",
    "cardinality expression",
    "dynamic parameter specification",
];

impl Rule for IntegerCount {
    fn name(&self) -> &str {
        "TRIM's list count is an integer"
    }

    fn cite(&self) -> &str {
        "20.16 SR 1 a: the <numeric value expression> of a <trim list function> is exact numeric with scale 0"
    }

    fn labels(&self) -> Vec<(Fact, String)> {
        labels(&[(IN_COUNT, "in-count")])
    }

    fn bookkeeping(&self) -> bool {
        true
    }

    fn down(&self, node: &Node, inh: &State, pos: usize, _left: &[State], out: &mut State) {
        let owner = node.def.split('/').next().unwrap_or(node.def);
        let child = owner_of(&node.items[pos]);
        let opens = owner == "trim list function" && child == Some("numeric value expression");
        let within = inh.has(IN_COUNT) && !COUNT_STOPS.contains(&owner) && child.is_some();
        if opens || within {
            out.set(IN_COUNT, true);
        }
    }

    fn rejects(&self, node: &Node, inh: &State) -> bool {
        if !inh.has(IN_COUNT) {
            return false;
        }
        // A group leads only to definitions, each judged on its own.
        if node.group {
            return false;
        }
        !integer_count_shape(node.def, node.items)
    }

    fn step(&self, node: &Node, inh: &State, _children: &[State], s: State) -> Option<State> {
        if self.rejects(node, inh) {
            return None;
        }
        Some(s)
    }
}

/// The statement kinds: 9.1 SR 5-7, 9.2 SR 4-6, 12.8 SR 2, 13.6 SR 2, 14.5 SR 2, 14.2 SR 3-4,
/// 14.12 SR 26 b ii.
///
/// Synthesized facts flow from each statement up its procedure's spine: the kind of each
/// <statement> (catalog, data-modifying, query), whether the block has a NEXT, whether its
/// directly contained statements are focused or ambient, whether its linear query statements
/// are SELECTs or not, and the query conjunctions of each composite query. They are judged at
/// the composite query statement (14.2), the statement block (9.2) and the procedure
/// specification's kind (9.1), where they stop: a <procedure body> occurs only under the three
/// kinds, so nothing from a nested body reaches an enclosing one. A <query specification>
/// turns its focused and ambient facts into the ones 14.12 SR 26 reads at a <select query
/// specification>, dropped at any other parent. Inherited: the kind an inline CALL's
/// statement asks of its procedure (12.8, 13.6, 14.5), refused at the <procedure
/// specification>; and, under a <set operator>, that its quantifier is the operator's.
///
/// 9.2 SR 7 (with a result statement beside one without) is the checker's alone: "contains"
/// reaches into nested bodies, which these facts do not.
pub struct StatementKinds;

const K_CAT: Fact = 46;
const K_DATA: Fact = 47;
const K_QUERY: Fact = 48;
const HAS_NEXT: Fact = 49;
const FOC: Fact = 50;
const AMB: Fact = 51;
const SEL_Q: Fact = 52;
const NSEL_Q: Fact = 53;
/// The query conjunctions, normalised by 14.2 SR 1.
const CONJ: [Fact; 7] = [54, 55, 56, 57, 58, 59, 60];
const SPEC_FOC: Fact = 61;
const SPEC_AMB: Fact = 62;
const SEL: Fact = 63;
const CALL_CAT: Fact = 64;
const CALL_DATA: Fact = 65;
const CALL_QUERY: Fact = 66;
const Q_ALL: Fact = 67;
const IN_SETOP: Fact = 68;
const BLOCK_FACTS: [Fact; 8] = [K_CAT, K_DATA, K_QUERY, HAS_NEXT, FOC, AMB, SEL_Q, NSEL_Q];
const SPEC_KINDS: [&str; 3] = [
    "catalog-modifying procedure specification",
    "data-modifying procedure specification",
    "query specification",
];
/// From an inline CALL's statement down to its <procedure specification>.
const CALL_CHAIN: [&str; 4] = [
    "call procedure statement",
    "procedure call",
    "inline procedure call",
    "nested procedure specification",
];

impl Rule for StatementKinds {
    fn name(&self) -> &str {
        "statement kinds"
    }

    fn cite(&self) -> &str {
        "9.1 SR 5-7, 9.2 SR 4-6, 12.8 SR 2, 13.6 SR 2, 14.5 SR 2, 14.2 SR 3-4, 14.12 SR 26: each procedure's statements are of its kind, a block's statements agree, a composite query has one conjunction and one focus, an inline CALL's procedure has its statement's kind, a FROM's nested query has the focus its graph expression asks"
    }

    fn labels(&self) -> Vec<(Fact, String)> {
        let mut l = labels(&[
            (K_CAT, "k-cat"),
            (K_DATA, "k-data"),
            (K_QUERY, "k-query"),
            (HAS_NEXT, "has-next"),
            (FOC, "foc"),
            (AMB, "amb"),
            (SEL_Q, "sel-q"),
            (NSEL_Q, "nsel-q"),
            (SPEC_FOC, "spec-foc"),
            (SPEC_AMB, "spec-amb"),
            (SEL, "sel"),
            (CALL_CAT, "call-cat"),
            (CALL_DATA, "call-data"),
            (CALL_QUERY, "call-query"),
            (Q_ALL, "q-all"),
            (IN_SETOP, "in-setop"),
        ]);
        for (i, f) in CONJ.iter().enumerate() {
            l.push((*f, format!("conj{i}")));
        }
        l
    }

    fn bookkeeping(&self) -> bool {
        true
    }

    fn down(&self, node: &Node, inh: &State, pos: usize, _left: &[State], out: &mut State) {
        let owner = node.def.split('/').next().unwrap_or(node.def);
        let child = owner_of(&node.items[pos]);
        // The kind an inline CALL asks of its procedure.
        let asks = match owner {
            "call catalog-modifying procedure statement" => Some(CALL_CAT),
            "call data-modifying procedure statement" => Some(CALL_DATA),
            "call query statement" => Some(CALL_QUERY),
            _ => None,
        };
        // Only along the chain to the <procedure specification>, nowhere else.
        let onward = child.is_some_and(|c| {
            CALL_CHAIN.contains(&c) || c == "procedure specification"
        }) || matches!(node.items[pos], Item::Group(_));
        if let Some(f) = asks {
            if onward {
                out.set(f, true);
            }
        } else if (CALL_CHAIN.contains(&owner) || node.group) && onward {
            for f in [CALL_CAT, CALL_DATA, CALL_QUERY] {
                if inh.has(f) {
                    out.set(f, true);
                }
            }
        }
        // A set operator's quantifier.
        if (owner == "set operator" && !node.group) || (node.group && inh.has(IN_SETOP)) {
            if matches!(child, Some("set quantifier")) || node.group || owner == "set operator" {
                out.set(IN_SETOP, true);
            }
        }
    }

    fn rejects(&self, node: &Node, inh: &State) -> bool {
        if node.group || node.def != "procedure specification" {
            return false;
        }
        let want = if inh.has(CALL_CAT) {
            SPEC_KINDS[0]
        } else if inh.has(CALL_DATA) {
            SPEC_KINDS[1]
        } else if inh.has(CALL_QUERY) {
            SPEC_KINDS[2]
        } else {
            return false;
        };
        node.items != [Item::Def(want)]
    }

    fn step(&self, node: &Node, inh: &State, _children: &[State], s: State) -> Option<State> {
        if self.rejects(node, inh) {
            return None;
        }
        if node.group {
            return Some(s);
        }
        let only = |d: &str| node.items == [Item::Def(d)];
        Some(match node.def {
            "set quantifier" if inh.has(IN_SETOP) => {
                if node.items == [Item::Token("ALL")] { s.with(Q_ALL) } else { s }
            }
            "set operator" => {
                let all = s.has(Q_ALL);
                let op = match node.items.first() {
                    Some(Item::Token("UNION")) => 0,
                    Some(Item::Token("EXCEPT")) => 2,
                    _ => 4,
                };
                s.without(Q_ALL).with(CONJ[op + usize::from(all)])
            }
            "query conjunction" if node.items == [Item::Token("OTHERWISE")] => s.with(CONJ[6]),
            "select statement" => s.with(SEL),
            "linear query statement" => {
                let sel = s.has(SEL);
                s.without(SEL).with(if sel { SEL_Q } else { NSEL_Q })
            }
            "focused linear query statement" | "focused linear data-modifying statement" => {
                s.with(FOC)
            }
            "ambient linear query statement" | "ambient linear data-modifying statement" => {
                s.with(AMB)
            }
            // 14.2 SR 3, 4, judged at each expression of the spine so that it holds one
            // conjunction and one focus; SR 6 of 9.2 (SELECT or not) too, the operands being
            // directly contained in the block.
            "composite query expression" => {
                if CONJ.iter().filter(|f| s.has(**f)).count() > 1
                    || (s.has(FOC) && s.has(AMB))
                    || (s.has(SEL_Q) && s.has(NSEL_Q))
                {
                    return None;
                }
                s
            }
            "composite query statement" => s.without_all(&CONJ),
            "statement" => {
                let k = if only("linear catalog-modifying statement") {
                    K_CAT
                } else if only("linear data-modifying statement") {
                    K_DATA
                } else {
                    K_QUERY
                };
                s.with(k)
            }
            "next statement" => s.with(HAS_NEXT),
            // 9.2 SR 4, 5, 6.
            "statement block" => {
                if (s.has(K_CAT) && s.has(HAS_NEXT))
                    || (s.has(FOC) && s.has(AMB))
                    || (s.has(SEL_Q) && s.has(NSEL_Q))
                {
                    return None;
                }
                s
            }
            // 9.1 SR 5, 6, 7.
            d if SPEC_KINDS.contains(&d) => {
                let (cat, data, query) = (s.has(K_CAT), s.has(K_DATA), s.has(K_QUERY));
                let ok = match d {
                    "catalog-modifying procedure specification" => !data && !query,
                    "data-modifying procedure specification" => !cat && data,
                    _ => !cat && !data,
                };
                if !ok {
                    return None;
                }
                let (foc, amb) = (s.has(FOC), s.has(AMB));
                let mut s = s.without_all(&BLOCK_FACTS).without_all(&CONJ).without(SEL);
                if d == "query specification" {
                    s.set(SPEC_FOC, foc);
                    s.set(SPEC_AMB, amb);
                }
                s
            }
            "nested query specification" => s,
            // 14.12 SR 26 b ii.
            "select query specification" => {
                let graph = node.items.contains(&Item::Def("graph expression"));
                if (graph && !s.has(SPEC_AMB)) || (!graph && !s.has(SPEC_FOC)) {
                    return None;
                }
                s.without(SPEC_FOC).without(SPEC_AMB)
            }
            _ => s.without(SPEC_FOC).without(SPEC_AMB),
        })
    }
}

/// 17.6 SR 1: a <catalog object parent reference> holds a solidus after its schema reference
/// unless that is the bare `/` (`//` is none). Reading: a parent reference with no schema
/// reference falls to the rule's "otherwise" and would need a solidus it cannot hold, so it is
/// refused (the literal text; the alternative stays a never target).
pub struct ParentSolidus;

/// Synthesized: the schema reference is the bare `/`.
const BARE_SCHEMA: Fact = 70;
/// Synthesized: the parent reference's own optional solidus is present.
const OWN_SOLIDUS: Fact = 71;

impl Rule for ParentSolidus {
    fn name(&self) -> &str {
        "parent reference solidus"
    }

    fn cite(&self) -> &str {
        "17.6 SR 1: no solidus after a bare / schema reference, a solidus after any other"
    }

    fn labels(&self) -> Vec<(Fact, String)> {
        labels(&[(BARE_SCHEMA, "bare-schema"), (OWN_SOLIDUS, "own-solidus")])
    }

    fn bookkeeping(&self) -> bool {
        true
    }

    fn step(&self, node: &Node, _inh: &State, _children: &[State], s: State) -> Option<State> {
        let owner = node.def.split('/').next().unwrap_or(node.def);
        if node.group {
            // The parent reference's `[ <solidus> ]`.
            return Some(if owner == "catalog object parent reference" && node.items == [Item::Def("solidus")] {
                s.with(OWN_SOLIDUS)
            } else {
                s
            });
        }
        Some(match node.def {
            "absolute catalog schema reference" if node.items == [Item::Def("solidus")] => {
                s.with(BARE_SCHEMA)
            }
            "absolute catalog schema reference" | "schema reference" => s,
            "catalog object parent reference" => {
                let schema = node.items.first() == Some(&Item::Def("schema reference"));
                let ok = schema && (s.has(BARE_SCHEMA) != s.has(OWN_SOLIDUS));
                if !ok {
                    return None;
                }
                s.without(BARE_SCHEMA).without(OWN_SOLIDUS)
            }
            _ => s.without(BARE_SCHEMA).without(OWN_SOLIDUS),
        })
    }
}

/// 18.6 SR 4, 18.7 SR 4: a property's value type is a supported property value type.
///
/// Reading under hypothesis H2: the supported ones are the predefined types that are neither
/// reference value types nor immaterial (4.3.4: every supported property value type is
/// material). Inherited from a <property value type> to its <value type> and on to its
/// <predefined type>, where the other alternatives are refused.
pub struct PropertyValueTypes;

const IN_PROPERTY_TYPE: Fact = 72;

impl Rule for PropertyValueTypes {
    fn name(&self) -> &str {
        "supported property value types"
    }

    fn cite(&self) -> &str {
        "18.6 SR 4, 18.7 SR 4: a property value type is supported: a predefined, material, non-reference type (H2)"
    }

    fn labels(&self) -> Vec<(Fact, String)> {
        labels(&[(IN_PROPERTY_TYPE, "in-property-type")])
    }

    fn bookkeeping(&self) -> bool {
        true
    }

    fn down(&self, node: &Node, inh: &State, pos: usize, _left: &[State], out: &mut State) {
        let child = owner_of(&node.items[pos]);
        let opens = node.def == "property value type" && child == Some("value type");
        let within = inh.has(IN_PROPERTY_TYPE)
            && node.def == "value type"
            && child == Some("predefined type");
        if opens || within {
            out.set(IN_PROPERTY_TYPE, true);
        }
    }

    fn rejects(&self, node: &Node, inh: &State) -> bool {
        if !inh.has(IN_PROPERTY_TYPE) || node.group {
            return false;
        }
        match node.def {
            "value type" => node.items != [Item::Def("predefined type")],
            "predefined type" => matches!(
                node.items,
                [Item::Def("reference value type" | "immaterial value type")]
            ),
            _ => false,
        }
    }

    fn step(&self, node: &Node, inh: &State, _children: &[State], s: State) -> Option<State> {
        if self.rejects(node, inh) {
            return None;
        }
        Some(s)
    }
}

/// 7.1 SR 6 c i-ii, 10.1 SR 8, 10.2 SR 8: an initializer's graph or binding table type is
/// assignable to the declared one.
///
/// Reading: graphs and tables are not typed (the types engine), so a closed declared type
/// (`GRAPH { .. }`, and every binding table type, which is always `TABLE { .. }`) cannot be
/// shown to hold and is refused; an open graph type (`ANY GRAPH`) holds whatever graph it
/// gets. Inherited from the initializer to its declared type, refused there.
pub struct ClosedInitializerTypes;

const IN_TABLE_INIT: Fact = 73;
const IN_GRAPH_INIT: Fact = 74;

impl Rule for ClosedInitializerTypes {
    fn name(&self) -> &str {
        "no closed declared graph or table type"
    }

    fn cite(&self) -> &str {
        "7.1 SR 6 c, 10.1 SR 8, 10.2 SR 8: a declared closed graph or binding table type is refused (reading: graph and table types are not followed)"
    }

    fn labels(&self) -> Vec<(Fact, String)> {
        labels(&[(IN_TABLE_INIT, "in-table-init"), (IN_GRAPH_INIT, "in-graph-init")])
    }

    fn bookkeeping(&self) -> bool {
        true
    }

    fn down(&self, node: &Node, inh: &State, pos: usize, _left: &[State], out: &mut State) {
        let owner = node.def.split('/').next().unwrap_or(node.def);
        let child = owner_of(&node.items[pos]);
        let to_type = |c: Option<&str>, t: &str| c == Some(t) || matches!(node.items[pos], Item::Group(_));
        if owner == "opt typed binding table initializer"
            && to_type(child, "binding table reference value type")
        {
            out.set(IN_TABLE_INIT, true);
        }
        if (owner == "opt typed graph initializer" && to_type(child, "graph reference value type"))
            || (inh.has(IN_GRAPH_INIT) && node.def == "graph reference value type")
        {
            out.set(IN_GRAPH_INIT, true);
        }
    }

    fn rejects(&self, node: &Node, inh: &State) -> bool {
        (inh.has(IN_TABLE_INIT) && node.def == "binding table reference value type")
            || (inh.has(IN_GRAPH_INIT) && node.def == "closed graph reference value type")
    }

    fn step(&self, node: &Node, inh: &State, _children: &[State], s: State) -> Option<State> {
        if self.rejects(node, inh) {
            return None;
        }
        Some(s)
    }
}

/// 18.9 SR 88: the components of a union are all possibly nullable or all known not nullable.
///
/// A component's nullability (SR 4: a <not null> without an intervening <value type>) is read
/// under an inherited context that starts at each <component type> and stops at the next
/// <value type> below its own, so only a union's components are copied: their <not null>
/// rises to the component's value type, which says nullable or not, and the <component type
/// list> judges them.
pub struct UnionNullability;

/// Inherited: within a component's own value type.
const IN_COMPONENT: Fact = 75;
const COMP_NOT_NULL: Fact = 76;
const COMP_NULLABLE: Fact = 77;
const RAW_NOT_NULL: Fact = 78;

impl Rule for UnionNullability {
    fn name(&self) -> &str {
        "union components agree on nullability"
    }

    fn cite(&self) -> &str {
        "18.9 SR 88: a union's components are all possibly nullable or all known not nullable"
    }

    fn labels(&self) -> Vec<(Fact, String)> {
        labels(&[
            (IN_COMPONENT, "in-component"),
            (COMP_NOT_NULL, "comp-not-null"),
            (COMP_NULLABLE, "comp-nullable"),
            (RAW_NOT_NULL, "raw-not-null"),
        ])
    }

    fn bookkeeping(&self) -> bool {
        true
    }

    fn down(&self, node: &Node, inh: &State, pos: usize, _left: &[State], out: &mut State) {
        let child = owner_of(&node.items[pos]);
        let opens = node.def == "component type" && child == Some("value type");
        // Not into a nested type's own specifications: their <not null>s are not the
        // component's (and the copies would multiply).
        const STOPS: [&str; 6] = [
            "value type",
            "nested graph type specification",
            "node type specification",
            "edge type specification",
            "field types specification",
            "property types specification",
        ];
        let within = inh.has(IN_COMPONENT) && child.is_some_and(|c| !STOPS.contains(&c));
        if opens || within {
            out.set(IN_COMPONENT, true);
        }
    }

    fn step(&self, node: &Node, inh: &State, _children: &[State], s: State) -> Option<State> {
        let owner = node.def.split('/').next().unwrap_or(node.def);
        if inh.has(IN_COMPONENT) {
            // SR 4 a, b: a <not null>, or NOTHING (the empty type), is known not nullable.
            if node.def == "not null" || node.def == "empty type" {
                return Some(s.with(RAW_NOT_NULL));
            }
            if node.def == "value type" && !node.group {
                let nn = s.has(RAW_NOT_NULL);
                let s = s.without(RAW_NOT_NULL);
                return Some(s.with(if nn { COMP_NOT_NULL } else { COMP_NULLABLE }));
            }
            return Some(s);
        }
        match owner {
            "component type" => Some(s),
            "component type list" => {
                if s.has(COMP_NOT_NULL) && s.has(COMP_NULLABLE) {
                    return None;
                }
                Some(if node.group {
                    s
                } else {
                    s.without(COMP_NOT_NULL).without(COMP_NULLABLE)
                })
            }
            _ => Some(s.without(COMP_NOT_NULL).without(COMP_NULLABLE).without(RAW_NOT_NULL)),
        }
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
const KEEP_SELECTIVE: Fact = 69;
const SR12: [Fact; 7] = [SEARCH, SELECTIVE_PATTERN, ONE, MANY, DIFF, MODE, KEEP_SELECTIVE];

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
            (KEEP_SELECTIVE, "keep-selective"),
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
            // 16.4 SR 6 puts a KEEP clause's prefix on every path pattern: a selective one
            // makes them all selective.
            "keep clause" => {
                let selective = s.has(SEARCH);
                let mut s = s.without(SEARCH);
                s.set(KEEP_SELECTIVE, selective);
                s
            }
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
                if (s.has(DIFF) || default)
                    && (s.has(SELECTIVE_PATTERN) || s.has(KEEP_SELECTIVE))
                    && s.has(MANY)
                {
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
