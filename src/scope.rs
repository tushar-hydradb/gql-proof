//! Scoping of binding variables (ISO/IEC 39075 2024 + Cor 1), compiled into the grammar as
//! a `refine::Rule`, so every query refers only to variables in scope, declares only names
//! it may, and returns columns it may.
//!
//! Variables come from a small pool of names (`x`, `y` by default), which `<binding
//! variable>`, a return item alias and a NEXT yield name choose from and spell. Stub
//! identifiers (`a`, `ab`, ...) never collide with the pool, so labels, property names and
//! subpath variables cannot clash with a variable.
//!
//! The environment a node inherits is, per name, unbound or bound as a node, edge, path,
//! value or group variable, or blocked: a field of the working record, which inside a CALL
//! body or a subquery is everything bound outside it. It only flows into nonterminals that
//! can reach a `<binding variable reference>` or are statements, so the rest of the grammar
//! is not multiplied. A statement synthesizes its outgoing environment; statements of a
//! sequence chain through `Rule::down`'s left siblings (14.3 SR 3-5). A statement whose
//! output nothing reads (a program's, a subquery's) forgets it.
//!
//! The automaton is sound, not complete: where a rule is hard to state finitely it forbids
//! more than ISO does, and `verify::scope` (written independently, from the standard alone)
//! checks every tree. Readings that forbid more than ISO:
//! - record fields are neither referenced, joined nor declared again: no correlated
//!   references in subqueries or CALL bodies (19.4, 20.6, 15.2 allow them). In exchange the
//!   rest needs no record flag: every name a body can reference is a column of its table
//! - a graph pattern references only its own variables (16.3 SR 25 lets it see the outer
//!   scope), and nothing nested in it declares names: no subquery, no `LET ... IN`
//! - a pattern variable joins an incoming one or another occurrence only as an unconditional
//!   singleton node or edge (16.3 SR 10, 16, 16.4 SR 3); path variables, and variables of a
//!   selective path pattern (16.6 SR 7), never join
//! - no element variable is declared under a union, multiset alternation, `?` or quantifier
//!   (16.7 SR 22 d-f would make it conditional or a group); one subpath variable per pattern
//! - an element WHERE or property specification sees its own variable; a parenthesized WHERE
//!   sees what its own expression declares as a singleton, no path variable (16.7 SR 21,
//!   24, 4.11.5)
//! - group variables are never referenced (20.12 SR 11, 20.1 SR 7 allow some)
//! - aggregates appear only as a return item's own; a sort key holds none and no nested
//!   query, and ORDER BY after an aggregating, grouping or DISTINCT RETURN sees only its
//!   columns (14.10 SR 4); with GROUP BY, every item groups or aggregates (14.11 SR 10)
//! - no column is named like a field of the record, NEXT or not (9.2 SR 12 c)
//! - one SET or REMOVE item per variable (13.3 SR 4-5); every select item is named
//! - names a named procedure's YIELD gives without an alias, and SELECT's, bind nothing
//! - an INSERT reuses a bound variable only for a node with nothing else in its filler, and
//!   declares each name once (16.5 SR 10-11)
//! - a nested `{ ... }` data-modifying procedure leaves nothing referenceable behind

use crate::cfg::{Cfg, Sym};
use crate::refine::{Fact, Item, Node, Rule, State};
use std::collections::HashSet;

pub const DEFAULT_NAMES: &[&str] = &["x", "y"];

const BASE: Fact = 1 << 24;
const PER_NAME: Fact = 64;
const MAX_NAMES: usize = 32;
const GLOBAL: Fact = BASE + MAX_NAMES as Fact * PER_NAME;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    Node,
    Edge,
    Path,
    Value,
    Group,
    /// A field of the working record, kept in the slot of its flag.
    Blocked,
}

/// The kinds a column or a yielded name can have.
const KINDS: [Kind; 5] = [Kind::Node, Kind::Edge, Kind::Path, Kind::Value, Kind::Group];

impl Kind {
    fn code(self) -> Fact {
        self as Fact
    }

    fn label(self) -> &'static str {
        match self {
            Kind::Node => "node",
            Kind::Edge => "edge",
            Kind::Path => "path",
            Kind::Value => "value",
            Kind::Group => "group",
            Kind::Blocked => "blocked",
        }
    }
}

// Facts per name, as offsets in its block.
/// Inherited: bound as a kind (5 facts).
const IN: Fact = 0;
/// Inherited: a field of the working record (the `Blocked` kind).
const IN_RECORD: Fact = 5;
/// Synthesized: a statement's outgoing environment (5 facts and the record flag).
const OUT: Fact = 6;
const OUT_RECORD: Fact = 11;
/// Synthesized: declared by a graph pattern as a node, edge or path (3 facts), and whether
/// opaque: declared under a union, `?` or a quantifier, so conditional or a group, and here
/// neither referenced nor joined.
const DECL: Fact = 12;
const DECL_OPAQUE: Fact = 15;
/// Synthesized: declared by a selective path pattern, so never joined (16.6 SR 7).
const DECL_SELECTIVE: Fact = 16;
/// Synthesized: a `<binding variable>` spells this name.
const CHOSEN: Fact = 17;
/// Synthesized: an `<identifier>` that must be a pool name spells this one.
const SPELLED: Fact = 18;
const ELEMENT: Fact = 19;
const PATH_VAR: Fact = 20;
/// Synthesized: a `<binding variable reference>` names it.
const REF: Fact = 21;
/// Synthesized: the subtree is nothing but a reference to it.
const BARE: Fact = 22;
/// Synthesized: referenced outside any aggregate.
const USED: Fact = 23;
/// Synthesized: declared as a new name by LET, FOR, a YIELD alias or a definition.
const NEW: Fact = 24;
/// Synthesized: a return column of a kind (5 facts).
const COLUMN: Fact = 25;
const ALIASED: Fact = 30;
const KEY: Fact = 31;
const LISTED: Fact = 32;
const YIELDED: Fact = 33;
/// Synthesized: a NEXT YIELD column of a kind (5 facts).
const YIELD_KIND: Fact = 34;
/// Synthesized: the variable a SET or REMOVE item changes.
const TARGET: Fact = 39;

// Facts for the whole state.
const STATEMENT: Fact = GLOBAL;
const RESULT: Fact = GLOBAL + 1;
const PLAIN: Fact = GLOBAL + 2;
const AGGREGATES: Fact = GLOBAL + 3;
const STAR: Fact = GLOBAL + 4;
const DISTINCT: Fact = GLOBAL + 5;
const GROUPED: Fact = GLOBAL + 6;
const SELECTIVE: Fact = GLOBAL + 7;
const SPELL: Fact = GLOBAL + 8;
const IN_YIELD: Fact = GLOBAL + 9;
/// Inherited: under a return item or a pattern's YIELD, where references outside aggregates
/// are collected and aggregates may appear.
const COLLECT: Fact = GLOBAL + 12;
/// Inherited: under a union, multiset alternation, `?` or quantifier, where no element
/// variable is declared (reading: their variables could not be referenced or joined here
/// anyway, and the declaration is covered elsewhere).
const NO_DECL: Fact = GLOBAL + 13;
/// Inherited: nothing reads this statement's output (a whole program's, a subquery's in an
/// expression), so it is forgotten instead of making a copy per outgoing environment.
const DISCARD: Fact = GLOBAL + 14;
/// Synthesized: the statement ends in FINISH.
const FINISHED: Fact = GLOBAL + 15;
/// Synthesized: an element pattern has a WHERE.
const ELEMENT_WHERE: Fact = GLOBAL + 16;
/// Synthesized: a SELECT has a body (FROM), a select item an alias.
const SELECT_FROM: Fact = GLOBAL + 17;
const SELECT_ALIAS: Fact = GLOBAL + 18;
/// Inherited: in a named procedure call's YIELD, whose names are spelled and declared.
const IN_CALL_YIELD: Fact = GLOBAL + 19;
/// Synthesized: the subtree derives the empty string.
const EMPTY: Fact = GLOBAL + 20;
/// Inherited: inside the value expression an aggregating value expression immediately
/// contains, where an aggregate is no horizontal aggregation (20.1 SR 7).
const AGGREGABLE: Fact = GLOBAL + 21;
/// Inherited: inside a sort key, where no query is nested (14.10 SR 4).
const IN_SORT_KEY: Fact = GLOBAL + 22;
/// Synthesized: a subpath variable is declared (all are spelled alike).
const SUBPATH: Fact = GLOBAL + 23;
/// Synthesized: a return item neither aggregates nor is a bare reference.
const LOOSE: Fact = GLOBAL + 24;
/// Inherited: inside a graph pattern, where no query is nested (reading: a nested pattern
/// would see, and join, the enclosing pattern's variables, 16.3 SR 25).
const IN_PATTERN: Fact = GLOBAL + 25;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Bound {
    kind: Kind,
    record: bool,
}

type Env = Vec<Option<Bound>>;

/// Statements and the clauses around their variables. They get the environment with its
/// record flags, and chain it left to right.
const STATEMENTS: &[&str] = &[
    "GQL-program",
    "program activity",
    "session activity",
    "transaction activity",
    "procedure specification",
    "query specification",
    "catalog-modifying procedure specification",
    "data-modifying procedure specification",
    "procedure body",
    "statement block",
    "statement",
    "next statement",
    "yield clause",
    "yield item list",
    "yield item",
    "yield item name",
    "yield item alias",
    "composite query statement",
    "composite query expression",
    "composite query primary",
    "linear query statement",
    "focused linear query statement",
    "focused linear query statement part",
    "focused linear query and primitive result statement part",
    "focused primitive result statement",
    "focused nested query specification",
    "ambient linear query statement",
    "simple linear query statement",
    "simple query statement",
    "primitive query statement",
    "call query statement",
    "call procedure statement",
    "procedure call",
    "inline procedure call",
    "named procedure call",
    "nested procedure specification",
    "nested query specification",
    "match statement",
    "simple match statement",
    "optional match statement",
    "optional operand",
    "match statement block",
    "let statement",
    "let variable definition list",
    "let variable definition",
    "value variable definition",
    "for statement",
    "for item",
    "for item alias",
    "for ordinality or offset",
    "filter statement",
    "order by and page statement",
    "primitive result statement",
    "return statement",
    "return statement body",
    "return item list",
    "return item",
    "group by clause",
    "grouping element list",
    "grouping element",
    "select statement",
    "linear data-modifying statement",
    "focused linear data-modifying statement",
    "focused linear data-modifying statement body",
    "focused nested data-modifying procedure specification",
    "ambient linear data-modifying statement",
    "ambient linear data-modifying statement body",
    "nested data-modifying procedure specification",
    "simple linear data-accessing statement",
    "simple data-accessing statement",
    "simple data-modifying statement",
    "primitive data-modifying statement",
    "call data-modifying procedure statement",
    "insert statement",
    "insert graph pattern",
    "insert path pattern list",
    "insert path pattern",
    "insert node pattern",
    "insert edge pattern",
    "insert edge pointing left",
    "insert edge pointing right",
    "insert edge undirected",
    "insert element pattern filler",
    "set statement",
    "set item list",
    "set item",
    "remove statement",
    "remove item list",
    "remove item",
    "delete statement",
    "delete item list",
    "binding variable definition block",
    "binding variable definition",
    "graph variable definition",
    "binding table variable definition",
    "linear catalog-modifying statement",
];

/// Statement nodes whose children do not chain: branches of a set operation each get the
/// statement's input, the rest are handled one by one in `down`.
const NO_CHAIN: &[&str] = &[
    "composite query expression",
    "primitive result statement",
    "next statement",
    "inline procedure call",
];

/// Bodies in braces: a scope of their own.
const NESTED: &[&str] = &[
    "nested procedure specification",
    "nested query specification",
    "nested data-modifying procedure specification",
    "focused nested data-modifying procedure specification",
    "focused nested query specification",
];

/// Where references outside aggregates are still collected: a RETURN checks them against
/// its grouping.
const RETURN_FAMILY: &[&str] = &[
    "return statement body",
    "return item list",
    "return item",
    "group by clause",
    "grouping element list",
    "grouping element",
];

/// The definition a desugaring group belongs to, or the definition itself.
fn owner(def: &str) -> &str {
    def.split('/').next().unwrap_or(def)
}

pub struct Scope {
    names: Vec<String>,
    /// Definitions and groups whose trees can hold a `<binding variable reference>` or a
    /// `<subpath variable>`: what reads the environment.
    reaches: HashSet<String>,
}

impl Scope {
    pub fn new(cfg: &Cfg, names: &[&str]) -> Scope {
        assert!(names.len() <= MAX_NAMES, "at most {MAX_NAMES} names");
        let mut reach = vec![false; cfg.nts.len()];
        let mut changed = true;
        while changed {
            changed = false;
            for prod in &cfg.prods {
                if reach[prod.lhs as usize] {
                    continue;
                }
                let hit = matches!(
                    cfg.base(prod.lhs),
                    "binding variable reference" | "subpath variable"
                ) || prod
                    .rhs
                    .iter()
                    .any(|s| matches!(*s, Sym::Nt(c) if reach[c as usize]));
                if hit {
                    reach[prod.lhs as usize] = true;
                    changed = true;
                }
            }
        }
        Scope {
            names: names.iter().map(|s| s.to_string()).collect(),
            reaches: (0..cfg.nts.len())
                .filter(|&n| reach[n])
                .map(|n| cfg.base(n as u32).to_string())
                .collect(),
        }
    }

    fn n(&self) -> usize {
        self.names.len()
    }

    fn statement(def: &str) -> bool {
        STATEMENTS.contains(&owner(def))
    }

    /// An environment from its facts: a record field reads back as `Blocked`.
    fn read(&self, s: &State, kinds: Fact, record: Fact) -> Env {
        (0..self.n())
            .map(|i| {
                if s.has(fact(i, record)) {
                    return Some(Bound {
                        kind: Kind::Blocked,
                        record: true,
                    });
                }
                KINDS
                    .iter()
                    .find(|k| s.has(fact(i, kinds + k.code())))
                    .map(|&kind| Bound {
                        kind,
                        record: false,
                    })
            })
            .collect()
    }

    /// A record field is written as its flag alone, whatever its kind was: blocked.
    fn write(&self, s: &mut State, env: &Env, kinds: Fact, record: Fact) {
        for (i, b) in env.iter().enumerate() {
            match b {
                Some(b) if b.record || b.kind == Kind::Blocked => s.set(fact(i, record), true),
                Some(b) => s.set(fact(i, kinds + b.kind.code()), true),
                None => {}
            }
        }
    }

    fn names_with(&self, s: &State, code: Fact) -> Vec<usize> {
        (0..self.n()).filter(|&i| s.has(fact(i, code))).collect()
    }

    fn decl(&self, s: &State, i: usize) -> Option<Kind> {
        [Kind::Node, Kind::Edge, Kind::Path]
            .into_iter()
            .find(|k| s.has(fact(i, DECL + k.code())))
    }

    /// What a graph pattern declares, as an environment: groups as group variables.
    fn declared(&self, s: &State) -> Env {
        (0..self.n())
            .map(|i| {
                self.decl(s, i).map(|kind| Bound {
                    kind: if s.has(fact(i, DECL_OPAQUE)) {
                        Kind::Group
                    } else {
                        kind
                    },
                    record: false,
                })
            })
            .collect()
    }

    fn label(&self, f: Fact) -> String {
        if f >= GLOBAL {
            return match f - GLOBAL {
                0 => "statement",
                1 => "result",
                2 => "plain",
                3 => "aggregates",
                4 => "star",
                5 => "distinct",
                6 => "grouped",
                7 => "selective",
                8 => "spell",
                9 => "in-yield",
                10 => "in-node",
                11 => "in-edge",
                12 => "collect",
                13 => "no-decl",
                14 => "discard",
                15 => "finished",
                16 => "element-where",
                17 => "select-from",
                18 => "select-alias",
                19 => "in-call-yield",
                20 => "empty",
                21 => "aggregable",
                22 => "in-sort-key",
                23 => "subpath",
                24 => "loose",
                25 => "in-pattern",
                _ => "?",
            }
            .to_string();
        }
        let i = ((f - BASE) / PER_NAME) as usize;
        let code = (f - BASE) % PER_NAME;
        let name = &self.names[i];
        let kind = |c: Fact| KINDS[c as usize].label();
        match code {
            c if c < IN_RECORD => format!("{name}:{}", kind(c)),
            IN_RECORD => format!("{name}:record"),
            c if (OUT..OUT_RECORD).contains(&c) => format!("{name}>{}", kind(c - OUT)),
            OUT_RECORD => format!("{name}>record"),
            c if (DECL..DECL_OPAQUE).contains(&c) => format!("{name}=decl-{}", kind(c - DECL)),
            DECL_OPAQUE => format!("{name}=opaque"),
            DECL_SELECTIVE => format!("{name}=selective"),
            CHOSEN => name.to_string(),
            SPELLED => format!("{name}-alias"),
            ELEMENT => format!("{name}-element"),
            PATH_VAR => format!("{name}-pathvar"),
            REF => format!("{name}-ref"),
            BARE => format!("{name}-bare"),
            USED => format!("{name}-used"),
            NEW => format!("{name}-new"),
            c if (COLUMN..ALIASED).contains(&c) => format!("{name}-column-{}", kind(c - COLUMN)),
            ALIASED => format!("{name}-aliased"),
            KEY => format!("{name}-key"),
            LISTED => format!("{name}-listed"),
            YIELDED => format!("{name}-yielded"),
            TARGET => format!("{name}-target"),
            c if c >= YIELD_KIND => format!("{name}-yield-{}", kind(c - YIELD_KIND)),
            _ => format!("{name}-unused"),
        }
    }

    /// The environment a child gets, before projection.
    fn child_env(&self, node: &Node, inh: &State, pos: usize, left: &[State]) -> Env {
        let mut env = self.read(inh, IN, IN_RECORD);
        let def = node.def;
        let last_out = || left.iter().rev().find(|s| s.has(STATEMENT));
        if owner(def) == "select statement" {
            return vec![None; self.n()];
        }
        // A nested procedure or query is a body of its own: what is bound outside is its
        // record (15.1 SR 5-7, 9.2), blocked here.
        if NESTED.contains(&owner(def)) {
            for b in env.iter_mut().flatten() {
                b.record = true;
            }
            return env;
        }
        if node.group {
            if Self::statement(def)
                && !NO_CHAIN.contains(&owner(def))
                && let Some(o) = last_out()
            {
                env = self.read(o, OUT, OUT_RECORD);
            }
            return env;
        }
        match def {
            // 14.10 SR 4: the columns, and the names before the projection when it neither
            // aggregates, groups nor removes duplicates.
            "primitive result statement" if pos > 0 => {
                if let Some(ret) = left.first().filter(|s| s.has(STATEMENT)) {
                    let columns = self.read(ret, OUT, OUT_RECORD);
                    if ret.has(PLAIN) {
                        amend(&mut env, &columns);
                    } else {
                        env = columns;
                    }
                }
            }
            // 16.2 SR 3-4: a USE graph expression sees the record and a unit table.
            "use graph clause" => env = record_part(&env),
            // 9.2 SR 12, 16.14: the record and what the YIELD keeps.
            "next statement" => {
                if let Some(y) = left
                    .iter()
                    .find(|s| !self.names_with(s, YIELDED).is_empty())
                {
                    let record: Env = env.iter().map(|b| b.filter(|b| b.record)).collect();
                    let yielded = self.read(y, YIELD_KIND, IN_RECORD);
                    env = record;
                    amend(&mut env, &yielded);
                }
            }
            // 15.1 SR 5-7, 15.2 SR 3, 7: the body sees the listed names, or all, as its
            // record, and a unit table.
            // The scope clause itself (position 0) sees the call's scope.
            "inline procedure call" if pos > 0 => {
                let listed = left.iter().find(|s| !self.names_with(s, LISTED).is_empty());
                env = env
                    .iter()
                    .enumerate()
                    .map(|(i, b)| {
                        b.filter(|_| listed.is_none_or(|l| l.has(fact(i, LISTED))))
                            .map(|b| Bound { record: true, ..b })
                    })
                    .collect();
            }
            // 16.3 SR 12: YIELD names the pattern's own variables.
            "graph pattern binding table" if pos > 0 => {
                env = left.first().map_or(env, |gp| self.declared(gp));
            }
            // 20.12 SR 10, 11: the pattern's variables are in scope in its WHERE.
            "graph pattern" => {
                for l in left {
                    amend(&mut env, &self.declared(l));
                }
            }
            // 16.7 SR 21: an element WHERE or property specification sees its variable, as
            // an element (expressions do not tell nodes from edges).
            "element pattern filler" => {
                let kind = Kind::Node;
                for l in left {
                    for i in self.names_with(l, ELEMENT) {
                        env[i] = Some(Bound {
                            kind,
                            record: false,
                        });
                    }
                }
            }
            // 16.7 SR 24, 4.11.5: no path variables, local singletons only.
            "parenthesized path pattern expression" => {
                for b in env.iter_mut() {
                    if b.is_some_and(|b| b.kind == Kind::Path) {
                        *b = None;
                    }
                }
                for l in left {
                    let local: Env = self
                        .declared(l)
                        .into_iter()
                        .map(|b| b.filter(|b| !matches!(b.kind, Kind::Group | Kind::Path)))
                        .collect();
                    amend(&mut env, &local);
                }
            }
            // 4.11.5: a selective path pattern references nothing declared outside it.
            "path pattern" if left.iter().any(|s| s.has(SELECTIVE)) => {
                env = vec![None; self.n()];
            }
            // 20.5: the IN expression sees the definitions.
            "let value expression" => {
                for l in left {
                    for i in self.names_with(l, NEW) {
                        env[i] = Some(Bound {
                            kind: Kind::Value,
                            record: false,
                        });
                    }
                }
            }
            d if Self::statement(d) && !NO_CHAIN.contains(&d) => {
                if let Some(o) = last_out() {
                    env = self.read(o, OUT, OUT_RECORD);
                }
            }
            _ => {}
        }
        env
    }
}

fn fact(i: usize, code: Fact) -> Fact {
    BASE + i as Fact * PER_NAME + code
}

/// `env` amended with `with`: its bindings win (4.15.4).
fn amend(env: &mut Env, with: &Env) {
    for (e, w) in env.iter_mut().zip(with) {
        if w.is_some() {
            *e = *w;
        }
    }
}

fn record_part(env: &Env) -> Env {
    env.iter().map(|b| b.filter(|b| b.record)).collect()
}

fn others(s: &State) -> State {
    s.facts()
        .filter(|&f| f < BASE)
        .fold(State::default(), |s, f| s.with(f))
}

impl Rule for Scope {
    fn name(&self) -> &str {
        "binding variables in scope"
    }

    fn cite(&self) -> &str {
        "20.12 SR 8, 14.3 SR 3-5, 14.4, 14.7, 14.8, 14.10 SR 4, 14.11, 16.3, 16.4 SR 3-5, 16.7 SR 21-24, 9.2 SR 12, 15.1, 15.2: variables are referenced in scope and declared new"
    }

    fn labels(&self) -> Vec<(Fact, String)> {
        let per_name = (0..self.n()).flat_map(|i| (0..=TARGET).map(move |c| fact(i, c)));
        per_name
            .chain(GLOBAL..=IN_PATTERN)
            .map(|f| (f, self.label(f)))
            .collect()
    }

    fn bookkeeping(&self) -> bool {
        true
    }

    fn down(&self, node: &Node, inh: &State, pos: usize, left: &[State], out: &mut State) {
        let child = match node.items[pos] {
            Item::Def(c) | Item::Group(c) => c,
            _ => return,
        };
        let parent = owner(node.def);
        // Roles: which identifiers spell a pool name.
        let yield_family = [
            "next statement",
            "named procedure call",
            "yield clause",
            "yield item list",
            "yield item",
            "yield item name",
            "field name",
        ];
        let in_family = yield_family.contains(&owner(child));
        if in_family && (parent == "next statement" || inh.has(IN_YIELD)) {
            out.set(IN_YIELD, true);
        }
        if in_family && (parent == "named procedure call" || inh.has(IN_CALL_YIELD)) {
            out.set(IN_CALL_YIELD, true);
        }
        let spelled_yield = inh.has(IN_YIELD) || inh.has(IN_CALL_YIELD);
        let alias = matches!(parent, "return item alias" | "select item alias");
        if child == "identifier" && (alias || spelled_yield) {
            out.set(SPELL, true);
        }
        let statement = Self::statement(child);
        let collects = matches!(parent, "return item" | "graph pattern yield clause")
            || inh.has(COLLECT) && !matches!(parent, "exists predicate" | "value query expression");
        if collects && !statement {
            out.set(COLLECT, true);
        }
        // 20.1 SR 7: an aggregate is a return item's own only under the value expression its
        // aggregating value expression immediately contains, not under a nested one (a CAST
        // operand, a function argument).
        let aggregable = parent == "aggregating value expression"
            || inh.has(AGGREGABLE)
                && child != "value expression"
                && !matches!(parent, "exists predicate" | "value query expression");
        if aggregable && !statement {
            out.set(AGGREGABLE, true);
        }
        if (parent == "graph pattern" || inh.has(IN_PATTERN)) && !statement {
            out.set(IN_PATTERN, true);
        }
        if (parent == "sort key" || inh.has(IN_SORT_KEY)) && !statement {
            out.set(IN_SORT_KEY, true);
        }
        let no_decl = matches!(
            parent,
            "quantified path primary"
                | "questioned path primary"
                | "path pattern union"
                | "path multiset alternation"
        ) || inh.has(NO_DECL);
        if no_decl && !statement && !matches!(child, "graph pattern" | "nested query specification")
        {
            out.set(NO_DECL, true);
        }
        if statement {
            // A program's output, and a subquery's in an expression, are never read. A
            // statement passes that on to the child whose output is its own, its last one,
            // except where outputs are compared (set operations), read by the next sibling
            // (a RETURN's by its ORDER BY) or are the result (CALL's body).
            let last = node
                .items
                .iter()
                .rposition(|it| matches!(it, Item::Def(_) | Item::Group(_)));
            let passes = inh.has(DISCARD)
                && Self::statement(node.def)
                && Some(pos) == last
                && !matches!(
                    parent,
                    "composite query expression" | "inline procedure call"
                )
                && !(parent == "primitive result statement" && pos == 0);
            if parent == "GQL-program" || !Self::statement(node.def) || passes {
                out.set(DISCARD, true);
            }
        }
        if !statement && !self.reaches.contains(child) {
            return;
        }
        let mut env = self.child_env(node, inh, pos, left);
        if child == "graph pattern" {
            // Reading: a graph pattern references only its own variables (16.3 SR 25 lets it
            // see the outer scope); the outer ones stay bound, for its subpath names. Joins
            // with them are checked by the MATCH.
            for b in env.iter_mut().flatten() {
                b.record = true;
            }
        }
        if statement && !Self::statement(node.def) {
            // Entering a subquery from an expression: the enclosing names are its record
            // (19.4, 20.6 SR 11-12).
            for b in env.iter_mut().flatten() {
                b.record = true;
            }
        }
        if !statement {
            // An expression only asks whether a name is an element, a path or a value
            // variable, or bound and not referenceable; exact kinds are read at statement
            // level (return items, MATCH).
            for b in env.iter_mut().flatten() {
                b.kind = match b.kind {
                    Kind::Edge => Kind::Node,
                    Kind::Group => Kind::Blocked,
                    k => k,
                };
            }
        }
        self.write(out, &env, IN, IN_RECORD);
    }

    fn steps(&self, node: &Node, inh: &State, children: &[State], syn: State) -> Vec<State> {
        let def = node.def;
        let n = self.n();
        let env = self.read(inh, IN, IN_RECORD);
        let has = |code: Fact, i: usize| children.iter().any(|c| c.has(fact(i, code)));
        let count = |code: Fact, i: usize| children.iter().filter(|c| c.has(fact(i, code))).count();
        let mut out = others(&syn);

        // Choosing a name.
        if def == "binding variable" || (def == "identifier" && inh.has(SPELL)) {
            let code = if def == "identifier" { SPELLED } else { CHOSEN };
            return (0..n)
                .filter(|&i| node.text.is_none_or(|t| t == self.names[i]))
                .map(|i| out.clone().with(fact(i, code)))
                .collect();
        }

        // Defaults: carry what flows up, check what meets.
        let union_like = matches!(
            owner(def),
            "path pattern union" | "path multiset alternation"
        );
        for i in 0..n {
            for code in [ELEMENT, PATH_VAR, USED, KEY, TARGET] {
                if has(code, i) {
                    out.set(fact(i, code), true);
                }
            }
            // A name declared twice in one place (16.4 SR 5, 4.11.4, 10.3 SR 7, 14.11 SR 11).
            for code in [NEW, COLUMN_ANY, LISTED, YIELDED, TARGET] {
                let k = if code == COLUMN_ANY {
                    children.iter().filter(|c| column(c, i).is_some()).count()
                } else {
                    count(code, i)
                };
                if k > 1 {
                    return vec![];
                }
            }
            if has(NEW, i) {
                out.set(fact(i, NEW), true);
            }
            if has(LISTED, i) {
                out.set(fact(i, LISTED), true);
            }
            if has(YIELDED, i) {
                out.set(fact(i, YIELDED), true);
                for k in KINDS {
                    if has(YIELD_KIND + k.code(), i) {
                        out.set(fact(i, YIELD_KIND + k.code()), true);
                    }
                }
            }
            if let Some(k) = children.iter().find_map(|c| column(c, i)) {
                out.set(fact(i, COLUMN + k.code()), true);
            }
            // Pattern declarations: two occurrences join (16.4 SR 3, 16.7 SR 22 c), operands
            // of a union are alternatives (16.7 SR 22 d).
            let decls: Vec<(Kind, bool)> = children
                .iter()
                .filter_map(|c| self.decl(c, i).map(|k| (k, c.has(fact(i, DECL_OPAQUE)))))
                .collect();
            if let Some(&(kind, _)) = decls.first() {
                if decls.iter().any(|d| d.0 != kind) {
                    return vec![];
                }
                let joins = decls.len() > 1 && !union_like;
                // 16.5 SR 10-11 (reading): an insert pattern declares each name once.
                let insert = owner(def).starts_with("insert");
                let selective = children.iter().any(|c| c.has(fact(i, DECL_SELECTIVE)));
                if joins && (kind == Kind::Path || insert || selective || decls.iter().any(|d| d.1))
                {
                    return vec![];
                }
                out.set(fact(i, DECL + kind.code()), true);
                out.set(fact(i, DECL_OPAQUE), decls.iter().any(|d| d.1));
                out.set(fact(i, DECL_SELECTIVE), selective);
            }
            if children.iter().any(|c| c.has(fact(i, SPELLED)))
                && matches!(owner(def), "field name" | "yield item name" | "yield item")
            {
                out.set(fact(i, SPELLED), true);
            }
            if has(ALIASED, i) && owner(def) == "return item" {
                out.set(fact(i, ALIASED), true);
            }
        }
        for g in [AGGREGATES, DISTINCT, GROUPED, SELECTIVE, STAR, SUBPATH] {
            if children.iter().any(|c| c.has(g)) {
                out.set(g, true);
            }
        }
        // 16.4 SR 4 (reading): subpath variables are all spelled alike, so one per pattern.
        if children.iter().filter(|c| c.has(SUBPATH)).count() > 1 {
            return vec![];
        }
        // Flags only the node above reads, carried only that far.
        for (g, through) in [
            (
                ELEMENT_WHERE,
                &["element pattern predicate", "element pattern filler"][..],
            ),
            (SELECT_FROM, &["select statement"][..]),
            (SELECT_ALIAS, &["select item"][..]),
            (LOOSE, &["return item list", "return statement body"][..]),
        ] {
            if through.contains(&owner(def)) && children.iter().any(|c| c.has(g)) {
                out.set(g, true);
            }
        }
        // A bare reference stays bare through nodes whose other children derive nothing:
        // `x` is bare, `NOT x` and `(x)` are not.
        let tokens = node
            .items
            .iter()
            .any(|it| matches!(it, Item::Token(_) | Item::Prose(_)));
        let nonempty: Vec<&State> = children.iter().filter(|c| !c.has(EMPTY)).collect();
        out.set(EMPTY, !tokens && nonempty.is_empty());
        if let [only] = nonempty[..]
            && !tokens
        {
            for i in 0..n {
                if only.has(fact(i, BARE)) {
                    out.set(fact(i, BARE), true);
                }
            }
        }
        // A statement's output: its last statement's (14.3 SR 6). It goes no higher than
        // statements: a subquery's output stays inside its expression.
        if Self::statement(def)
            && let Some(last) = children.iter().rev().find(|c| c.has(STATEMENT))
        {
            out = copy_out(out, last, n);
        }

        let refs: Vec<usize> = (0..n).filter(|&i| has(REF, i)).collect();
        let chosen: Vec<usize> = (0..n).filter(|&i| has(CHOSEN, i)).collect();
        let kind_of = |i: usize| env[i].map(|b| b.kind);
        let set_out = |out: State, env: &Env, result: bool| -> State {
            let mut out = clear_out(out, n).with(STATEMENT);
            out.set(RESULT, result);
            self.write(&mut out, env, OUT, OUT_RECORD);
            out
        };

        // 15.2 SR 6 a ii: a scope clause lists each name once.
        if owner(def) == "binding variable reference list" {
            for &i in &refs {
                if has(LISTED, i) {
                    return vec![];
                }
                out = out.with(fact(i, LISTED));
            }
        }

        match def {
            // 20.12 SR 8: a reference names something in scope.
            "binding variable reference" => {
                for &i in &chosen {
                    if !matches!(
                        kind_of(i),
                        Some(Kind::Node | Kind::Edge | Kind::Path | Kind::Value)
                    ) {
                        return vec![];
                    }
                    out = out.with(fact(i, REF)).with(fact(i, BARE));
                    out.set(fact(i, USED), inh.has(COLLECT));
                }
            }
            // 16.10 SR 3, 16.9 SR 2: of the kind the reference needs.
            "element variable reference"
            | "set property item"
            | "set all properties item"
            | "set label item"
            | "remove property item"
            | "remove label item" => {
                if refs
                    .iter()
                    .any(|&i| !matches!(kind_of(i), Some(Kind::Node | Kind::Edge)))
                {
                    return vec![];
                }
                // 13.3 SR 4-5 (reading): one item per variable in a SET or REMOVE.
                if def != "element variable reference" {
                    for &i in &refs {
                        out = out.with(fact(i, TARGET));
                    }
                }
            }
            "path variable reference" => {
                if refs.iter().any(|&i| kind_of(i) != Some(Kind::Path)) {
                    return vec![];
                }
            }
            // 14.11 SR 10: a grouping element is a column.
            "grouping element" => {
                for &i in &refs {
                    if env[i].is_none_or(|b| b.record) {
                        return vec![];
                    }
                    out = out.with(fact(i, KEY)).without(fact(i, USED));
                }
            }
            "graph pattern yield item" => {
                for i in 0..n {
                    if out.has(fact(i, USED)) {
                        out = out.without(fact(i, USED)).with(fact(i, YIELDED));
                    }
                }
            }
            "element variable" => {
                if inh.has(NO_DECL) {
                    return vec![];
                }
                for &i in &chosen {
                    out = out.with(fact(i, ELEMENT));
                }
            }
            "path variable" => {
                for &i in &chosen {
                    out = out.with(fact(i, PATH_VAR));
                }
            }
            "let variable definition"
            | "value variable definition"
            | "graph variable definition"
            | "binding table variable definition"
            | "for item alias"
            | "for ordinality or offset"
            | "yield item alias" => {
                for &i in &chosen {
                    out = out.with(fact(i, NEW));
                }
            }
            "node pattern" | "insert node pattern" => {
                out = self.element_to_decl(out, Kind::Node);
            }
            "edge pattern"
            | "insert edge pointing left"
            | "insert edge pointing right"
            | "insert edge undirected" => {
                out = self.element_to_decl(out, Kind::Edge);
            }
            // A bound variable in INSERT is an existing node, inserted as is (reading).
            "insert element pattern filler" => {
                let bound = |i: usize| out.has(fact(i, ELEMENT)) && env[i].is_some();
                if node.items.len() > 1 && (0..n).any(bound) {
                    return vec![];
                }
            }
            "element pattern where clause" => out = out.with(ELEMENT_WHERE),
            // 16.7 SR 21: an element WHERE needs the element's variable.
            "element pattern filler" => {
                if out.has(ELEMENT_WHERE) && self.names_with(&out, ELEMENT).is_empty() {
                    return vec![];
                }
                out = out.without(ELEMENT_WHERE);
            }
            // 16.3 SR 3-4: one name, one variable.
            "path pattern" => {
                for i in 0..n {
                    if out.has(fact(i, PATH_VAR)) {
                        if self.decl(&out, i).is_some() {
                            return vec![];
                        }
                        out = out
                            .without(fact(i, PATH_VAR))
                            .with(fact(i, DECL + Kind::Path.code()));
                    }
                }
                // 16.6 SR 7: what a selective path pattern declares is joined nowhere else.
                if out.has(SELECTIVE) {
                    let declared: Vec<usize> =
                        (0..n).filter(|&i| self.decl(&out, i).is_some()).collect();
                    for i in declared {
                        out = out.with(fact(i, DECL_SELECTIVE));
                    }
                }
                out = out.without(SELECTIVE);
            }
            // 16.3 SR 7, 9: a subpath variable is none of the incoming names.
            "subpath variable" => {
                if let Some(t) = node.text
                    && (0..n).any(|i| self.names[i] == t && env[i].is_some())
                {
                    return vec![];
                }
                out = out.with(SUBPATH);
            }
            "graph pattern" => out = out.without(SUBPATH),
            "path search prefix" => {
                out.set(SELECTIVE, node.items != [Item::Def("all path search")]);
            }
            "keep clause" => out = out.without(SELECTIVE),
            // 16.7 SR 22 d-f: group, or conditional.
            "quantified path primary"
            | "questioned path primary"
            | "path pattern union"
            | "path multiset alternation" => {
                for i in 0..n {
                    if self.decl(&out, i).is_some() {
                        out = out.with(fact(i, DECL_OPAQUE));
                    }
                }
            }
            // 16.3 SR 12: with YIELD, what overlaps and what is yielded.
            "graph pattern binding table" => {
                let yielded = self.names_with(&out, YIELDED);
                if children.len() > 1 && !yielded.is_empty() {
                    for (i, b) in env.iter().enumerate() {
                        if b.is_none() && !yielded.contains(&i) {
                            out = clear_decl(out, i);
                        }
                        out = out.without(fact(i, YIELDED));
                    }
                }
            }
            // 14.4, 16.3 SR 10, 16: new names extend the scope, repeated ones join.
            "simple match statement" => {
                let mut next = env.clone();
                for i in 0..n {
                    let Some(kind) = self.decl(&out, i) else {
                        continue;
                    };
                    let opaque = out.has(fact(i, DECL_OPAQUE));
                    let selective = out.has(fact(i, DECL_SELECTIVE));
                    match env[i] {
                        Some(b) => {
                            let joins = b.kind == kind
                                && matches!(kind, Kind::Node | Kind::Edge)
                                && !opaque
                                && !selective;
                            if !joins {
                                return vec![];
                            }
                        }
                        None => {
                            next[i] = Some(Bound {
                                kind: if opaque { Kind::Group } else { kind },
                                record: false,
                            });
                        }
                    }
                }
                out = (0..n).fold(out, clear_decl);
                out = set_out(out, &next, false);
            }
            "filter statement"
            | "order by and page statement"
            | "set statement"
            | "remove statement"
            | "delete statement" => {
                out = (0..n).fold(out, |o, i| o.without(fact(i, TARGET)));
                out = set_out(out, &env, false);
            }
            "insert statement" => {
                let mut next = env.clone();
                for i in 0..n {
                    if let Some(kind) = self.decl(&out, i) {
                        match env[i] {
                            Some(b) if b.kind == Kind::Node && kind == Kind::Node => {}
                            Some(_) => return vec![],
                            None => {
                                next[i] = Some(Bound {
                                    kind,
                                    record: false,
                                })
                            }
                        }
                    }
                }
                out = (0..n).fold(out, clear_decl);
                out = set_out(out, &next, false);
            }
            // 14.10 SR 4 (reading): no aggregate in a sort key.
            "sort key" => {
                if out.has(AGGREGATES) {
                    return vec![];
                }
            }
            // 20.1 SR 7: aggregates only as a return item's own; a horizontal one would need
            // a group variable, never referenced here.
            "aggregate function" => {
                if !inh.has(COLLECT) || !inh.has(AGGREGABLE) {
                    return vec![];
                }
                out = (0..n)
                    .fold(out, |o, i| o.without(fact(i, USED)))
                    .with(AGGREGATES)
                    .without(DISTINCT);
            }
            // 10.3 SR 7, 14.7, 14.8 SR 11, 15.1 SR 9: new names are new.
            "let statement"
            | "for statement"
            | "named procedure call"
            | "binding variable definition block" => {
                let record = def == "binding variable definition block";
                let mut next = env.clone();
                for i in 0..n {
                    if out.has(fact(i, NEW)) {
                        if env[i].is_some() {
                            return vec![];
                        }
                        next[i] = Some(Bound {
                            kind: Kind::Value,
                            record,
                        });
                        out = out.without(fact(i, NEW));
                    }
                }
                out = set_out(out, &next, false);
            }
            // 20.5 SR 3: new names; none inside a pattern, whose variables it would also have to
            // avoid (reading).
            "let value expression" => {
                if inh.has(IN_PATTERN) {
                    return vec![];
                }
                for (i, b) in env.iter().enumerate() {
                    if out.has(fact(i, NEW)) {
                        if b.is_some() {
                            return vec![];
                        }
                        out = out.without(fact(i, NEW));
                    }
                }
            }
            // 15.1 SR 9-12: the body's result columns are new and join the table.
            "inline procedure call" => {
                let mut next = env.clone();
                if let Some(body) = children.iter().rev().find(|c| c.has(STATEMENT))
                    && body.has(RESULT)
                {
                    let result = self.read(body, OUT, OUT_RECORD);
                    for (i, b) in result.iter().enumerate() {
                        let Some(b) = b.filter(|b| !b.record) else {
                            continue;
                        };
                        if env[i].is_some() {
                            return vec![];
                        }
                        next[i] = Some(Bound {
                            kind: b.kind,
                            record: false,
                        });
                    }
                }
                out = (0..n).fold(out, |o, i| o.without(fact(i, LISTED)));
                out = set_out(out, &next, false);
            }
            // 16.14 SR 7: a yielded name is a column; the alias renames it.
            "yield item" => {
                let spelled: Vec<usize> = (0..n).filter(|&i| has(SPELLED, i)).collect();
                if let (Some(&i), true) = (spelled.first(), inh.has(IN_CALL_YIELD)) {
                    // 16.14 SR 6, 15.1 SR 9: a procedure's yielded name, or its alias, is a
                    // new column.
                    let target = (0..n).find(|&j| out.has(fact(j, NEW))).unwrap_or(i);
                    out = out.without(fact(i, SPELLED)).with(fact(target, NEW));
                } else if let Some(&i) = spelled.first() {
                    let Some(b) = env[i].filter(|b| !b.record) else {
                        return vec![];
                    };
                    let target = (0..n).find(|&j| out.has(fact(j, NEW))).unwrap_or(i);
                    // 9.2 SR 12 c: the new table shares no name with the record.
                    if env[target].is_some_and(|b| b.record) {
                        return vec![];
                    }
                    out = out
                        .without(fact(target, NEW))
                        .without(fact(i, SPELLED))
                        .with(fact(target, YIELDED))
                        .with(fact(target, YIELD_KIND + b.kind.code()));
                }
            }
            "next statement" => {
                out = (0..n).fold(out, |o, i| {
                    KINDS.iter().fold(o.without(fact(i, YIELDED)), |o, k| {
                        o.without(fact(i, YIELD_KIND + k.code()))
                    })
                });
            }
            // 9.2 SR 12 b: a statement without a result leaves a unit table.
            "statement" => {
                if !out.has(RESULT) {
                    out = set_out(out, &record_part(&env), false);
                }
                out = out.without(FINISHED);
            }
            "composite query statement" => out = out.without(FINISHED),
            // 14.2 SR 5, 10: no branch finishes, every branch returns the same columns.
            "composite query expression" if children.len() == 3 => {
                if children[0].has(FINISHED) || children[2].has(FINISHED) {
                    return vec![];
                }
                let a = self.read(&children[0], OUT, OUT_RECORD);
                let b = self.read(&children[2], OUT, OUT_RECORD);
                let table =
                    |e: &Env| -> Env { e.iter().map(|b| b.filter(|b| !b.record)).collect() };
                if table(&a) != table(&b) {
                    return vec![];
                }
                out = copy_out(clear_out(out, n), &children[0], n).without(FINISHED);
            }
            "primitive result statement" => {
                if node.items == [Item::Token("FINISH")] {
                    out = set_out(out, &record_part(&env), true).with(FINISHED);
                } else {
                    out = copy_out(clear_out(out, n), &children[0], n)
                        .with(RESULT)
                        .without(PLAIN);
                }
            }
            "set quantifier" => out.set(DISTINCT, node.items == [Item::Token("DISTINCT")]),
            "group by clause" => out = out.with(GROUPED),
            "return item alias" => {
                for i in 0..n {
                    if has(SPELLED, i) {
                        out = out.with(fact(i, ALIASED));
                    }
                }
            }
            // 14.11 SR 8: a column is its alias, or a bare variable's name.
            "return item" => {
                let bare = (0..n).find(|&i| has(BARE, i));
                let alias = (0..n).find(|&i| has(ALIASED, i));
                let kind = bare.and_then(kind_of).unwrap_or(Kind::Value);
                let Some(name) = alias.or(bare) else {
                    return vec![];
                };
                // 14.11 SR 10 (Cor 1): with GROUP BY, an item is a grouping item or aggregates.
                let loose = bare.is_none() && !out.has(AGGREGATES);
                for i in 0..n {
                    out = out.without(fact(i, BARE)).without(fact(i, ALIASED));
                }
                out = out.with(fact(name, COLUMN + kind.code()));
                out.set(LOOSE, loose);
            }
            // 14.11 SR 6, 10-13: the columns become the table, the record stays.
            "return statement body" => {
                let mut next = record_part(&env);
                if node.items.first() != Some(&Item::Token("NO")) {
                    let used = self.names_with(&out, USED);
                    if out.has(GROUPED) {
                        if out.has(LOOSE) || used.iter().any(|&i| !out.has(fact(i, KEY))) {
                            return vec![];
                        }
                    } else if out.has(AGGREGATES) && !used.is_empty() {
                        return vec![];
                    }
                    if out.has(STAR) {
                        let table: Env = env.iter().map(|b| b.filter(|b| !b.record)).collect();
                        if table.iter().all(Option::is_none) || out.has(GROUPED) {
                            return vec![];
                        }
                        amend(&mut next, &table);
                    }
                    for (i, slot) in next.iter_mut().enumerate() {
                        if let Some(k) = column(&out, i) {
                            // 9.2 SR 12 c (reading: always): no column named like a field of
                            // the record.
                            if slot.is_some_and(|b| b.record) {
                                return vec![];
                            }
                            *slot = Some(Bound {
                                kind: k,
                                record: false,
                            });
                        }
                    }
                }
                let plain = !out.has(DISTINCT) && !out.has(AGGREGATES) && !out.has(GROUPED);
                for i in 0..n {
                    out = out.without(fact(i, USED)).without(fact(i, KEY));
                    for k in KINDS {
                        out = out.without(fact(i, COLUMN + k.code()));
                    }
                }
                for g in [STAR, DISTINCT, GROUPED, AGGREGATES, LOOSE] {
                    out = out.without(g);
                }
                out = set_out(out, &next, false);
                out.set(PLAIN, plain);
            }
            // What a nested data-modifying procedure leaves behind (reading): nothing new,
            // and nothing that was bound referenced again.
            "nested data-modifying procedure specification"
            | "focused nested data-modifying procedure specification" => {
                let blocked: Env = env
                    .iter()
                    .map(|b| b.map(|b| Bound { record: true, ..b }))
                    .collect();
                out = set_out(out, &blocked, false);
            }
            // 14.10 SR 4: a sort key holds no nested query.
            "nested binding table query specification"
                if inh.has(IN_SORT_KEY) || inh.has(IN_PATTERN) =>
            {
                return vec![];
            }
            "exists predicate" | "value query expression" => {
                if inh.has(IN_SORT_KEY) || inh.has(IN_PATTERN) {
                    return vec![];
                }
                // No correlation (reading): what `EXISTS { pattern }` declares is new.
                if (0..n).any(|i| self.decl(&out, i).is_some() && env[i].is_some()) {
                    return vec![];
                }
                out = clear_out(out, n);
                for i in 0..n {
                    out = clear_decl(out, i)
                        .without(fact(i, USED))
                        .without(fact(i, NEW));
                }
                out = out.without(AGGREGATES);
            }
            // 14.12 SR 7, 8: without FROM, no `*`; every item named (reading: always).
            "select statement" => {
                if out.has(STAR) && !out.has(SELECT_FROM) {
                    return vec![];
                }
                out = (0..n).fold(out, clear_decl);
                for i in 0..n {
                    for k in KINDS {
                        out = out.without(fact(i, COLUMN + k.code()));
                    }
                }
                out = out.without(SELECT_FROM);
                out = set_out(out, &record_part(&env), true);
            }
            "select statement body" => out = out.with(SELECT_FROM),
            "select item alias" => {
                for i in (0..n).filter(|&i| has(SPELLED, i)) {
                    out = out.with(fact(i, COLUMN + Kind::Value.code()));
                }
                out = out.with(SELECT_ALIAS);
            }
            "select item" => {
                if !out.has(SELECT_ALIAS) {
                    return vec![];
                }
                out = out.without(SELECT_ALIAS);
            }
            _ => {}
        }
        // What only flows inside a statement stops at it. An aggregate outside a RETURN
        // needs a group variable to aggregate (20.1 SR 7), and none is referenced here.
        if Self::statement(def) && !RETURN_FAMILY.contains(&owner(def)) {
            if out.has(AGGREGATES) {
                return vec![];
            }
            out = (0..n).fold(out, |o, i| o.without(fact(i, USED)).without(fact(i, KEY)));
            for g in [DISTINCT, GROUPED, STAR, SELECTIVE] {
                out = out.without(g);
            }
        }
        // `*` for the RETURN or SELECT right above.
        if node.group
            && matches!(owner(def), "return statement body" | "select statement")
            && node.items == [Item::Def("asterisk")]
        {
            out = out.with(STAR);
        }
        if inh.has(DISCARD) {
            out = clear_out(out, n);
        }
        vec![out]
    }

    fn text(&self, def: &str, syn: &State) -> Option<String> {
        let code = match def {
            "binding variable" => CHOSEN,
            "identifier" => SPELLED,
            _ => return None,
        };
        (0..self.n())
            .find(|&i| syn.has(fact(i, code)))
            .map(|i| self.names[i].clone())
    }
}

/// Marks any column fact in `count`'s duplicate check.
const COLUMN_ANY: Fact = Fact::MAX;

fn column(s: &State, i: usize) -> Option<Kind> {
    KINDS
        .into_iter()
        .find(|k| s.has(fact(i, COLUMN + k.code())))
}

fn clear_out(mut s: State, n: usize) -> State {
    for i in 0..n {
        for c in OUT..=OUT_RECORD {
            s = s.without(fact(i, c));
        }
    }
    s.without(STATEMENT)
        .without(RESULT)
        .without(PLAIN)
        .without(FINISHED)
}

fn copy_out(s: State, from: &State, n: usize) -> State {
    let mut s = clear_out(s, n);
    for i in 0..n {
        for c in OUT..=OUT_RECORD {
            if from.has(fact(i, c)) {
                s = s.with(fact(i, c));
            }
        }
    }
    for g in [STATEMENT, RESULT, PLAIN, FINISHED] {
        if from.has(g) {
            s = s.with(g);
        }
    }
    s
}

fn clear_decl(mut s: State, i: usize) -> State {
    for c in DECL..=DECL_SELECTIVE {
        s = s.without(fact(i, c));
    }
    s
}

impl Scope {
    fn element_to_decl(&self, mut out: State, kind: Kind) -> State {
        for i in 0..self.n() {
            if out.has(fact(i, ELEMENT)) {
                out = out
                    .without(fact(i, ELEMENT))
                    .with(fact(i, DECL + kind.code()));
            }
        }
        out
    }
}
