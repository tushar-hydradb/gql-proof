//! Scoping of binding variables (ISO/IEC 39075 2024 + Cor 1) as a [`Context`]: every query
//! refers only to variables in scope, declares only names it may, and returns columns it may.
//!
//! A label says, per variable of the subtree (a slot), what the subtree does with it: needs
//! it bound before (a reference, a join), binds it for what follows (`out`), declares it in a
//! pattern (`decl`, a statement decides whether that is new or a join), or returns it as a
//! column; and a few flags, per variable and for the whole subtree. Nothing is inherited:
//! where the old automaton passed an environment down, a statement sequence here meets each
//! statement's needs with what the statements before it bind (14.3 SR 3-5), and a context
//! that forbids something below it (a sort key, a graph pattern, a quantifier) rejects a
//! child whose label says it holds it.
//!
//! Sound, not complete, like the automaton it replaces; `verify::scope` (written separately,
//! from the standard alone) checks every tree. Readings that forbid more than ISO:
//! - nothing bound outside a CALL body, a subquery, a graph pattern or a SELECT is referenced
//!   inside it (no correlation, 19.4, 20.6, 15.2, 16.3 SR 25 allow some), and nothing
//!   nested in a graph pattern declares names (no subquery, no `LET ... IN`)
//! - a pattern variable joins an incoming one or another occurrence only as a singleton node
//!   or edge (16.3 SR 10, 16, 16.4 SR 3); path variables and the variables of a selective
//!   path pattern (16.6 SR 7) never join
//! - no element variable is declared under a union, multiset alternation, `?` or quantifier
//!   (16.7 SR 22 d-f); one subpath variable per pattern
//! - an element WHERE or property specification sees its own variable; a parenthesized WHERE
//!   sees the singletons its own expression declares (16.7 SR 21, 24, 4.11.5)
//! - aggregates appear only as a return item's own (20.1 SR 7); a sort key holds none and no
//!   nested query; with GROUP BY every item groups or aggregates (14.11 SR 10); ORDER BY after
//!   an aggregating, grouping or DISTINCT RETURN sees only its columns (14.10 SR 4)
//! - `RETURN *` follows a statement of the same sequence that binds something
//! - after NEXT, only what the statement before returns is referenced (9.2 SR 12 also passes
//!   the working record, which outside bodies holds nothing referenceable here)
//! - one SET or REMOVE item per variable (13.3 SR 4-5); every select item is named
//! - an INSERT reuses a bound variable only for a node with nothing else in its filler, and
//!   declares each name once (16.5 SR 10-11)
//! - a nested `{ ... }` data-modifying procedure leaves nothing referenceable behind, and
//!   neither do binding variable definitions (they bind the record)
//! - at most [`SLOTS`] variables in one subtree's label: a longer list of distinct names is
//!   not generated (coverage counts occurrences, and fewer names reach the same ones)

use super::{Context, FactSpec, Link, Masks, Projection, Slot};
use crate::refine::{Item, Node};

/// The most variables one label holds, and one that only references them (an expression).
/// Some bound keeps the labels finite: an expression may reference ever more variables.
#[derive(Clone, Copy, Debug)]
pub struct Caps {
    pub slots: usize,
    pub references: usize,
}

impl Default for Caps {
    fn default() -> Self {
        Caps {
            slots: 3,
            references: 3,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum Kind {
    Node,
    Edge,
    Path,
    Value,
    /// Declared under a quantifier or union: never referenced here.
    Group,
    /// Needed only: any variable a reference may name (20.12 SR 8), a node or an edge, or
    /// what a DELETE item may name (13.5 SR 5: a node, an edge or a value, never a path).
    /// The kind is chosen only where it matters (a column, an element reference).
    Any,
    Element,
    Deletable,
}

/// What a reference may name (20.12 SR 8).
const REFERENCEABLE: [Kind; 4] = [Kind::Node, Kind::Edge, Kind::Path, Kind::Value];

/// Whether a variable of kind `have` meets a need for `need`.
fn fits(need: Kind, have: Kind) -> bool {
    need == have
        || need == Kind::Any && REFERENCEABLE.contains(&have)
        || need == Kind::Element && matches!(have, Kind::Node | Kind::Edge)
        || need == Kind::Deletable && matches!(have, Kind::Node | Kind::Edge | Kind::Value)
}

/// One need for two needs of one variable.
fn narrow(a: Kind, b: Kind) -> Option<Kind> {
    if fits(a, b) {
        Some(b)
    } else if fits(b, a) {
        Some(a)
    } else {
        // Two needs chosen later: the one every variable meeting both meets.
        match (a, b) {
            (Kind::Any, Kind::Element | Kind::Deletable)
            | (Kind::Element | Kind::Deletable, Kind::Any) => Some(if a == Kind::Any {
                b
            } else {
                a
            }),
            (Kind::Element, Kind::Deletable) | (Kind::Deletable, Kind::Element) => {
                Some(Kind::Element)
            }
            _ => None,
        }
    }
}

/// Flags of one variable.
mod vf {
    /// Referenced outside any aggregate (for a RETURN's grouping).
    pub const USED: u16 = 1;
    /// The subtree is nothing but a reference to it.
    pub const BARE: u16 = 1 << 1;
    /// A GROUP BY key.
    pub const KEY: u16 = 1 << 2;
    /// A return item's alias.
    pub const ALIASED: u16 = 1 << 3;
    /// An element variable, before its pattern says node or edge.
    pub const ELEMENT: u16 = 1 << 4;
    /// A path variable, before its path pattern declares it.
    pub const PATH_VAR: u16 = 1 << 5;
    /// Declared by a selective path pattern: joined nowhere (16.6 SR 7).
    pub const SELECTIVE: u16 = 1 << 6;
    /// Declared, but not in a YIELD that lists others (16.3 SR 12): bound by nothing after.
    pub const HIDDEN: u16 = 1 << 7;
    /// Inserted with more than its name in its filler: never an existing node.
    pub const INSERT_FULL: u16 = 1 << 8;
    /// Named by a CALL's scope clause.
    pub const LISTED: u16 = 1 << 9;
    /// Named by a pattern's YIELD.
    pub const YIELDED: u16 = 1 << 10;
    /// Changed by a SET or REMOVE item.
    pub const TARGET: u16 = 1 << 11;
    /// Defined as a new name by LET, FOR or a procedure's YIELD.
    pub const NEW: u16 = 1 << 12;
    /// A name spelled here, its role not given yet.
    pub const CHOSEN: u16 = 1 << 13;
    /// A record field's name.
    pub const FIELD: u16 = 1 << 14;
    /// What may meet another occurrence of the same name and become one variable.
    pub const IDENTITY: u16 = ALIASED | LISTED | YIELDED | TARGET | NEW | CHOSEN | FIELD;
}

/// Flags of the whole subtree.
mod gf {
    /// A statement: its variables' `out` is what follows it sees.
    pub const STATEMENT: u32 = 1;
    /// The statement does not pass on the table it gets (a RETURN replaces it).
    pub const CLOSES: u32 = 1 << 1;
    pub const RESULT: u32 = 1 << 2;
    pub const FINISHED: u32 = 1 << 3;
    /// A RETURN without DISTINCT, aggregates or GROUP BY (14.10 SR 4).
    pub const PLAIN: u32 = 1 << 4;
    /// `RETURN *`, still to meet the table it returns.
    pub const STAR: u32 = 1 << 5;
    pub const NEEDS_TABLE: u32 = 1 << 6;
    /// An aggregate a return item owns (20.1 SR 7).
    pub const AGGREGATES: u32 = 1 << 7;
    /// An aggregate below no value expression yet, and below one.
    pub const AGG_LOOSE: u32 = 1 << 8;
    pub const AGG_IN_VE: u32 = 1 << 9;
    pub const DISTINCT: u32 = 1 << 10;
    pub const GROUPED: u32 = 1 << 11;
    /// A selective path search prefix, for the path pattern above.
    pub const SELECTIVE: u32 = 1 << 12;
    pub const SUBPATH: u32 = 1 << 13;
    pub const ELEMENT_WHERE: u32 = 1 << 14;
    pub const SELECT_FROM: u32 = 1 << 15;
    pub const SELECT_ALIAS: u32 = 1 << 16;
    /// A return item that neither is a bare reference nor aggregates.
    pub const LOOSE: u32 = 1 << 17;
    /// The subtree derives at least one token.
    pub const TOKENS: u32 = 1 << 18;
    /// A nested query somewhere below (in an expression), for a sort key.
    pub const QUERY: u32 = 1 << 19;
    /// A NEXT statement: its needs are met by the statement before only.
    pub const NEXT: u32 = 1 << 21;
    /// A yield item read as a procedure's result, not a column of the statement before.
    pub const CALL_YIELD: u32 = 1 << 22;
    /// A graph pattern's YIELD is present, for the binding table above.
    pub const PATTERN_YIELD: u32 = 1 << 23;
}

/// What a subtree does with one variable.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash, Default)]
pub struct Var {
    /// Bound before the subtree, as this kind.
    need: Option<Kind>,
    /// Bound after it, as this kind.
    out: Option<Kind>,
    /// Declared by a pattern, as this kind.
    decl: Option<Kind>,
    /// A column of a RETURN or SELECT, or a yielded one.
    column: Option<Kind>,
    flags: u16,
}

impl Var {
    fn has(&self, f: u16) -> bool {
        self.flags & f != 0
    }

    fn with(mut self, f: u16) -> Var {
        self.flags |= f;
        self
    }

    fn without(mut self, f: u16) -> Var {
        self.flags &= !f;
        self
    }

    /// Only referenced: a need and nothing else that names it.
    fn reference(&self) -> bool {
        self.need.is_some()
            && self.out.is_none()
            && self.decl.is_none()
            && self.column.is_none()
            && !self.has(vf::IDENTITY | vf::ELEMENT | vf::PATH_VAR)
    }

    /// A reference still to meet what it names, whatever its use flags say.
    fn pending(&self) -> bool {
        self.need.is_some()
            && self.out.is_none()
            && self.decl.is_none()
            && self.column.is_none()
            && !self
                .has(vf::CHOSEN | vf::ELEMENT | vf::PATH_VAR | vf::NEW | vf::FIELD | vf::ALIASED)
    }

    /// Nothing left to say about it: the variable is local to what was scanned.
    fn idle(&self) -> bool {
        self.need.is_none()
            && self.out.is_none()
            && self.decl.is_none()
            && self.column.is_none()
            && !self.has(vf::IDENTITY | vf::ELEMENT | vf::PATH_VAR)
    }

    /// A declaration another may join.
    fn joinable(&self) -> bool {
        matches!(self.decl, Some(Kind::Node | Kind::Edge))
            && !self.has(vf::SELECTIVE | vf::INSERT_FULL)
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash, Default)]
pub struct Label {
    vars: Vec<Var>,
    flags: u32,
}

impl Label {
    fn has(&self, f: u32) -> bool {
        self.flags & f != 0
    }

    /// How many variables it holds.
    pub fn width(&self) -> usize {
        self.vars.len()
    }

    /// What a rule running under scope (`context::pair`) reads of slot `s`.
    pub fn view(&self, s: usize) -> View {
        let v = &self.vars[s];
        View {
            need: v.need,
            out: v.out,
            decl: v.decl,
            column: v.column,
            new: v.has(vf::NEW),
            aliased: v.has(vf::ALIASED),
        }
    }
}

/// One variable of a label, read only: what it needs, binds, declares or returns as, and
/// whether it is a new name (LET, FOR, a procedure's YIELD) or a return item's alias.
#[derive(Clone, Copy, Debug)]
pub struct View {
    pub need: Option<Kind>,
    pub out: Option<Kind>,
    pub decl: Option<Kind>,
    pub column: Option<Kind>,
    pub new: bool,
    pub aliased: bool,
}

/// A label being built: its variables (`None` once closed), flags, and where each input slot
/// went.
#[derive(Clone)]
struct Draft {
    vars: Vec<Option<Var>>,
    flags: u32,
    map: Vec<Option<usize>>,
}

impl Draft {
    /// `l` as it is.
    fn of(l: &Label) -> Draft {
        Draft {
            vars: l.vars.iter().copied().map(Some).collect(),
            flags: l.flags,
            map: (0..l.vars.len()).map(Some).collect(),
        }
    }

    fn has(&self, f: u32) -> bool {
        self.flags & f != 0
    }

    fn set(&mut self, f: u32, on: bool) {
        if on {
            self.flags |= f;
        } else {
            self.flags &= !f;
        }
    }

    fn live(&self) -> impl Iterator<Item = (usize, &Var)> {
        self.vars
            .iter()
            .enumerate()
            .filter_map(|(i, v)| v.as_ref().map(|v| (i, v)))
    }

    fn any(&self, f: impl Fn(&Var) -> bool) -> bool {
        self.live().any(|(_, v)| f(v))
    }

    fn update(&mut self, mut f: impl FnMut(Var) -> Var) {
        for v in self.vars.iter_mut().flatten() {
            *v = f(*v);
        }
    }

    /// Closes the variables `f` says: they are local to what was scanned.
    fn close(&mut self, f: impl Fn(&Var) -> bool) {
        for v in &mut self.vars {
            if v.as_ref().is_some_and(&f) {
                *v = None;
            }
        }
    }

    /// Merges variable `from` into `into`: one variable from now on.
    fn merge(&mut self, from: usize, into: usize, v: Var) {
        self.vars[into] = Some(v);
        self.vars[from] = None;
        for m in self.map.iter_mut().flatten() {
            if *m == from {
                *m = into;
            }
        }
    }

    /// The label, its variables in canonical order, and the link from the inputs; `None` if
    /// it holds too many variables. Idle variables close.
    fn done(mut self, caps: Caps) -> Option<(Label, Link)> {
        let _span = tracing::trace_span!("done").entered();
        self.close(Var::idle);
        let mut live: Vec<(Var, usize)> = self.live().map(|(i, v)| (*v, i)).collect();
        let references = live.iter().all(|(v, _)| v.pending());
        if live.len()
            > if references {
                caps.references
            } else {
                caps.slots
            }
        {
            return None;
        }
        live.sort();
        let mut slot = vec![None; self.vars.len()];
        for (s, (_, i)) in live.iter().enumerate() {
            slot[*i] = Some(s as Slot);
        }
        // A closed variable keeps one local slot past the label's, so inputs that became one
        // variable before it closed stay one (for names in `accepts`, for naming trees).
        let mut local = live.len() as Slot;
        for m in self.map.iter().flatten() {
            if slot[*m].is_none() {
                slot[*m] = Some(local);
                local += 1;
            }
        }
        let link = Link(self.map.iter().map(|m| m.and_then(|i| slot[i])).collect());
        Some((
            Label {
                vars: live.into_iter().map(|(v, _)| v).collect(),
                flags: self.flags,
            },
            link,
        ))
    }
}

/// Where a child's variable goes when it meets the variables before it.
#[derive(Clone, Copy)]
enum Target {
    /// One of the variables before it, which then becomes this.
    Into(usize, Var),
    /// A new variable.
    New,
}

/// Every way `child`'s variables meet `draft`'s, each child variable taking one of its
/// targets and no two the same one. The child's slots are the inputs after `draft`'s.
fn meet(draft: &Draft, child: &Label, targets: impl Fn(&Var) -> Vec<Target>) -> Vec<Draft> {
    let _span = tracing::trace_span!("meet").entered();
    let mut out = vec![draft.clone()];
    for cv in &child.vars {
        let mut next = Vec::new();
        for d in &out {
            for t in targets(cv) {
                let mut d = d.clone();
                match t {
                    Target::Into(i, v) => {
                        // Each variable before meets one of the child's at most.
                        if d.vars[i].is_none() || d.map[draft.map.len()..].contains(&Some(i)) {
                            continue;
                        }
                        d.vars[i] = Some(v);
                        d.map.push(Some(i));
                    }
                    Target::New => {
                        d.vars.push(Some(*cv));
                        d.map.push(Some(d.vars.len() - 1));
                    }
                }
                next.push(d);
            }
        }
        out = next;
    }
    out
}

/// Two references to one variable, as one.
fn joined(a: &Var, b: &Var) -> Option<Var> {
    let one = |x: Option<Kind>, y: Option<Kind>| match (x, y) {
        (Some(_), Some(_)) => None,
        (x, y) => Some(x.or(y)),
    };
    if a.out.is_some() || b.out.is_some() || a.decl.is_some() || b.decl.is_some() {
        return None;
    }
    if (a.flags | b.flags) & vf::IDENTITY != 0 {
        return None;
    }
    let need = narrow(a.need?, b.need?)?;
    // A column's kind is chosen: the other reference must fit it.
    if a.column.is_some_and(|c| !fits(need, c)) || b.column.is_some_and(|c| !fits(need, c)) {
        return None;
    }
    Some(Var {
        need: Some(need),
        out: None,
        decl: None,
        column: one(a.column, b.column)?,
        flags: a.flags | b.flags,
    })
}

/// Two pattern declarations of one variable, a join (16.4 SR 3, 16.7 SR 22 c).
fn joined_decl(a: &Var, b: &Var) -> Option<Var> {
    (a.joinable() && b.joinable() && a.decl == b.decl && a.need.is_none() && b.need.is_none())
        .then_some(Var {
            flags: a.flags | b.flags,
            ..*a
        })
}

/// Statements and the clauses around their variables, from the automaton this replaces.
/// Aggregates do not cross them, and they are where what only flows inside a statement
/// stops.
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
    "filter statement",
    "order by and page statement",
    "primitive result statement",
    "return statement",
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
    "set statement",
    "remove statement",
    "delete statement",
    "binding variable definition block",
    "binding variable definition",
    "graph variable definition",
    "binding table variable definition",
    "linear catalog-modifying statement",
];

/// Bodies in braces: a scope of their own, which sees nothing bound outside (reading).
const NESTED: &[&str] = &[
    "nested procedure specification",
    "nested query specification",
    "nested data-modifying procedure specification",
    "focused nested data-modifying procedure specification",
    "focused nested query specification",
];

/// Where a name an `<identifier>` or `<binding variable>` spells gets its role, or passes
/// through on its way there.
const NAMING: &[&str] = &[
    "binding variable reference",
    "element variable",
    "path variable",
    "let variable definition",
    "value variable definition",
    "for item alias",
    "for ordinality or offset",
    "yield item alias",
    "graph variable definition",
    "binding table variable definition",
    "return item alias",
    "select item alias",
    "field name",
    "yield item name",
];

/// Where nothing a reference names can be in scope (reading for SELECT; nothing binds before
/// a catalog or session command): a reference there is rejected as soon as it is seen, not
/// carried up to the statement that would reject it.
const NO_SCOPE: &[&str] = &[
    "select statement",
    "select statement body",
    "select graph match list",
    "select graph match",
    "select query specification",
    "session set command",
    "create schema statement",
    "drop schema statement",
    "create graph statement",
    "drop graph statement",
    "create graph type statement",
    "drop graph type statement",
    "graph source",
    "graph type like graph",
];

fn owner(def: &str) -> &str {
    def.split('/').next().unwrap_or(def)
}

#[derive(Default)]
pub struct Scope {
    pub caps: Caps,
}

impl Scope {
    fn statement(def: &str) -> bool {
        STATEMENTS.contains(&owner(def))
    }

    /// The default meeting of a child with what came before it: statements chain, the rest
    /// is a union where references to one variable may be one, and declarations join.
    fn combine(&self, node: &Node, partial: &Label, child: &Label) -> Vec<(Label, Link)> {
        let _span = tracing::trace_span!("combine").entered();
        let d = Draft::of(partial);
        let chain = partial.has(gf::STATEMENT) && child.has(gf::STATEMENT);
        let passes = !chain || !partial.has(gf::CLOSES);
        // 9.2 SR 12: after NEXT, only the statement before is seen.
        let next = chain && child.has(gf::NEXT);
        let drafts = meet(&d, child, |cv| {
            let mut t = Vec::new();
            for (i, pv) in d.live() {
                if let Some(k) = cv.need {
                    // Met by what a statement before binds (14.3 SR 3-5).
                    let bound = pv.out.is_some_and(|o| fits(k, o));
                    if chain && bound && cv.reference() {
                        let out = if child.has(gf::CLOSES) { None } else { pv.out };
                        t.push(Target::Into(i, Var { out, ..*pv }));
                    }
                    if chain
                        && bound
                        && cv.out.is_some()
                        && !cv.has(vf::IDENTITY)
                        && pv.out == cv.out
                    {
                        // A RETURN's bare column, a join: the same variable, rebound.
                        let out = if child.has(gf::CLOSES) {
                            cv.out
                        } else {
                            pv.out
                        };
                        t.push(Target::Into(
                            i,
                            Var {
                                out,
                                flags: pv.flags | cv.flags,
                                ..*pv
                            },
                        ));
                    }
                }
                // 15.2 SR 6 a ii: names in a scope clause are distinct variables.
                let listing = owner(node.def) == "binding variable reference list";
                if passes
                    && !next
                    && !listing
                    && pv.out.is_none()
                    && let Some(v) = joined(pv, cv)
                {
                    t.push(Target::Into(i, v));
                }
                if !chain && let Some(v) = joined_decl(pv, cv) {
                    // An insert pattern declares each name once (16.5 SR 10-11).
                    if !owner(node.def).starts_with("insert") {
                        t.push(Target::Into(i, v));
                    }
                }
            }
            if cv.need.is_none() || (passes && !next) {
                t.push(Target::New);
            }
            t
        });
        let mut out = Vec::new();
        for mut d in drafts {
            if chain {
                if child.has(gf::NEEDS_TABLE) {
                    // `RETURN *` returns the table the statements before bind.
                    if !d.any(|v| v.out.is_some()) {
                        continue;
                    }
                    d.flags &= !gf::NEEDS_TABLE;
                }
                if child.has(gf::CLOSES) {
                    // What the statements before bound is no longer in scope.
                    let before: Vec<usize> = (0..partial.vars.len()).collect();
                    for i in before {
                        if !d.map[partial.vars.len()..].contains(&Some(i))
                            && let Some(v) = &mut d.vars[i]
                        {
                            v.out = None;
                        }
                    }
                }
                // The output is the last statement's.
                let keep = gf::RESULT | gf::FINISHED | gf::PLAIN | gf::CLOSES;
                d.flags = (d.flags & !keep) | (child.flags & keep);
                if partial.has(gf::CLOSES) {
                    d.flags |= gf::CLOSES;
                }
                d.flags |= child.flags & !keep & !gf::NEXT;
            } else {
                // 16.4 SR 4 (reading): subpath variables are spelled alike, one per pattern.
                if partial.has(gf::SUBPATH) && child.has(gf::SUBPATH) {
                    continue;
                }
                // A procedure's results and columns before do not mix in one YIELD.
                if !partial.vars.is_empty()
                    && partial.has(gf::CALL_YIELD) != child.has(gf::CALL_YIELD)
                {
                    continue;
                }
                // Two children that derive something: no reference is bare.
                if partial.has(gf::TOKENS) && child.has(gf::TOKENS) {
                    d.update(|v| v.without(vf::BARE));
                }
                d.flags |= child.flags;
            }
            out.extend(d.done(self.caps));
        }
        out
    }

    /// Meets every reference in `d` that `wants` takes with a variable `into` accepts, as the
    /// same variable, which `merge` makes of the two; references left over stay, or reject
    /// if `all`.
    fn discharge(
        d: Draft,
        wants: impl Fn(&Var) -> bool,
        into: impl Fn(&Var, Kind) -> bool,
        merge: impl Fn(&Var, &Var) -> Var,
        all: bool,
    ) -> Vec<Draft> {
        let _span = tracing::trace_span!("discharge").entered();
        let refs: Vec<usize> = d
            .live()
            .filter(|(_, v)| v.pending() && wants(v))
            .map(|(i, _)| i)
            .collect();
        let mut out = vec![d];
        for r in refs {
            let mut next = Vec::new();
            for d in out {
                let Some(rv) = d.vars[r] else { continue };
                let k = rv.need.unwrap();
                for (i, v) in d.live() {
                    if i != r && !v.pending() && into(v, k) {
                        let mut e = d.clone();
                        e.merge(r, i, merge(v, &rv));
                        next.push(e);
                    }
                }
                if !all {
                    next.push(d);
                }
            }
            out = next;
        }
        out
    }

    /// The variable `into` becomes when a reference meets it: it keeps what it is, and what
    /// the reference said about its use.
    fn absorb(into: &Var, r: &Var) -> Var {
        Var {
            flags: into.flags | (r.flags & (vf::YIELDED | vf::KEY | vf::USED)),
            ..*into
        }
    }

    fn finish_def(&self, node: &Node, partial: &Label) -> Vec<Draft> {
        let def = node.def;
        let mut d = Draft::of(partial);
        // `*` for the RETURN or SELECT right above.
        if node.group
            && matches!(owner(def), "return statement body" | "select statement")
            && node.items == [Item::Def("asterisk")]
        {
            d.set(gf::STAR, true);
        }
        match def {
            "binding variable" => {
                let d = Draft {
                    vars: vec![Some(Var::default().with(vf::CHOSEN))],
                    flags: gf::TOKENS,
                    map: vec![None; partial.vars.len()],
                };
                return vec![d];
            }
            // A plain name (a label, a property), or a name spelled from the pool (an alias).
            "identifier" if partial.vars.is_empty() => {
                let spelled = Draft {
                    vars: vec![Some(Var::default().with(vf::CHOSEN))],
                    flags: d.flags,
                    map: Vec::new(),
                };
                return vec![d, spelled];
            }
            // 20.12 SR 8: a reference names a variable in scope, of some kind.
            "binding variable reference" => {
                d.update(|v| Var {
                    need: Some(Kind::Any),
                    flags: (v.flags & !vf::CHOSEN) | vf::USED | vf::BARE,
                    ..v
                });
            }
            // 16.10 SR 3, 16.9 SR 2: of the kind the reference needs.
            "element variable reference" | "path variable reference" => {
                let want = if def == "path variable reference" {
                    Kind::Path
                } else {
                    Kind::Element
                };
                let mut ok = true;
                d.update(|v| match v.need.filter(|_| v.pending()) {
                    Some(n) => match narrow(n, want) {
                        Some(k) => Var { need: Some(k), ..v },
                        None => {
                            ok = false;
                            v
                        }
                    },
                    None => v,
                });
                if !ok {
                    return vec![];
                }
            }
            // 14.11 SR 10: a grouping element is a key.
            "grouping element" => d.update(|v| v.with(vf::KEY).without(vf::USED)),
            "graph pattern yield item" => d.update(|v| v.with(vf::YIELDED).without(vf::USED)),
            // 15.2 SR 6 a ii: a scope clause lists each name once.
            "binding variable reference list" => d.update(|v| v.with(vf::LISTED)),
            "element variable" => d.update(|v| v.with(vf::ELEMENT).without(vf::CHOSEN)),
            "path variable" => d.update(|v| v.with(vf::PATH_VAR).without(vf::CHOSEN)),
            // 10.3 SR 7, 14.8 SR 11: a new name.
            "let variable definition"
            | "value variable definition"
            | "graph variable definition"
            | "binding table variable definition"
            | "for item alias"
            | "for ordinality or offset"
            | "yield item alias" => {
                d.update(|v| {
                    if v.has(vf::CHOSEN) {
                        v.with(vf::NEW).without(vf::CHOSEN)
                    } else {
                        v
                    }
                });
            }
            // An alias or a field name is a name of its own, spelled here, never a stub.
            "return item alias" | "select item alias" | "field" | "field type"
                if !d.any(|v| v.has(vf::CHOSEN)) =>
            {
                return vec![];
            }
            "return item alias" => d.update(|v| v.with(vf::ALIASED).without(vf::CHOSEN)),
            // 20.19 SR 2: a record names each field once.
            "field" | "field type" => {
                d.update(|v| {
                    if v.has(vf::CHOSEN) {
                        v.with(vf::FIELD).without(vf::CHOSEN)
                    } else {
                        v
                    }
                });
            }
            "fields specification" | "field types specification" => d.close(|v| v.has(vf::FIELD)),
            "node pattern" | "insert node pattern" => {
                if d.any(|v| v.has(vf::ELEMENT) && v.decl.is_some_and(|k| k != Kind::Node)) {
                    return vec![];
                }
                d.update(|v| {
                    if v.has(vf::ELEMENT) {
                        Var {
                            decl: Some(Kind::Node),
                            ..v.without(vf::ELEMENT)
                        }
                    } else {
                        v
                    }
                });
            }
            "edge pattern"
            | "insert edge pointing left"
            | "insert edge pointing right"
            | "insert edge undirected" => {
                if d.any(|v| v.has(vf::ELEMENT) && v.decl.is_some_and(|k| k != Kind::Edge)) {
                    return vec![];
                }
                d.update(|v| {
                    if v.has(vf::ELEMENT) {
                        Var {
                            decl: Some(Kind::Edge),
                            ..v.without(vf::ELEMENT)
                        }
                    } else {
                        v
                    }
                });
            }
            // A bound variable in INSERT is an existing node, inserted as is (reading).
            "insert element pattern filler" if node.items.len() > 1 => d.update(|v| {
                if v.has(vf::ELEMENT) {
                    v.with(vf::INSERT_FULL)
                } else {
                    v
                }
            }),
            "element pattern where clause" => d.set(gf::ELEMENT_WHERE, true),
            // 16.7 SR 21: an element WHERE or property specification sees its own variable,
            // which it needs.
            "element pattern filler" => {
                if d.has(gf::ELEMENT_WHERE) && !d.any(|v| v.has(vf::ELEMENT)) {
                    return vec![];
                }
                d.set(gf::ELEMENT_WHERE, false);
                // The kind the WHERE reads it as is the kind its pattern must give it.
                return Self::discharge(
                    d,
                    |_| true,
                    |v, k| {
                        v.has(vf::ELEMENT)
                            && narrow(k, Kind::Element).is_some()
                            && v.decl.is_none_or(|e| fits(k, e))
                    },
                    |v, r| Var {
                        decl: r
                            .need
                            .filter(|k| matches!(k, Kind::Node | Kind::Edge))
                            .or(v.decl),
                        ..Self::absorb(v, r)
                    },
                    true,
                );
            }
            // 16.3 SR 3-4, 16.6 SR 7.
            "path pattern" => {
                let selective = d.has(gf::SELECTIVE);
                d.update(|v| {
                    let v = if v.has(vf::PATH_VAR) {
                        Var {
                            decl: Some(Kind::Path),
                            ..v.without(vf::PATH_VAR)
                        }
                    } else {
                        v
                    };
                    if selective && v.decl.is_some() {
                        v.with(vf::SELECTIVE)
                    } else {
                        v
                    }
                });
                d.set(gf::SELECTIVE, false);
            }
            "subpath variable" => d.set(gf::SUBPATH, true),
            "path search prefix" => {
                d.set(gf::SELECTIVE, node.items != [Item::Def("all path search")])
            }
            "keep clause" => d.set(gf::SELECTIVE, false),
            // 16.7 SR 22 d-f (reading): nothing declared under these.
            "quantified path primary"
            | "questioned path primary"
            | "path pattern union"
            | "path multiset alternation" => {
                if d.any(|v| v.decl.is_some() || v.has(vf::ELEMENT | vf::PATH_VAR)) {
                    return vec![];
                }
            }
            // 16.7 SR 24, 4.11.5: a parenthesized WHERE sees the singletons declared inside.
            "parenthesized path pattern expression" => {
                return Self::discharge(
                    d,
                    |_| true,
                    |v, k| {
                        v.decl
                            .is_some_and(|e| matches!(e, Kind::Node | Kind::Edge) && fits(k, e))
                    },
                    Self::absorb,
                    true,
                );
            }
            // 20.12 SR 10-11: the pattern's WHERE sees its variables. Names are fresh, so a
            // query nested in it joins none of them.
            "graph pattern" => {
                d.set(gf::SUBPATH, false);
                return Self::discharge(
                    d,
                    |_| true,
                    |v, k| v.decl.is_some_and(|e| fits(k, e)),
                    Self::absorb,
                    true,
                );
            }
            // 16.3 SR 12: with YIELD, only what it lists is bound after.
            "graph pattern yield clause" => d.set(gf::PATTERN_YIELD, true),
            "graph pattern binding table" if d.has(gf::PATTERN_YIELD) => {
                d.set(gf::PATTERN_YIELD, false);
                // 16.3 SR 12: each variable yielded once, so a declaration takes one item.
                let drafts = Self::discharge(
                    d,
                    |v| v.has(vf::YIELDED),
                    |v, k| v.decl.is_some_and(|e| fits(k, e)) && !v.has(vf::YIELDED),
                    Self::absorb,
                    true,
                );
                return drafts
                    .into_iter()
                    .map(|mut d| {
                        d.update(|v| {
                            let v = if v.decl.is_some() && !v.has(vf::YIELDED) {
                                v.with(vf::HIDDEN)
                            } else {
                                v
                            };
                            v.without(vf::YIELDED)
                        });
                        d
                    })
                    .collect();
            }
            // 14.4, 16.3 SR 10, 16: a declaration is new, or joins a bound singleton.
            "simple match statement" => return Self::bind(d, Var::joinable),
            // 16.5 SR 10-11 (reading): only a bare node joins.
            "insert statement" => {
                return Self::bind(d, |v| v.decl == Some(Kind::Node) && !v.has(vf::INSERT_FULL));
            }
            "let statement" | "for statement" | "named procedure call" => {
                d.update(|v| {
                    if v.has(vf::NEW) {
                        Var {
                            out: Some(Kind::Value),
                            ..v.without(vf::NEW)
                        }
                    } else {
                        v
                    }
                });
                d.set(gf::STATEMENT, true);
            }
            // They bind the record (reading: not referenced).
            "binding variable definition block" => {
                d.close(|v| v.has(vf::NEW));
                d.set(gf::STATEMENT, true);
            }
            "filter statement"
            | "order by and page statement"
            | "set statement"
            | "remove statement"
            | "delete statement" => {
                d.update(|v| v.without(vf::TARGET));
                d.set(gf::STATEMENT, true);
            }
            // 20.5: a new name for the expression after IN.
            "let value expression" => d.close(|v| v.has(vf::NEW)),
            // 15.1 SR 9-12: the body's result columns are new and join the table.
            "inline procedure call" => {
                d.update(|v| v.without(vf::LISTED));
                d.set(gf::STATEMENT, true);
                d.flags &= !(gf::RESULT | gf::CLOSES | gf::FINISHED);
            }
            "yield item" => return Self::yield_item(d),
            // 9.2 SR 12: what follows NEXT sees what the statement before returned.
            "next statement" => {
                d.set(gf::NEXT, true);
                d.set(gf::STATEMENT, true);
                d.set(gf::CLOSES, true);
            }
            // 9.2 SR 12 b: a statement without a result leaves a unit table.
            "statement" => {
                if !d.has(gf::RESULT) {
                    d.update(|v| Var { out: None, ..v });
                    d.set(gf::CLOSES, true);
                }
                d.set(gf::FINISHED, false);
            }
            "composite query statement" => d.set(gf::FINISHED, false),
            "primitive result statement" => {
                if node.items == [Item::Token("FINISH")] {
                    d.flags |= gf::STATEMENT | gf::CLOSES | gf::RESULT | gf::FINISHED;
                } else {
                    d.flags |= gf::RESULT;
                    d.set(gf::PLAIN, false);
                }
            }
            "set quantifier" => d.set(gf::DISTINCT, node.items == [Item::Token("DISTINCT")]),
            "group by clause" => d.set(gf::GROUPED, true),
            "return item" => return Self::return_item(d),
            "return statement body" => return Self::return_body(node, d),
            "return statement" => {}
            // 14.10 SR 4 (reading): no aggregate and no nested query in a sort key.
            "sort key" => {
                if d.flags & (gf::AGGREGATES | gf::AGG_LOOSE | gf::AGG_IN_VE | gf::QUERY) != 0 {
                    return vec![];
                }
            }
            // 20.1 SR 7: an aggregate, not nested in another.
            "aggregate function" => {
                if d.flags & (gf::AGGREGATES | gf::AGG_LOOSE | gf::AGG_IN_VE) != 0 {
                    return vec![];
                }
                d.update(|v| v.without(vf::USED));
                d.set(gf::AGG_LOOSE, true);
                d.set(gf::DISTINCT, false);
            }
            // An aggregate is a return item's own only under the value expression its
            // aggregating value expression contains, not a nested one.
            "value expression" => {
                if d.has(gf::AGG_IN_VE) {
                    return vec![];
                }
                if d.has(gf::AGG_LOOSE) {
                    d.set(gf::AGG_LOOSE, false);
                    d.set(gf::AGG_IN_VE, true);
                }
            }
            "aggregating value expression" => {
                if d.has(gf::AGG_IN_VE) {
                    d.set(gf::AGG_IN_VE, false);
                    d.set(gf::AGGREGATES, true);
                }
            }
            // Subqueries in expressions: nothing from outside (reading), their output unread.
            "exists predicate"
            | "value query expression"
            | "nested binding table query specification" => {
                if d.any(Var::reference) {
                    return vec![];
                }
                d.close(|_| true);
                d.flags &= gf::TOKENS;
                d.set(gf::QUERY, true);
            }
            // 14.12 SR 7, 8: no reference (reading); without FROM, no `*`; every item named.
            "select statement" => {
                if d.any(|v| v.need.is_some()) || (d.has(gf::STAR) && !d.has(gf::SELECT_FROM)) {
                    return vec![];
                }
                // Its columns are its result, as a RETURN's are (14.2 SR 10 compares them).
                d.update(|v| Var {
                    out: v.column,
                    column: None,
                    ..Var::default()
                });
                d.close(|v| v.out.is_none());
                d.flags = (d.flags & gf::TOKENS) | gf::STATEMENT | gf::CLOSES | gf::RESULT;
            }
            "select statement body" => d.set(gf::SELECT_FROM, true),
            "select item alias" => {
                d.update(|v| {
                    if v.has(vf::CHOSEN) {
                        Var {
                            column: Some(Kind::Value),
                            ..v.without(vf::CHOSEN)
                        }
                    } else {
                        v
                    }
                });
                d.set(gf::SELECT_ALIAS, true);
            }
            "select item" => {
                if !d.has(gf::SELECT_ALIAS) {
                    return vec![];
                }
                d.set(gf::SELECT_ALIAS, false);
            }
            // 16.2 SR 3-4: the record and a unit table, nothing referenceable here.
            "use graph clause" => {
                if d.any(|v| v.need.is_some()) {
                    return vec![];
                }
            }
            "nested data-modifying procedure specification"
            | "focused nested data-modifying procedure specification" => {
                if d.any(|v| v.need.is_some()) {
                    return vec![];
                }
                d.close(|_| true);
                d.flags |= gf::STATEMENT | gf::CLOSES;
            }
            _ => {}
        }
        if NESTED.contains(&owner(def)) && !node.group {
            // A body of its own: what is bound outside is its record, not referenced here.
            if d.any(|v| v.need.is_some()) || d.has(gf::NEEDS_TABLE) {
                return vec![];
            }
        }
        if NO_SCOPE.contains(&owner(def)) {
            if d.any(|v| v.need.is_some()) {
                return vec![];
            }
            d.close(|v| v.column.is_none() && v.out.is_none());
        }
        vec![d]
    }

    /// A pattern's declarations, at the statement: each new, or joining a variable bound
    /// before (`joins`). Hidden ones that are new are bound by nothing after.
    fn bind(d: Draft, joins: impl Fn(&Var) -> bool) -> Vec<Draft> {
        let _span = tracing::trace_span!("bind").entered();
        let decls: Vec<usize> = d
            .live()
            .filter(|(_, v)| v.decl.is_some())
            .map(|(i, _)| i)
            .collect();
        let mut out = vec![d];
        for i in decls {
            let mut next = Vec::new();
            for d in out {
                let v = d.vars[i].unwrap();
                let k = v.decl.unwrap();
                let base = v.without(vf::HIDDEN | vf::SELECTIVE | vf::INSERT_FULL | vf::YIELDED);
                // New.
                let mut e = d.clone();
                e.vars[i] = Some(Var {
                    decl: None,
                    out: if v.has(vf::HIDDEN) {
                        None
                    } else {
                        Some(if k == Kind::Group { Kind::Group } else { k })
                    },
                    ..base
                });
                next.push(e);
                // A join.
                if joins(&v) {
                    let mut e = d.clone();
                    e.vars[i] = Some(Var {
                        decl: None,
                        need: Some(k),
                        ..base
                    });
                    next.push(e);
                }
            }
            out = next;
        }
        for d in &mut out {
            d.set(gf::STATEMENT, true);
        }
        out
    }

    /// 16.14 SR 7: in NEXT, a yielded name is a column of the statement before, the alias
    /// renames it; in a named procedure call, the name or its alias is a new column (16.14 SR
    /// 6, 15.1 SR 9).
    fn yield_item(d: Draft) -> Vec<Draft> {
        let name = d
            .live()
            .find(|(_, v)| v.has(vf::CHOSEN) && !v.has(vf::NEW))
            .map(|(i, _)| i);
        let alias = d.live().find(|(_, v)| v.has(vf::NEW)).map(|(i, _)| i);
        let Some(name) = name else { return vec![] };
        let mut out = Vec::new();
        // A procedure's result.
        let mut call = d.clone();
        let fresh = alias.unwrap_or(name);
        if alias.is_some() {
            call.vars[name] = None;
        }
        call.vars[fresh] = Some(Var {
            out: Some(Kind::Value),
            ..Var::default()
        });
        call.set(gf::CALL_YIELD, true);
        out.push(call);
        // A column of the statement before.
        for k in REFERENCEABLE {
            let mut e = d.clone();
            match alias {
                Some(a) => {
                    e.vars[name] = Some(Var {
                        need: Some(k),
                        ..Var::default()
                    });
                    e.vars[a] = Some(Var {
                        out: Some(k),
                        ..Var::default()
                    });
                }
                None => {
                    e.vars[name] = Some(Var {
                        need: Some(k),
                        out: Some(k),
                        ..Var::default()
                    })
                }
            }
            out.push(e);
        }
        out
    }

    /// 14.11 SR 8: a column is its alias, or a bare variable's name.
    fn return_item(mut d: Draft) -> Vec<Draft> {
        let bare = d
            .live()
            .find(|(_, v)| v.has(vf::BARE) && v.reference())
            .map(|(i, v)| (i, v.need));
        let alias = d.live().find(|(_, v)| v.has(vf::ALIASED)).map(|(i, _)| i);
        let Some(name) = alias.or(bare.map(|b| b.0)) else {
            return vec![];
        };
        // 14.11 SR 10 (Cor 1): with GROUP BY, an item is a grouping item or aggregates.
        let loose = bare.is_none() && !d.has(gf::AGGREGATES);
        d.update(|v| v.without(vf::BARE | vf::ALIASED));
        d.set(gf::LOOSE, loose);
        // The column has the bare variable's kind, chosen here; otherwise it is a value.
        let Some((b, Some(need))) = bare else {
            if let Some(v) = &mut d.vars[name] {
                v.column = Some(Kind::Value);
            }
            return vec![d];
        };
        REFERENCEABLE
            .into_iter()
            .filter(|&k| fits(need, k))
            .map(|k| {
                let mut e = d.clone();
                if let Some(v) = &mut e.vars[b] {
                    v.need = Some(k);
                }
                if let Some(v) = &mut e.vars[name] {
                    v.column = Some(k);
                }
                e
            })
            .collect()
    }

    /// 14.11 SR 6, 10-13: the columns become the table.
    fn return_body(node: &Node, mut d: Draft) -> Vec<Draft> {
        let _span = tracing::trace_span!("return_body").entered();
        if node.items.first() == Some(&Item::Token("NO")) {
            d.flags |= gf::STATEMENT | gf::CLOSES;
            return vec![d];
        }
        // A GROUP BY key is a variable of its own, or one an item uses.
        let keys: Vec<usize> = d
            .live()
            .filter(|(_, v)| v.has(vf::KEY) && v.column.is_none() && !v.has(vf::USED))
            .map(|(i, _)| i)
            .collect();
        let mut drafts = vec![d];
        for k in keys {
            let mut next = Vec::new();
            for d in drafts {
                let kv = d.vars[k].unwrap();
                for (i, v) in d.live() {
                    if i == k || !v.has(vf::USED) || v.has(vf::KEY) {
                        continue;
                    }
                    if let Some(need) =
                        narrow(v.need.unwrap_or(Kind::Any), kv.need.unwrap_or(Kind::Any))
                        && v.column.is_none_or(|c| fits(need, c))
                    {
                        let mut e = d.clone();
                        e.merge(
                            k,
                            i,
                            Var {
                                need: Some(need),
                                ..v.with(vf::KEY)
                            },
                        );
                        next.push(e);
                    }
                }
                next.push(d);
            }
            drafts = next;
        }
        let mut out = Vec::new();
        for mut d in drafts {
            let used: Vec<Var> = d
                .live()
                .filter(|(_, v)| v.has(vf::USED))
                .map(|(_, v)| *v)
                .collect();
            if d.has(gf::GROUPED) {
                if d.has(gf::LOOSE) || used.iter().any(|v| !v.has(vf::KEY)) {
                    continue;
                }
            } else if d.has(gf::AGGREGATES) && !used.is_empty() {
                continue;
            }
            if d.has(gf::STAR) {
                if d.has(gf::GROUPED) {
                    continue;
                }
                d.set(gf::NEEDS_TABLE, true);
            } else {
                d.set(gf::CLOSES, true);
            }
            let plain = !d.has(gf::DISTINCT) && !d.has(gf::AGGREGATES) && !d.has(gf::GROUPED);
            d.update(|v| Var {
                out: v.column,
                column: None,
                ..v.without(vf::USED | vf::KEY)
            });
            d.flags &= !(gf::STAR | gf::DISTINCT | gf::GROUPED | gf::AGGREGATES | gf::LOOSE);
            d.set(gf::PLAIN, plain);
            d.set(gf::STATEMENT, true);
            out.push(d);
        }
        out
    }
}

/// A global flag's bit as a fact, and a variable flag's.
fn global(flag: u32) -> u32 {
    flag.trailing_zeros()
}

fn per_var(flag: u16) -> u32 {
    32 + flag.trailing_zeros()
}

/// Subqueries in expressions: they clear what flows up from their body.
const SUBQUERIES: [&str; 3] = [
    "exists predicate",
    "value query expression",
    "nested binding table query specification",
];

impl Context for Scope {
    type Label = Label;

    fn name(&self) -> &str {
        "binding variables in scope"
    }

    /// Who reads each flag, from the arms of `finish_def`, `combine` and `return_body`.
    /// Statements clear what only flows inside one (the boundary in `finish`), and reject a
    /// pending aggregate.
    fn facts(&self) -> Vec<FactSpec> {
        let statements = || STATEMENTS.to_vec();
        let with = |mut v: Vec<&'static str>, more: &[&'static str]| {
            v.extend_from_slice(more);
            v
        };
        let spec = |bit,
                    name,
                    readers: &[&'static str],
                    rejecters: Vec<&'static str>,
                    clearers: Vec<&'static str>| FactSpec {
            bit,
            name,
            readers: readers.to_vec(),
            rejecters,
            clearers,
        };
        vec![
            // Only a return item asks whether a reference is bare.
            spec(
                global(gf::TOKENS),
                "tokens",
                &["return item"],
                vec![],
                statements(),
            ),
            spec(
                per_var(vf::BARE),
                "bare",
                &["return item"],
                vec![],
                statements(),
            ),
            // Grouping is checked by the RETURN body.
            spec(
                per_var(vf::USED),
                "used",
                &["return statement body"],
                vec![],
                with(statements(), &["aggregate function", "grouping element"]),
            ),
            spec(
                per_var(vf::KEY),
                "key",
                &["return statement body"],
                vec![],
                statements(),
            ),
            spec(
                global(gf::DISTINCT),
                "distinct",
                &["return statement body"],
                vec![],
                with(statements(), &["aggregate function"]),
            ),
            // 14.10 SR 4: a sort key holds no nested query.
            spec(
                global(gf::QUERY),
                "query",
                &["sort key"],
                vec![],
                with(statements(), &SUBQUERIES),
            ),
            // 20.1 SR 7: an aggregate is a return item's own, rejected at any other statement.
            spec(
                global(gf::AGG_LOOSE),
                "aggregate below",
                &["value expression", "aggregate function"],
                statements(),
                SUBQUERIES.to_vec(),
            ),
            spec(
                global(gf::AGG_IN_VE),
                "aggregate in a value expression",
                &[
                    "value expression",
                    "aggregating value expression",
                    "aggregate function",
                ],
                statements(),
                SUBQUERIES.to_vec(),
            ),
            spec(
                global(gf::AGGREGATES),
                "aggregates",
                &[
                    "return item",
                    "return statement body",
                    "sort key",
                    "aggregate function",
                ],
                statements(),
                SUBQUERIES.to_vec(),
            ),
            // 16.4 SR 4 (reading): one subpath variable per graph pattern.
            spec(
                global(gf::SUBPATH),
                "subpath",
                &["graph pattern"],
                vec![],
                vec![],
            ),
            spec(
                global(gf::SELECTIVE),
                "selective prefix",
                &["path pattern", "keep clause"],
                vec![],
                statements(),
            ),
        ]
    }

    fn project(&self, l: &Label, m: Masks) -> Projection<Label> {
        let (global_live, global_doomed) = (m.live as u32, m.doomed as u32);
        let (var_live, var_doomed) = ((m.live >> 32) as u16, (m.doomed >> 32) as u16);
        if l.flags & global_doomed != 0 || l.vars.iter().any(|v| v.flags & var_doomed != 0) {
            return Projection::Reject;
        }
        if l.flags & !global_live == 0 && l.vars.iter().all(|v| v.flags & !var_live == 0) {
            return Projection::Keep;
        }
        let mut d = Draft::of(l);
        d.flags &= global_live;
        d.update(|v| Var {
            flags: v.flags & var_live,
            ..v
        });
        match d.done(self.caps) {
            Some((l, link)) => Projection::Replace(l, link),
            None => Projection::Reject,
        }
    }

    fn slots(&self, l: &Label) -> usize {
        l.vars.len()
    }

    fn empty(&self, _: &Node) -> Label {
        Label::default()
    }

    fn push(
        &self,
        node: &Node,
        pos: usize,
        partial: &Label,
        child: Option<&Label>,
    ) -> Vec<(Label, Link)> {
        let Some(child) = child else {
            let mut d = Draft::of(partial);
            d.set(gf::TOKENS, true);
            return d.done(self.caps).into_iter().collect();
        };
        let def = owner(node.def);
        // A spelled name with no role yet goes only where a role is given.
        if child.vars.iter().any(|v| v.has(vf::CHOSEN))
            && !NAMING.contains(&def)
            && !matches!(def, "field" | "field type" | "yield item")
        {
            return vec![];
        }
        let item = node.items[pos];
        match (def, item) {
            // 14.10 SR 4: ORDER BY after RETURN sees its columns, and the names before it
            // when it neither aggregates, groups nor removes duplicates.
            ("primitive result statement", _) if pos > 0 => {
                let plain = partial.has(gf::PLAIN);
                let d = Draft::of(partial);
                return meet(&d, child, |cv| {
                    let mut t = Vec::new();
                    if let Some(k) = cv.need.filter(|_| cv.reference()) {
                        for (i, pv) in d.live() {
                            if pv.out.is_some_and(|o| fits(k, o)) {
                                t.push(Target::Into(i, *pv));
                            }
                            if plain
                                && pv.out.is_none()
                                && let Some(v) = joined(pv, cv)
                            {
                                t.push(Target::Into(i, v));
                            }
                        }
                        if plain {
                            t.push(Target::New);
                        }
                    } else {
                        t.push(Target::New);
                    }
                    t
                })
                .into_iter()
                .filter_map(|mut d| {
                    d.flags |= child.flags & !(gf::STATEMENT | gf::CLOSES);
                    d.done(self.caps)
                })
                .collect();
            }
            // 20.5: the expression after IN sees the definitions.
            ("let value expression", _) if pos == 3 => {
                let d = Draft::of(partial);
                return meet(&d, child, |cv| {
                    let mut t = vec![Target::New];
                    if let Some(k) = cv.need.filter(|_| cv.reference()) {
                        for (i, pv) in d.live() {
                            if pv.has(vf::NEW) && fits(k, Kind::Value) {
                                t.push(Target::Into(i, *pv));
                            }
                            if !pv.has(vf::NEW)
                                && let Some(v) = joined(pv, cv)
                            {
                                t.push(Target::Into(i, v));
                            }
                        }
                    }
                    t
                })
                .into_iter()
                .filter_map(|mut d| {
                    d.flags |= child.flags;
                    d.done(self.caps)
                })
                .collect();
            }
            // 15.1 SR 5-7, 15.2: the body sees nothing from outside (reading); its result
            // columns are new.
            ("inline procedure call", _)
                if matches!(item, Item::Def("nested procedure specification")) =>
            {
                let mut d = Draft::of(partial);
                if child.vars.iter().any(|v| v.need.is_some()) {
                    return vec![];
                }
                for v in &child.vars {
                    let out = if child.has(gf::RESULT) { v.out } else { None };
                    d.vars.push(Some(Var {
                        out,
                        ..Var::default()
                    }));
                    d.map.push(Some(d.vars.len() - 1));
                }
                d.flags |= child.flags & gf::TOKENS;
                d.flags |= gf::STATEMENT;
                return d.done(self.caps).into_iter().collect();
            }
            // 14.2 SR 5, 10: each branch gets the same input and returns the same columns.
            ("composite query expression", _) if pos == 2 => {
                if partial.has(gf::FINISHED) || child.has(gf::FINISHED) {
                    return vec![];
                }
                let d = Draft::of(partial);
                return meet(&d, child, |cv| {
                    let mut t = Vec::new();
                    for (i, pv) in d.live() {
                        // One column name: a bare variable's, an alias's, or both.
                        let need = match (pv.need, cv.need) {
                            (Some(a), Some(b)) if a != b => continue,
                            (a, b) => a.or(b),
                        };
                        if cv.out.is_some() && pv.out == cv.out {
                            t.push(Target::Into(
                                i,
                                Var {
                                    need,
                                    flags: pv.flags | cv.flags,
                                    ..*pv
                                },
                            ));
                        }
                        if cv.out.is_none()
                            && pv.out.is_none()
                            && let Some(v) = joined(pv, cv)
                        {
                            t.push(Target::Into(i, v));
                        }
                    }
                    if cv.out.is_none() {
                        t.push(Target::New);
                    }
                    t
                })
                .into_iter()
                .filter_map(|mut d| {
                    // Every column of the first branch met one of the second's.
                    let met: Vec<usize> = d.map[partial.vars.len()..]
                        .iter()
                        .flatten()
                        .copied()
                        .collect();
                    let columns = partial
                        .vars
                        .iter()
                        .enumerate()
                        .filter(|(_, v)| v.out.is_some());
                    for (i, _) in columns {
                        if !met.contains(&i) {
                            return None;
                        }
                    }
                    d.flags |= child.flags & gf::TOKENS;
                    d.done(self.caps)
                })
                .collect();
            }
            // 13.3 SR 4-5: the item's variable is an element, changed once.
            (
                "set property item"
                | "set all properties item"
                | "set label item"
                | "remove property item"
                | "remove label item",
                Item::Def("binding variable reference"),
            ) => {
                let mut c = child.clone();
                for v in &mut c.vars {
                    let Some(k) = v.need.and_then(|n| narrow(n, Kind::Element)) else {
                        return vec![];
                    };
                    *v = Var {
                        need: Some(k),
                        ..v.with(vf::TARGET).without(vf::USED | vf::BARE)
                    };
                }
                return self.combine(node, partial, &c);
            }
            // 13.5 SR 5: an item that is a reference names a node, an edge or a value, never
            // a path (the value's type is the types rule's to check).
            ("delete item", Item::Def("value expression")) => {
                let mut c = child.clone();
                for v in &mut c.vars {
                    if !v.has(vf::BARE) || !v.pending() {
                        continue;
                    }
                    let Some(k) = v.need.and_then(|n| narrow(n, Kind::Deletable)) else {
                        return vec![];
                    };
                    v.need = Some(k);
                }
                return self.combine(node, partial, &c);
            }
            // The yield clause: in NEXT, columns of the statement before; in a named call,
            // results.
            ("next statement", Item::Group(_)) | ("named procedure call", Item::Group(_))
                if child.vars.iter().any(|v| v.out.is_some()) || child.has(gf::CALL_YIELD) =>
            {
                let call = def == "named procedure call";
                if child.has(gf::CALL_YIELD) != call && !child.vars.is_empty() {
                    return vec![];
                }
                let mut c = child.clone();
                c.flags &= !gf::CALL_YIELD;
                if call {
                    for v in &mut c.vars {
                        *v = Var {
                            out: None,
                            ..v.with(vf::NEW)
                        };
                    }
                    return self.combine(node, partial, &c);
                }
                // NEXT YIELD: a statement that sees the columns it names, and binds them.
                c.flags |= gf::STATEMENT | gf::CLOSES;
                let mut d = Draft::of(partial);
                for v in &c.vars {
                    d.vars.push(Some(*v));
                    d.map.push(Some(d.vars.len() - 1));
                }
                d.flags |= c.flags;
                return d.done(self.caps).into_iter().collect();
            }
            _ => {}
        }
        if child.has(gf::CALL_YIELD) {
            return vec![];
        }
        self.combine(node, partial, child)
    }

    fn finish(&self, node: &Node, partial: &Label) -> Vec<(Label, Link)> {
        let def = node.def;
        let mut out = Vec::new();
        for mut d in self.finish_def(node, partial) {
            // A bare reference stays bare through nodes with no token and one child that
            // derives something: `x` is bare, `NOT x` and `(x)` are not.
            let tokens = node
                .items
                .iter()
                .any(|it| matches!(it, Item::Token(_) | Item::Prose(_)));
            if tokens {
                d.update(|v| v.without(vf::BARE));
            }
            // What only flows inside a statement stops at it. An aggregate outside a RETURN
            // needs a group variable to aggregate (20.1 SR 7), and none is referenced here.
            if Self::statement(def) && !node.group {
                if d.flags & (gf::AGGREGATES | gf::AGG_LOOSE | gf::AGG_IN_VE) != 0 {
                    continue;
                }
                if d.any(|v| v.has(vf::CHOSEN)) && !NAMING.contains(&owner(def)) {
                    continue;
                }
                // 14.11 SR 6 (reading): `RETURN *` returns what a statement before it in the
                // same sequence binds; met there, or nowhere.
                if d.has(gf::NEEDS_TABLE)
                    && !matches!(
                        owner(def),
                        "return statement" | "primitive result statement"
                    )
                {
                    continue;
                }
                d.update(|v| v.without(vf::USED | vf::KEY | vf::BARE));
                d.flags &= !(gf::DISTINCT | gf::GROUPED | gf::SELECTIVE | gf::QUERY | gf::LOOSE);
                if !matches!(
                    owner(def),
                    "yield clause"
                        | "let variable definition list"
                        | "let variable definition"
                        | "value variable definition"
                        | "for item"
                ) {
                    d.set(gf::STATEMENT, true);
                }
            }
            if def == "GQL-program" {
                // A program's output is never read.
                if d.any(|v| v.need.is_some()) || d.has(gf::NEEDS_TABLE) {
                    continue;
                }
                d.close(|_| true);
                d.flags &= gf::TOKENS;
            }
            out.extend(d.done(self.caps));
        }
        out
    }

    fn top(&self, l: &Label) -> bool {
        l.vars.is_empty()
    }

    fn spells(&self, def: &str, l: &Label) -> bool {
        matches!(def, "binding variable" | "identifier")
            && l.vars.len() == 1
            && l.vars[0].has(vf::CHOSEN)
    }

    fn show(&self, l: &Label) -> String {
        let kind = |k: Option<Kind>| k.map_or(String::new(), |k| format!("{k:?}").to_lowercase());
        let vars: Vec<String> = l
            .vars
            .iter()
            .map(|v| {
                let mut s = Vec::new();
                if v.need.is_some() {
                    s.push(format!("need-{}", kind(v.need)));
                }
                if v.out.is_some() {
                    s.push(format!("out-{}", kind(v.out)));
                }
                if v.decl.is_some() {
                    s.push(format!("decl-{}", kind(v.decl)));
                }
                if v.column.is_some() {
                    s.push(format!("col-{}", kind(v.column)));
                }
                if v.flags != 0 {
                    s.push(format!("{:x}", v.flags));
                }
                s.join(".")
            })
            .collect();
        let mut out = vars.join("+");
        let flags = l.flags & !gf::TOKENS;
        if flags != 0 {
            out = format!("{out}#{flags:x}");
        }
        out
    }
}
