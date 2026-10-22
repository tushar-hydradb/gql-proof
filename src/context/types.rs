//! Static types of value expressions (ISO/IEC 39075 2024 + Cor 1) as a rule under scope
//! (`context::pair`): every expression synthesizes a class, the categories and operators the
//! grammar fixes check it, and each variable of scope's label carries what its uses need of
//! it or, for a value variable, the class its definition gave it.
//!
//! A reference does not guess its class: it is the class of its variable, deferred
//! (`Ty::Slot`). Categories and parentheses pass it on, as they pass an opaque value, so
//! `RETURN x` is one label. An operator, a function or a site that would refuse an opaque
//! operand chooses the class there, writing on the variable what it needs (`x + 1`: a value of
//! exact numeric class, `x.k`: a node or an edge), and the variable's binder meets the need:
//! a node, edge or path variable fits a need of its kind, a value variable one of its class.
//!
//! Classes are coarse: exact and approximate numbers, strings, bytes, booleans, the five
//! temporal instants, year-month and day-time durations, lists, records, nodes, edges, paths,
//! null, dynamic and opaque. Dynamic is a property of a node or edge with no catalog (20.11 SR
//! 3 b) or a parameter: 4.14.4 lets a dynamic operand stand wherever a class is checked.
//! Opaque is what is not followed, accepted only where any type is.
//!
//! Sound, not complete; `verify::types` (written separately, from the standard alone) checks
//! every tree. Readings that forbid more than ISO:
//! - a LET or VALUE variable has its definition's class only if that is an exact number, a
//!   string, a boolean or dynamic, and not another variable's; every other value variable (FOR,
//!   a column, a YIELD, an alias) is opaque. two columns of different classes meet as opaque
//! - list elements and record fields are not followed: lists and records are compared,
//!   combined or cast only where that holds whatever their elements are
//! - comparisons need comparable classes whatever the claim (22.13, 22.14 make it a
//!   conformance rule, GA04); ordering only on scalars, equality on nodes and edges too, never
//!   on paths (GA09)
//! - the datetime and duration primaries are checked statically (20.26, 20.28 GR 1 leave
//!   them to run time)
//! - `DURATION({...})`, `element_id` and VALUE subqueries are opaque
//! - CASE, NULLIF and COALESCE results are exact numbers or NULL, and a simple CASE operand is
//!   an exact number, a string, a node or an edge: one class folded up instead of every
//!   combination
//! - an operator with a null operand is an exact number, not the null type, and a function
//!   that would return the null type is refused
//! - a property's source is a node or an edge variable, never a dynamic value variable
//! - generated temporal and duration strings are the leaf provider's: a time or datetime
//!   string has no offset, a duration string is year-month, an interval a DAY

use super::pair::{Step, Under};
use super::scope::{Kind, Label as Scoped, Scope, View};
use super::{Link, Slot};
use crate::cfg::{Cfg, Sym};
use crate::refine::{Item, Node};
use std::collections::{BTreeMap, HashSet};

/// A type class.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum Class {
    Bool,
    Exact,
    Approx,
    Str,
    Bytes,
    Date,
    LocalTime,
    ZonedTime,
    LocalDatetime,
    ZonedDatetime,
    YearMonth,
    DayTime,
    List,
    Record,
    Node,
    Edge,
    Path,
    Null,
    Dynamic,
    Opaque,
}

use Class::*;

impl Class {
    fn numeric(self) -> bool {
        matches!(self, Exact | Approx)
    }

    fn instant(self) -> bool {
        matches!(
            self,
            Date | LocalTime | ZonedTime | LocalDatetime | ZonedDatetime
        )
    }

    fn duration(self) -> bool {
        matches!(self, YearMonth | DayTime)
    }

    /// Ordered by 22.14 with itself.
    fn scalar(self) -> bool {
        self.numeric() || self.instant() || self.duration() || matches!(self, Str | Bytes | Bool)
    }
}

/// The value classes a variable's uses choose among.
const VALUES: [Class; 3] = [Exact, Str, Bool];

/// The classes a value variable keeps; any other is opaque.
fn follow(c: Class) -> Class {
    if matches!(c, Exact | Str | Bool | Dynamic) {
        c
    } else {
        Opaque
    }
}

/// An expression's class: known, or its variable's (slot of scope's label), still to choose.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum Ty {
    Is(Class),
    /// The variable, and the classes of [`DOMAIN`] the sites it passed allow (a bit each).
    Slot(Slot, u8),
}

/// The classes a variable's class is chosen among.
const DOMAIN: [Class; 6] = [Exact, Str, Bool, Node, Edge, Path];
const ANY: u8 = (1 << DOMAIN.len()) - 1;

/// What a use asks of a variable.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum Req {
    Node,
    Edge,
    /// A node or an edge.
    Element,
    Path,
    /// A value used as this class.
    Value(Class),
}

/// What the subtree says of one of scope's variables.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash, Default)]
pub enum Entry {
    #[default]
    Free,
    Need(Req),
    /// A value variable of this class (its definition is in the subtree).
    Has(Class),
}

use Entry::{Free, Has, Need};

fn narrow(a: Req, b: Req) -> Option<Req> {
    match (a, b) {
        _ if a == b => Some(a),
        (Req::Element, r @ (Req::Node | Req::Edge))
        | (r @ (Req::Node | Req::Edge), Req::Element) => Some(r),
        _ => None,
    }
}

/// One entry for two occurrences of one variable.
fn meet(a: Entry, b: Entry) -> Option<Entry> {
    match (a, b) {
        (Free, e) | (e, Free) => Some(e),
        (Has(x), Has(y)) => Some(Has(if x == y { x } else { Opaque })),
        (Has(c), Need(Req::Value(w))) | (Need(Req::Value(w)), Has(c)) => {
            (c == w || c == Dynamic).then_some(Has(c))
        }
        (Has(_), Need(_)) | (Need(_), Has(_)) => None,
        (Need(x), Need(y)) => narrow(x, y).map(Need),
    }
}

/// The class of a variable that closed with `e`.
fn settled(e: Entry) -> Ty {
    Ty::Is(match e {
        Has(c) | Need(Req::Value(c)) => c,
        Need(Req::Node) => Node,
        Need(Req::Edge) => Edge,
        Need(Req::Path) => Path,
        _ => Opaque,
    })
}

/// Whether a variable scope needs as `k` may carry `e`.
fn fits_need(k: Kind, e: Entry) -> bool {
    matches!(
        (k, e),
        (_, Free)
            | (Kind::Any, _)
            | (Kind::Node, Need(Req::Node | Req::Element))
            | (Kind::Edge, Need(Req::Edge | Req::Element))
            | (Kind::Element, Need(Req::Node | Req::Edge | Req::Element))
            | (Kind::Path, Need(Req::Path))
            | (Kind::Value, Need(Req::Value(_)) | Has(_))
    )
}

/// The classes a deferred reference to a variable may be given, and what each asks of it.
fn domain(e: Entry, v: View) -> Vec<(Class, Req)> {
    let value = |c: Class| (c, Req::Value(c));
    let node = (Node, Req::Node);
    let edge = (Edge, Req::Edge);
    let path = (Path, Req::Path);
    match e {
        Has(Dynamic) => VALUES.map(value).to_vec(),
        Has(Opaque) => vec![],
        Has(c) | Need(Req::Value(c)) => vec![value(c)],
        Need(Req::Node) => vec![node],
        Need(Req::Edge) => vec![edge],
        Need(Req::Element) => vec![node, edge],
        Need(Req::Path) => vec![path],
        Free => match v.out.or(v.decl).or(v.column).or(v.need) {
            Some(Kind::Node) => vec![node],
            Some(Kind::Edge) => vec![edge],
            Some(Kind::Path) => vec![path],
            Some(Kind::Value) => VALUES.map(value).to_vec(),
            Some(Kind::Element) => vec![node, edge],
            Some(Kind::Group) => vec![],
            Some(Kind::Any) | None => {
                let mut d = VALUES.map(value).to_vec();
                d.extend([node, edge, path]);
                d
            }
        },
    }
}

/// Synthesized facts a node's parent (or a few ancestors) reads.
mod fact {
    /// An optional sign, NOT or IS of a factor or test is there.
    pub const MODIFIED: u16 = 1;
    /// A comparison operator orders (`<` and the like).
    pub const ORDERING: u16 = 1 << 1;
    /// A duration qualifier is YEAR TO MONTH.
    pub const YEARS: u16 = 1 << 2;
    /// The set function a `<general set function type>` names.
    pub const SUM_AVG: u16 = 1 << 3;
    pub const COUNT: u16 = 1 << 4;
    pub const MIN_MAX: u16 = 1 << 5;
    pub const COLLECT: u16 = 1 << 6;
    pub const STDDEV: u16 = 1 << 7;
    pub const SET_KIND: u16 = SUM_AVG | COUNT | MIN_MAX | COLLECT | STDDEV;
    /// A `<value type>` is immaterial, the dynamic union, holds NOT NULL.
    pub const IMMATERIAL: u16 = 1 << 8;
    pub const ANY_TYPE: u16 = 1 << 9;
    pub const NOT_NULL: u16 = 1 << 10;
    /// An element operand of ALL_DIFFERENT or SAME is a node, an edge.
    pub const SAW_NODE: u16 = 1 << 11;
    pub const SAW_EDGE: u16 = 1 << 12;
}

/// What a subtree says: its class, per variable of scope's label an entry, and what only the
/// nodes right above read. While a production is scanned, the classes of its children so far.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash, Default)]
pub struct Label {
    class: Option<Ty>,
    vars: Vec<Entry>,
    facts: u16,
    /// The class a `<value type>` names.
    target: Option<Class>,
    /// The class a CASE's or COALESCE's results combine to so far; also the first operand of
    /// DURATION_BETWEEN.
    result: Option<Class>,
    /// The second operand of DURATION_BETWEEN.
    when: Option<Class>,
    /// The simple CASE operand classes every when operand so far accepts (bits of
    /// [`OPERANDS`]).
    operand: Option<u8>,
    kids: Vec<Option<Ty>>,
}

impl Label {
    fn has(&self, f: u16) -> bool {
        self.facts & f != 0
    }

    pub fn class(&self) -> Option<Ty> {
        self.class
    }

    pub fn vars(&self) -> &[Entry] {
        &self.vars
    }

    /// While a production is scanned: its children's classes so far.
    pub fn kids(&self) -> &[Option<Ty>] {
        &self.kids
    }
}

/// What a simple CASE's operand may be (reading, to keep labels few).
const OPERANDS: [Class; 4] = [Exact, Str, Node, Edge];

/// The definition a desugaring group belongs to, or the definition itself.
fn owner(def: &str) -> &str {
    def.split('/').next().unwrap_or(def)
}

/// The text between the quotes of a literal's string.
fn quoted(text: &str) -> &str {
    text.split('\'').nth(1).unwrap_or(text)
}

/// 21.2 SR 63, 65: a time or datetime string with a zone displacement.
fn zoned(text: &str) -> bool {
    let s = quoted(text);
    let time = s.rsplit_once('T').map_or(s, |(_, t)| t);
    time.contains(['+', '-', 'Z'])
}

/// 21.2 SR 66, 71, 72, 20.29: a duration string or interval is day-time when it names days or
/// a time, year-month otherwise. With no text (the fixed point), the leaf provider's:
/// `'P1Y2M'`, `INTERVAL '1' DAY`.
fn duration_text(text: Option<&str>, interval: bool) -> Class {
    match text {
        None if interval => DayTime,
        None => YearMonth,
        Some(t) if interval => {
            if ["YEAR", "MONTH"].iter().any(|u| t.ends_with(u)) {
                YearMonth
            } else {
                DayTime
            }
        }
        Some(t) if quoted(t).contains(['D', 'T']) => DayTime,
        Some(_) => YearMonth,
    }
}

/// Accepted where `want` is checked: the class itself, null (21.2 SR 67 a types it from its
/// context) or a dynamic one (4.14.4).
fn fits(c: Option<Class>, want: impl Fn(Class) -> bool) -> bool {
    matches!(c, Some(c) if want(c) || matches!(c, Null | Dynamic))
}

/// 22.13, 22.14 (reading: as without GA04 and GA09): whether two classes may be compared.
fn comparable(a: Class, b: Class, ordering: bool) -> bool {
    match (a, b) {
        (Opaque, _) | (_, Opaque) => false,
        (Null | Dynamic, _) | (_, Null | Dynamic) => true,
        (Node, Node) | (Edge, Edge) => !ordering,
        _ => a.scalar() && (a == b || a.numeric() && b.numeric()),
    }
}

/// 22.18, 22.19 (reading: without GV65): the class of a CASE or COALESCE, if its results
/// combine. Nulls drop out; all of them null is no type (20.7 SR 3).
fn combine(classes: &[Class]) -> Option<Class> {
    let mut out: Option<Class> = None;
    for &c in classes.iter().filter(|&&c| c != Null) {
        out = Some(match (out, c) {
            (None, c) => c,
            (Some(Opaque), _) | (_, Opaque) => return None,
            (Some(Dynamic), _) | (_, Dynamic) => Dynamic,
            (Some(a), b) if a == b && a != Record => a,
            (Some(a), b) if a.numeric() && b.numeric() => Approx,
            (Some(ZonedDatetime | LocalDatetime), ZonedDatetime | LocalDatetime) => ZonedDatetime,
            (Some(ZonedTime | LocalTime), ZonedTime | LocalTime) => ZonedTime,
            _ => return None,
        });
    }
    out
}

/// 20.8 Table 4 (reading: lists, records and the unfollowed classes only to a dynamic
/// target).
fn castable(from: Class, to: Class) -> bool {
    if to == Opaque || from == Opaque {
        return false;
    }
    if to == Dynamic || matches!(from, Null | Dynamic) {
        return true;
    }
    let datetime = |c: Class| matches!(c, LocalDatetime | ZonedDatetime);
    let time = |c: Class| matches!(c, LocalTime | ZonedTime);
    match from {
        Exact | Approx => to.numeric() || to == Str,
        Str => to.numeric() || to.instant() || to.duration() || matches!(to, Str | Bool),
        Date => matches!(to, Str | Date) || datetime(to),
        LocalTime | ZonedTime => to == Str || time(to) || datetime(to),
        LocalDatetime | ZonedDatetime => to == Str || to == Date || time(to) || datetime(to),
        YearMonth | DayTime => to == Str || to == from,
        Bool => matches!(to, Str | Bool),
        Bytes => to == Bytes,
        Path => to == Path,
        Node | Edge => to == from || to == Path,
        _ => false,
    }
}

/// 22.10 store assignment (reading: lists and records only to a dynamic target).
fn assignable(from: Class, to: Class) -> bool {
    match (from, to) {
        (Opaque, _) | (_, Opaque) => false,
        (_, Dynamic) | (Null | Dynamic, _) => true,
        (a, b) if a.numeric() && b.numeric() => true,
        (LocalTime | ZonedTime, LocalTime | ZonedTime) => true,
        (LocalDatetime | ZonedDatetime, LocalDatetime | ZonedDatetime) => true,
        (a, b) => a == b && !matches!(a, Record | List),
    }
}

/// 20.21 SR 1: the type of numeric operators' results. Null operands take the type from
/// their context (21.2 SR 67 a): the result is still a number.
fn arithmetic(classes: &[Class]) -> Class {
    if classes.contains(&Dynamic) {
        Dynamic
    } else if classes.contains(&Approx) {
        Approx
    } else {
        Exact
    }
}

fn merge_result(a: Class, b: Class) -> Option<Class> {
    match (a, b) {
        (Null, x) | (x, Null) => Some(x),
        _ => combine(&[a, b]),
    }
}

/// Two folded results as one: `None` if they do not combine.
fn merge_results(a: Option<Class>, b: Option<Class>) -> Option<Option<Class>> {
    match (a, b) {
        (None, x) | (x, None) => Some(x),
        (Some(a), Some(b)) => merge_result(a, b).map(Some),
    }
}

/// NULLIF and COALESCE, whose arguments are narrowed to exact numbers and nulls.
const NARROWED: &[&str] = &["case abbreviation"];

/// Expression nodes whose class nothing reads: carrying one would only multiply labels.
const UNREAD: &[&str] = &[
    "list element",
    "list element list",
    "list value constructor by enumeration",
    "field",
    "field list",
    "fields specification",
    "path element list",
    "path element list start",
    "path element list step",
    "path value constructor by enumeration",
    "when operand list",
    "simple when clause",
    "searched when clause",
    "else clause",
    "result",
    "date function parameters",
    "time function parameters",
    "datetime function parameters",
    "duration function parameters",
];

/// Where the expression grammar stops: statements and patterns nested in it.
const BOUNDARY: &[&str] = &[
    "nested query specification",
    "graph pattern",
    "match statement block",
    "binding table expression",
    "graph expression",
    "nested graph type specification",
];

/// Definitions outside the expression grammar that read their children's classes.
const READS: &[&str] = &[
    "opt typed value initializer",
    "value initializer",
    "value variable definition",
    "let variable definition",
    "aggregating value expression",
    "sort key",
    "return item",
    "for item source",
    "object expression primary",
    "graph reference value expression",
    "binding table reference value expression",
];

/// Where a class is used up: nothing above reads it.
const CONSUMERS: &[&str] = &[
    "value variable definition",
    "let variable definition",
    "sort key",
    "return item",
];

/// Where a result folds: the CASE family, and a list's elements (20.17 SR 3, 22.19).
const CASE_FAMILY: &[&str] = &[
    "case abbreviation",
    "simple case",
    "searched case",
    "simple when clause",
    "searched when clause",
    "when operand list",
    "else clause",
    "list element list",
    "list value constructor by enumeration",
];

/// Where a deferred class is chosen even though an opaque one would pass: the kind of an
/// element ALL_DIFFERENT and SAME compare.
const CHOOSE: &[&str] = &["element variable reference"];

pub struct Types {
    /// Definitions and groups of the expression grammar, where classes flow up.
    expressions: HashSet<String>,
}

/// Where each input slot of a step went: its output slot, or the entry it closed with.
struct Relinked {
    vars: Vec<Entry>,
    at: Vec<Result<Slot, Entry>>,
}

impl Relinked {
    /// `inputs` (the partial label's entries, then the child's) through `link` into `width`
    /// slots; `None` if two occurrences of one variable disagree, or one disagrees with what
    /// scope said of it (`views`, in step with `inputs`): a variable closed here is checked
    /// here or never.
    fn new(inputs: &[Entry], views: &[View], link: &Link, width: usize) -> Option<Relinked> {
        let mut vars = vec![Free; width];
        let mut locals: BTreeMap<Slot, Entry> = BTreeMap::new();
        let to = |i: usize| link.0.get(i).copied().flatten();
        for (i, e) in inputs.iter().enumerate() {
            match to(i) {
                Some(o) if (o as usize) < width => vars[o as usize] = meet(vars[o as usize], *e)?,
                Some(o) => {
                    let l = locals.entry(o).or_default();
                    *l = meet(*l, *e)?;
                }
                None => {}
            }
        }
        let at: Vec<Result<Slot, Entry>> = inputs
            .iter()
            .enumerate()
            .map(|(i, e)| match to(i) {
                Some(o) if (o as usize) < width => Ok(o),
                Some(o) => Err(locals[&o]),
                None => Err(*e),
            })
            .collect();
        for (i, v) in views.iter().enumerate() {
            let e = match at[i] {
                Ok(o) => vars[o as usize],
                Err(e) => e,
            };
            if !admits(*v, e) {
                return None;
            }
        }
        Some(Relinked { vars, at })
    }

    /// A class of the input whose slots start at `base`, in the output's slots.
    fn ty(&self, base: usize, t: Option<Ty>) -> Option<Ty> {
        match t? {
            Ty::Slot(s, m) => Some(match self.at[base + s as usize] {
                Ok(o) => Ty::Slot(o, m),
                Err(e) => settled(e),
            }),
            t => Some(t),
        }
    }
}

fn views(a: &Scoped) -> Vec<View> {
    (0..a.width()).map(|s| a.view(s)).collect()
}

/// Whether a variable scope says `v` of may carry `e`.
fn admits(v: View, e: Entry) -> bool {
    let kind = match (v.out.or(v.decl).or(v.column), e) {
        (Some(Kind::Node), Free | Need(Req::Node | Req::Element)) => true,
        (Some(Kind::Edge), Free | Need(Req::Edge | Req::Element)) => true,
        (Some(Kind::Path), Free | Need(Req::Path)) => true,
        (Some(Kind::Node | Kind::Edge | Kind::Path), _) => false,
        (Some(Kind::Value), Need(_)) => v.need.is_some(),
        _ => true,
    };
    kind && v.need.is_none_or(|k| fits_need(k, e))
}

/// Entries checked against scope's variables after a step: a node, edge or path variable
/// takes only a need of its kind (and, met, owes nothing more); a value variable bound with
/// no class from its definition is opaque.
fn reconcile(vars: &mut [Entry], a: &Scoped) -> bool {
    for (s, e) in vars.iter_mut().enumerate() {
        let v = a.view(s);
        let bound = v.out.or(v.decl).or(v.column);
        *e = match (bound, *e) {
            (Some(Kind::Node), Free | Need(Req::Node | Req::Element)) => Free,
            (Some(Kind::Edge), Free | Need(Req::Edge | Req::Element)) => Free,
            (Some(Kind::Path), Free | Need(Req::Path)) => Free,
            (Some(Kind::Node | Kind::Edge | Kind::Path), _) => return false,
            (Some(Kind::Value), Free) if v.need.is_none() => Has(Opaque),
            (Some(Kind::Value), Need(_)) if v.need.is_none() => return false,
            (None, Free) if v.new => Has(Opaque),
            (_, e) => e,
        };
        if v.need.is_some_and(|k| !fits_need(k, *e)) {
            return false;
        }
    }
    true
}

impl Types {
    pub fn new(cfg: &Cfg) -> Types {
        let mut seen = HashSet::new();
        let mut stack: Vec<String> = ["value expression", "value type", "search condition"]
            .into_iter()
            .map(String::from)
            .collect();
        while let Some(def) = stack.pop() {
            if BOUNDARY.contains(&def.as_str()) || !seen.insert(def.clone()) {
                continue;
            }
            for nt in (0..cfg.nts.len() as u32).filter(|&n| cfg.base(n) == def) {
                for &p in &cfg.nts[nt as usize].prods {
                    for &sym in &cfg.prod(p).rhs {
                        if let Sym::Nt(c) = sym {
                            stack.push(cfg.base(c).to_string());
                        }
                    }
                }
            }
        }
        Types { expressions: seen }
    }

    fn expression(&self, def: &str) -> bool {
        self.expressions.contains(owner(def))
    }

    fn reads(&self, def: &str) -> bool {
        self.expression(def) || READS.contains(&owner(def))
    }

    /// The class `node` synthesizes from its children's classes, and what it passes up;
    /// `None` rejects the node. The arms of the product-grammar automaton this replaces.
    fn eval(&self, node: &Node, kids: &[Option<Class>], acc: &Label) -> Option<Label> {
        let class = self.class_of(node, kids, acc)?;
        let mut out = Label {
            class: class.map(Ty::Is),
            ..Label::default()
        };
        self.facts(node, kids, acc, &mut out).then_some(out)
    }

    fn class_of(&self, node: &Node, kids: &[Option<Class>], acc: &Label) -> Option<Option<Class>> {
        let def = node.def;
        let classed: Vec<Class> = kids.iter().flatten().copied().collect();
        let only = match classed[..] {
            [c] => Some(c),
            _ => None,
        };
        let at = |item: &str| {
            node.items
                .iter()
                .position(|i| *i == Item::Def(item))
                .and_then(|p| kids.get(p).copied().flatten())
        };
        let token = |t: &str| node.items.contains(&Item::Token(t));
        let has = |f: u16| acc.has(f);
        let text = node.text;
        // A check that passes `c` on, or rejects.
        let check = |ok: bool, c: Option<Class>| ok.then_some(c);
        // An opaque value only passes through the categories, untouched: a function, an
        // operator or a keyword form takes no such operand.
        let call = node.items.iter().any(|i| matches!(i, Item::Token(_)))
            || node
                .items
                .iter()
                .skip(1)
                .any(|i| *i == Item::Def("left paren"));
        if call && classed.contains(&Opaque) {
            return None;
        }
        // A category over an untyped primary: the class it fixes, or an opaque value.
        let site = |want: fn(Class) -> bool| check(fits(only, want) || only == Some(Opaque), only);
        let typed = !classed.contains(&Opaque);
        match def {
            // Literals (21.2).
            "exact numeric literal" => Some(Some(Exact)),
            "approximate numeric literal" => Some(Some(Approx)),
            "boolean literal" => Some(Some(Bool)),
            "character string literal" => Some(Some(Str)),
            "byte string literal" => Some(Some(Bytes)),
            "null literal" => Some(Some(Null)),
            "date literal" | "SQL-datetime literal" => Some(Some(Date)),
            "time literal" => Some(Some(if text.is_some_and(zoned) {
                ZonedTime
            } else {
                LocalTime
            })),
            "datetime literal" => Some(Some(if text.is_some_and(zoned) {
                ZonedDatetime
            } else {
                LocalDatetime
            })),
            "duration literal" => Some(Some(duration_text(
                text,
                node.items == [Item::Prose("SQL-interval literal")],
            ))),
            "list value constructor" => Some(Some(List)),
            "record constructor" => Some(Some(Record)),
            "path value constructor" => Some(Some(Path)),
            "general value specification" => {
                Some(Some(if token("SESSION_USER") { Str } else { Dynamic }))
            }
            // 20.11 SR 3 b: a property of an element with no closed type is dynamic.
            // A closed record's field has a type, not followed: opaque.
            "property reference" => Some(Some(match at("property source") {
                Some(Node | Edge | Dynamic) => Dynamic,
                _ => Opaque,
            })),
            "value query expression" | "element_id function" => Some(Some(Opaque)),
            // 20.27: the datetime value functions.
            "date function" => Some(Some(Date)),
            "time function" => Some(Some(ZonedTime)),
            "datetime function" => Some(Some(ZonedDatetime)),
            "localtime function" => Some(Some(LocalTime)),
            "localdatetime function" => Some(Some(LocalDatetime)),
            // 20.29: DURATION('...') by its string; of a record, not followed.
            "duration function" => Some(Some(if classed.contains(&Record) {
                Opaque
            } else {
                duration_text(text, false)
            })),
            // 20.22.
            "length expression" | "cardinality expression" => Some(Some(Exact)),
            // 20.22 SR 5: the divisor's type (of a null divisor, the dividend's); a dynamic
            // one is some number.
            "modulus expression" => match (
                at("numeric value expression divisor"),
                at("numeric value expression dividend"),
            ) {
                (Some(Null), Some(Null)) => None,
                (Some(Dynamic), _) | (Some(Null), Some(Dynamic)) => Some(Some(Exact)),
                (Some(Null), d) | (d, _) => Some(d),
            },
            "trigonometric function"
            | "general logarithm function"
            | "common logarithm"
            | "natural logarithm"
            | "exponential function"
            | "power function"
            | "square root" => check(typed, Some(Approx)),
            "character string function" => Some(Some(Str)),
            "byte string function" => Some(Some(Bytes)),
            "list value function" => Some(Some(List)),
            // The categories over an untyped primary (20.21 SR 3, 20.23 SR 2, 4, 20.15 SR 1,
            // 20.13 SR 2, 20.1 SR 4-6, 20.20 SR 3; 20.26, 20.28 statically, a reading).
            "numeric primary" => site(Class::numeric),
            "character string primary" => site(|c| c == Str),
            "byte string primary" => site(|c| c == Bytes),
            "datetime primary" => site(Class::instant),
            "duration primary" => site(Class::duration),
            "list primary" => site(|c| c == List),
            "path value primary" => site(|c| c == Path),
            "boolean predicand" => site(|c| c == Bool),
            // These feed properties and paths, never a bare value: no opaque one.
            "record expression" => check(fits(only, |c| c == Record), only),
            "node reference value expression" => check(fits(only, |c| c == Node), only),
            "edge reference value expression" => check(fits(only, |c| c == Edge), only),
            // No graph or table is ever a variable here; a dynamic value may stand for one.
            // `GRAPH g`, `TABLE {...}`: graphs and tables are not followed.
            "graph reference value expression" | "binding table reference value expression" => {
                let primary = node.items == [Item::Def("value expression primary")];
                if primary {
                    check(only == Some(Dynamic), Some(Dynamic))
                } else {
                    Some(Some(Opaque))
                }
            }
            // 11.1 SR 3, 11.2 SR 4: a value as a graph or a table has that type; only a
            // dynamic one may be.
            "object expression primary" => check(only == Some(Dynamic), Some(Dynamic)),
            // 14.8 SR 10: FOR iterates a list or a binding table.
            "for item source" => check(fits(only, |c| c == List), only),
            // 16.13, 14.6, 20.7: a condition is a boolean.
            "search condition" => check(fits(only, |c| c == Bool), Some(Bool)),
            // A sign, NOT or IS TRUE takes an operand of its category; without one the
            // operand passes as it is.
            "factor" if has(fact::MODIFIED) => check(fits(only, Class::numeric), only),
            "duration factor" if has(fact::MODIFIED) => check(fits(only, Class::duration), only),
            "boolean factor" | "boolean test" if has(fact::MODIFIED) => {
                check(fits(only, |c| c == Bool), Some(Bool))
            }
            "normalized predicate" => check(fits(kids[0], |c| c == Str), Some(Bool)),
            "node reference" => check(only == Some(Node), only),
            "edge reference" => check(only == Some(Edge), only),
            "directed predicate" => check(kids[0] == Some(Edge), Some(Bool)),
            // 20.21: numeric operators.
            "numeric value expression" | "term" if classed.len() == 2 => check(
                classed.iter().all(|c| fits(Some(*c), Class::numeric)),
                Some(arithmetic(&classed)),
            ),
            // 20.23, 20.15, 20.13: concatenation.
            "character string concatenation" => check(typed, Some(Str)),
            "byte string concatenation" => check(typed, Some(Bytes)),
            "list concatenation" => check(typed, Some(List)),
            "path value concatenation" => check(typed, Some(Path)),
            // 20.26 SR 1, read as written: an instant moved by a duration is a zoned datetime if
            // the instant is a zoned datetime, a local datetime otherwise, a zoned time included
            // (Table 1 would keep its class).
            "datetime value expression" if classed.len() == 2 => {
                let instant = at("datetime primary").or(at("datetime value expression"));
                let duration = at("duration value expression").or(at("duration term"));
                let result = match instant {
                    Some(ZonedDatetime) => Some(ZonedDatetime),
                    Some(Dynamic) => instant,
                    _ => Some(LocalDatetime),
                };
                check(
                    fits(instant, Class::instant) && fits(duration, Class::duration),
                    result,
                )
            }
            // 20.28 SR 1 a: durations of one kind add.
            "duration addition and subtraction" => {
                let (a, b) = (at("duration value expression 1"), at("duration term 1"));
                let loose = |c: Option<Class>| matches!(c, Some(Null | Dynamic));
                let ok = fits(a, Class::duration)
                    && fits(b, Class::duration)
                    && (a == b || loose(a) || loose(b));
                // The operator types the result: of a null operand, the other's kind; of two,
                // no kind to give (reading: refused).
                let result = if a == Some(Null) { b } else { a };
                check(ok && result != Some(Null), result)
            }
            "duration term" if classed.len() == 2 => {
                let duration = classed.iter().find(|c| c.duration()).copied();
                let dynamic = classed.contains(&Dynamic).then_some(Dynamic);
                check(
                    typed && duration.or(dynamic).is_some(),
                    duration.or(dynamic),
                )
            }
            // 20.28 SR 3, 4.16.5: DURATION_BETWEEN takes two instants of one class.
            "datetime subtraction" => {
                let (a, b) = (acc.result, acc.when);
                let years = has(fact::YEARS);
                let same = matches!((a, b), (Some(x), Some(y)) if x == y && x.instant());
                let times = matches!(a, Some(LocalTime | ZonedTime));
                check(
                    same && !(times && years),
                    Some(if years { YearMonth } else { DayTime }),
                )
            }
            // 20.20 SR 1: AND, OR, XOR take booleans.
            "boolean value expression" | "boolean term" if classed.len() == 2 => check(
                classed.iter().all(|c| fits(Some(*c), |c| c == Bool)),
                Some(Bool),
            ),
            // 19.x: predicates are booleans.
            "predicate"
            | "exists predicate"
            | "null predicate"
            | "value type predicate"
            | "labeled predicate"
            | "source/destination predicate"
            | "property_exists predicate" => Some(Some(Bool)),
            // 22.13: the operands of an equality are of one kind.
            "all_different predicate" | "same predicate" => {
                let nodes = has(fact::SAW_NODE) || classed.contains(&Node);
                let edges = has(fact::SAW_EDGE) || classed.contains(&Edge);
                check(!(nodes && edges), Some(Bool))
            }
            // 19.3, 22.13, 22.14.
            "comparison predicate" => {
                let ok = matches!((kids[0], kids[1]), (Some(a), Some(b)) if comparable(a, b, has(fact::ORDERING)));
                check(ok, Some(Bool))
            }
            "comparison predicate part 2" => Some(kids[1]),
            // 20.7: CASE, NULLIF, COALESCE take exact numbers and nulls only (reading, to keep
            // labels few): every one of their productions still has typed instances.
            _ if NARROWED.contains(&owner(def))
                && !classed.iter().all(|c| matches!(c, Exact | Null)) =>
            {
                None
            }
            "case abbreviation" if token("NULLIF") => {
                let (a, b) = (kids[2], kids[4]);
                check(
                    matches!((a, b), (Some(x), Some(y)) if comparable(x, y, false)),
                    a,
                )
            }
            "case abbreviation" => {
                let mut all: Vec<Class> = acc.result.into_iter().collect();
                all.extend(classed.iter().copied());
                combine(&all).map(Some)
            }
            // Each when operand was checked against the operand's possible classes.
            "simple case" => {
                let c = only.filter(|c| OPERANDS.contains(c))?;
                let bit = 1 << OPERANDS.iter().position(|o| *o == c)?;
                if acc.operand.is_some_and(|m| m & bit == 0) {
                    return None;
                }
                acc.result.filter(|c| *c != Null).map(Some)
            }
            "searched case" => acc.result.filter(|c| *c != Null).map(Some),
            // 20.8: CAST to a material target the operand converts to (SR 4).
            "cast specification" => {
                if has(fact::IMMATERIAL) {
                    return None;
                }
                let to = if has(fact::ANY_TYPE) {
                    Some(Dynamic)
                } else {
                    acc.target
                };
                // 20.8 SR 5: no null to a type NOT NULL (reading: NOT NULL anywhere in it).
                match (at("cast operand"), to) {
                    (Some(Null), _) if has(fact::NOT_NULL) => None,
                    (Some(from), Some(to)) if castable(from, to) => Some(Some(to)),
                    _ => None,
                }
            }
            // 20.9.
            "aggregate function" if token("COUNT") => Some(Some(Exact)),
            "general set function" => {
                let arg = at("value expression");
                if has(fact::COUNT) {
                    Some(Some(Exact))
                } else if has(fact::COLLECT) {
                    Some(Some(List))
                } else if has(fact::SUM_AVG) {
                    // 20.9 SR 8 d: a number, whatever the argument (a null or a dynamic one
                    // included).
                    let result = match arg {
                        Some(Null | Dynamic) => Some(Exact),
                        _ => arg,
                    };
                    check(fits(arg, Class::numeric), result)
                } else if has(fact::STDDEV) {
                    check(fits(arg, Class::numeric), Some(Approx))
                } else {
                    // MIN, MAX order their argument (22.14).
                    check(
                        matches!(arg, Some(c) if c.scalar() || matches!(c, Null | Dynamic)),
                        arg,
                    )
                }
            }
            "binary set function" => Some(Some(Approx)),
            "let value expression" => Some(at("value expression")),
            "aggregating value expression" | "value initializer" => Some(only),
            // 10.3 SR 8: a typed initializer's value is assignable to the type; the variable
            // has the type, or the value's class.
            "opt typed value initializer" => {
                if has(fact::IMMATERIAL) {
                    return None;
                }
                let value = kids.last().copied().flatten();
                let to = if has(fact::ANY_TYPE) {
                    Some(Dynamic)
                } else {
                    acc.target
                };
                match (to, value) {
                    (Some(to), Some(from))
                        if !assignable(from, to) || from == Null && has(fact::NOT_NULL) =>
                    {
                        None
                    }
                    (Some(to), _) => Some(Some(to)),
                    (None, v) => Some(v),
                }
            }
            "value variable definition" | "let variable definition" => {
                Some(kids.iter().rev().flatten().next().copied())
            }
            // 14.10 SR 4, 22.14: a sort key is ordered.
            "sort key" => {
                let ok = matches!(kids.first().copied().flatten(), Some(c) if c.scalar() || matches!(c, Null | Dynamic));
                check(ok, None)
            }
            "return item" => Some(kids.first().copied().flatten()),
            _ if UNREAD.contains(&owner(def)) => Some(None),
            // A function of a null (ABS(NULL), FLOOR(NULL)) is typed by the function, which
            // passes its argument's type on: refused, having none to give (reading).
            _ if self.expression(def) && call && only == Some(Null) => None,
            _ if self.expression(def) => Some(only),
            _ => Some(None),
        }
    }

    /// What `node` passes up besides its class; false rejects it.
    fn facts(&self, node: &Node, kids: &[Option<Class>], acc: &Label, out: &mut Label) -> bool {
        let def = node.def;
        let own = owner(def);
        let has = |f: u16| acc.has(f);
        let class = out.class.and_then(|t| match t {
            Ty::Is(c) => Some(c),
            Ty::Slot(..) => None,
        });
        let first = kids.iter().flatten().next().copied();
        match def {
            // `<value type>` and what it names, up to a CAST or a typed initializer.
            "boolean type" => out.target = Some(Bool),
            "character string type" => out.target = Some(Str),
            "byte string type" => out.target = Some(Bytes),
            "exact numeric type" => out.target = Some(Exact),
            "approximate numeric type" => out.target = Some(Approx),
            "date type" => out.target = Some(Date),
            "time type" => out.target = Some(ZonedTime),
            "localtime type" => out.target = Some(LocalTime),
            "datetime type" => out.target = Some(ZonedDatetime),
            "localdatetime type" => out.target = Some(LocalDatetime),
            "temporal duration type" => {
                out.target = Some(if has(fact::YEARS) { YearMonth } else { DayTime })
            }
            "path value type" => out.target = Some(Path),
            "list value type" => out.target = Some(List),
            "record type" => out.target = Some(Record),
            "node reference value type" => out.target = Some(Node),
            "edge reference value type" => out.target = Some(Edge),
            "graph reference value type" | "binding table reference value type" => {
                out.target = Some(Opaque)
            }
            "immaterial value type" => out.facts |= fact::IMMATERIAL,
            "dynamic union type" => out.facts |= fact::ANY_TYPE,
            "value type"
            | "predefined type"
            | "numeric type"
            | "temporal type"
            | "temporal instant type"
            | "reference value type"
            | "constructed value type"
            | "cast target" => {
                out.target = acc.target;
                out.facts |= acc.facts & (fact::IMMATERIAL | fact::ANY_TYPE);
            }
            "not null" => out.facts |= fact::NOT_NULL,
            "temporal duration qualifier" => {
                if node.items.first() == Some(&Item::Token("YEAR")) {
                    out.facts |= fact::YEARS;
                }
            }
            "general set function type" => {
                out.facts |= match node.items.first() {
                    Some(Item::Token("SUM" | "AVG")) => fact::SUM_AVG,
                    Some(Item::Token("COUNT")) => fact::COUNT,
                    Some(Item::Token("COLLECT_LIST")) => fact::COLLECT,
                    Some(Item::Token("STDDEV_SAMP" | "STDDEV_POP")) => fact::STDDEV,
                    _ => fact::MIN_MAX,
                };
            }
            _ if node.group
                && matches!(
                    own,
                    "factor" | "duration factor" | "boolean factor" | "boolean test"
                )
                && !node.items.is_empty() =>
            {
                out.facts |= fact::MODIFIED
            }
            "comp op"
                if !matches!(
                    node.items.first(),
                    Some(Item::Def("equals operator" | "not equals operator"))
                ) =>
            {
                out.facts |= fact::ORDERING
            }
            "list element" => out.result = first,
            "result" => {
                if let Some(c) = first {
                    if !matches!(c, Exact | Null) {
                        return false;
                    }
                    out.result = Some(c);
                }
            }
            // 20.7 SR 2: a when operand applies to the operand (as an equality, ordered here,
            // or the predicate it completes): the operand classes it accepts.
            "when operand" => {
                let ok = |operand: Class| match node.items.first() {
                    Some(Item::Def(
                        "non-parenthesized value expression primary"
                        | "comparison predicate part 2",
                    )) => matches!(kids[0], Some(c) if comparable(operand, c, true)),
                    Some(Item::Def("normalized predicate part 2")) => {
                        fits(Some(operand), |c| c == Str)
                    }
                    Some(Item::Def("directed predicate part 2")) => operand == Edge,
                    Some(Item::Def("labeled predicate part 2")) => matches!(operand, Node | Edge),
                    Some(Item::Def("source predicate part 2" | "destination predicate part 2")) => {
                        operand == Node
                    }
                    _ => true,
                };
                let mask = OPERANDS
                    .iter()
                    .enumerate()
                    .filter(|(_, o)| ok(**o))
                    .fold(0u8, |m, (i, _)| m | 1 << i);
                if mask == 0 {
                    return false;
                }
                out.operand = Some(mask);
            }
            "element variable reference" => match class {
                Some(Node) => out.facts |= fact::SAW_NODE,
                Some(Edge) => out.facts |= fact::SAW_EDGE,
                _ => {}
            },
            // 20.28 SR 3: DURATION_BETWEEN reads both only to see one instant class.
            "datetime subtraction parameters" => {
                let (a, b) = (
                    kids.first().copied().flatten(),
                    kids.get(2).copied().flatten(),
                );
                if !matches!((a, b), (Some(x), Some(y)) if x == y && x.instant()) {
                    return false;
                }
                out.result = a;
                out.when = b;
            }
            _ => {}
        }
        if CASE_FAMILY.contains(&own) {
            // One class, folded as results meet, so a CASE's labels do not multiply: results
            // combine (22.18). COALESCE's later arguments are results too (20.7 SR 1 c).
            let mut folded = acc.result;
            if own == "case abbreviation" && node.group {
                for c in kids.iter().flatten() {
                    match merge_results(folded, Some(*c)) {
                        Some(r) => folded = r,
                        None => return false,
                    }
                }
            }
            out.result = folded;
        }
        // The simple CASE operand classes, from the when operands up to the CASE.
        if matches!(
            own,
            "simple case" | "simple when clause" | "when operand list"
        ) {
            out.operand = acc.operand;
        }
        if matches!(own, "all_different predicate" | "same predicate") {
            out.facts |= acc.facts & (fact::SAW_NODE | fact::SAW_EDGE);
        }
        if def == "comparison predicate part 2" {
            out.facts |= acc.facts & fact::ORDERING;
        }
        if own == "general set function" {
            out.facts |= acc.facts & fact::SET_KIND;
        }
        if matches!(own, "datetime subtraction" | "temporal duration type") {
            out.facts |= acc.facts & fact::YEARS;
        }
        if matches!(own, "cast specification" | "opt typed value initializer") {
            out.target = out.target.or(acc.target);
            out.facts |= acc.facts & (fact::IMMATERIAL | fact::ANY_TYPE | fact::NOT_NULL);
        }
        // NOT NULL rises through the type that holds it, up to the CAST or initializer.
        if own.ends_with(" type") || own == "cast target" {
            out.facts |= acc.facts & fact::NOT_NULL;
        }
        // The node a carried fact is for consumes it.
        if matches!(
            def,
            "case abbreviation"
                | "simple case"
                | "searched case"
                | "case specification"
                | "list value constructor by enumeration"
        ) {
            out.result = None;
            out.when = None;
            out.operand = None;
        }
        true
    }

    /// The labels of a finished node: its children's classes, a deferred one passed on
    /// where an opaque one would be, chosen where it would not.
    fn finish_node(&self, node: &Node, acc: &Label, a: &Scoped) -> Vec<Label> {
        let def = node.def;
        let mut kids = acc.kids.clone();
        if !self.reads(def) {
            kids.clear();
        }
        let mut vars = acc.vars.clone();
        // 20.12 SR 8: a reference is its variable's, whatever that is.
        if def == "binding variable reference" {
            return vec![Label {
                class: Some(Ty::Slot(0, ANY)),
                vars,
                ..Label::default()
            }];
        }
        // 20.11: a property's source is a node or an edge.
        if def == "property reference"
            && let Some(Some(Ty::Slot(s, _))) = kids.first()
        {
            let s = *s as usize;
            vars[s] = match meet(vars[s], Need(Req::Element)) {
                Some(e) => e,
                None => return vec![],
            };
            return vec![Label {
                class: Some(Ty::Is(Dynamic)),
                vars,
                ..Label::default()
            }];
        }
        // Each deferred variable, with the classes the sites below still allow it.
        let mut slots: BTreeMap<Slot, u8> = BTreeMap::new();
        for k in &kids {
            if let Some(Ty::Slot(s, m)) = k {
                *slots.entry(*s).or_insert(ANY) &= m;
            }
        }
        let concrete = |pick: &BTreeMap<Slot, Class>| -> Vec<Option<Class>> {
            kids.iter()
                .map(|k| match k {
                    Some(Ty::Is(c)) => Some(*c),
                    Some(Ty::Slot(s, _)) => Some(pick[s]),
                    None => None,
                })
                .collect()
        };
        // Deferred where an opaque value passes; a site that passes it on keeps only the
        // classes it would pass itself.
        if !CHOOSE.contains(&owner(def)) {
            let opaque: BTreeMap<Slot, Class> = slots.keys().map(|s| (*s, Opaque)).collect();
            if let Some(mut out) = self.eval(node, &concrete(&opaque), acc) {
                let one: Vec<(Slot, u8)> = slots.iter().map(|(s, m)| (*s, *m)).collect();
                if let ([(s, m)], Some(Ty::Is(Opaque))) = (&one[..], out.class) {
                    let (s, m) = (*s, *m);
                    let kept = DOMAIN
                        .iter()
                        .enumerate()
                        .filter(|(i, c)| {
                            m & 1 << i != 0
                                && self
                                    .eval(node, &concrete(&BTreeMap::from([(s, **c)])), acc)
                                    .is_some_and(|o| o.class == Some(Ty::Is(**c)))
                        })
                        .fold(0, |m, (i, _)| m | 1 << i);
                    if kept == 0 {
                        return vec![];
                    }
                    out.class = Some(Ty::Slot(s, kept));
                }
                out.vars = vars;
                return vec![out];
            }
            if slots.is_empty() {
                return vec![];
            }
        }
        // Chosen: every class each variable may have, and what that asks of it.
        let mut picks: Vec<(BTreeMap<Slot, Class>, Vec<Entry>)> = vec![(BTreeMap::new(), vars)];
        for (&s, &m) in &slots {
            let mut next = Vec::new();
            for (pick, vars) in &picks {
                let allowed = domain(vars[s as usize], a.view(s as usize))
                    .into_iter()
                    .filter(|(c, _)| {
                        DOMAIN
                            .iter()
                            .position(|d| d == c)
                            .is_some_and(|i| m & 1 << i != 0)
                    });
                for (c, req) in allowed {
                    let Some(e) = meet(vars[s as usize], Need(req)) else {
                        continue;
                    };
                    let mut pick = pick.clone();
                    pick.insert(s, c);
                    let mut vars = vars.clone();
                    vars[s as usize] = e;
                    next.push((pick, vars));
                }
            }
            picks = next;
        }
        picks
            .into_iter()
            .filter_map(|(pick, vars)| {
                let mut out = self.eval(node, &concrete(&pick), acc)?;
                out.vars = vars;
                Some(out)
            })
            .collect()
    }
}

impl Under<Scope> for Types {
    type Label = Label;

    fn name(&self) -> &str {
        "value expressions typed"
    }

    fn empty(&self, _: &Node, a: &Scoped) -> Label {
        Label {
            vars: vec![Free; a.width()],
            ..Label::default()
        }
    }

    fn push(
        &self,
        node: &Node,
        _: usize,
        partial: &Label,
        child: Option<&Label>,
        a: Step<'_, Scoped>,
    ) -> Vec<Label> {
        let width = a.out.width();
        let mut inputs = partial.vars.clone();
        let mut views = views(a.partial);
        if let Some(c) = child {
            inputs.extend_from_slice(&c.vars);
        }
        if let Some(c) = a.child {
            views.extend(self::views(c));
        }
        let Some(r) = Relinked::new(&inputs, &views, a.link, width) else {
            return vec![];
        };
        let mut out = Label {
            class: None,
            vars: r.vars.clone(),
            facts: partial.facts,
            target: partial.target,
            result: partial.result,
            when: partial.when,
            operand: partial.operand,
            kids: partial.kids.iter().map(|k| r.ty(0, *k)).collect(),
        };
        if let Some(c) = child {
            out.facts |= c.facts;
            out.target = out.target.or(c.target);
            match merge_results(out.result, c.result) {
                Some(res) => out.result = res,
                None => return vec![],
            }
            out.when = out.when.or(c.when);
            out.operand = match (out.operand, c.operand) {
                (Some(x), Some(y)) => Some(x & y),
                (x, y) => x.or(y),
            };
        }
        let class = child.and_then(|c| r.ty(partial.vars.len(), c.class));
        out.kids
            .push(if self.reads(node.def) { class } else { None });
        if !reconcile(&mut out.vars, a.out) {
            return vec![];
        }
        vec![out]
    }

    fn finish(&self, node: &Node, partial: &Label, a: Step<'_, Scoped>) -> Vec<Label> {
        let width = a.out.width();
        let Some(r) = Relinked::new(&partial.vars, &views(a.partial), a.link, width) else {
            return vec![];
        };
        let acc = Label {
            vars: r.vars.clone(),
            kids: partial.kids.iter().map(|k| r.ty(0, *k)).collect(),
            ..partial.clone()
        };
        let def = node.def;
        let mut out = self.finish_node(node, &acc, a.out);
        for l in &mut out {
            // 10.3: a new value variable has its definition's class.
            if matches!(def, "let variable definition" | "value variable definition") {
                let c = match l.class {
                    Some(Ty::Is(c)) => follow(c),
                    _ => Opaque,
                };
                for (s, e) in l.vars.iter_mut().enumerate() {
                    if a.out.view(s).new && *e == Free {
                        *e = Has(c);
                    }
                }
            }
            // 14.8 SR 13: an ordinality or offset is a number.
            if def == "for ordinality or offset" {
                for (s, e) in l.vars.iter_mut().enumerate() {
                    if a.out.view(s).new && *e == Free {
                        *e = Has(Exact);
                    }
                }
            }
            // A return item's alias is a column of its expression's class.
            if def == "return item" {
                let c = match l.class {
                    Some(Ty::Is(c)) => follow(c),
                    _ => Opaque,
                };
                for s in 0..a.partial.width() {
                    if a.partial.view(s).aliased
                        && let Ok(o) = r.at[s]
                        && a.out.view(o as usize).column == Some(Kind::Value)
                        && l.vars[o as usize] == Free
                    {
                        l.vars[o as usize] = Has(c);
                    }
                }
            }
            if !self.reads(def) || CONSUMERS.contains(&owner(def)) {
                l.class = None;
            }
        }
        out.retain_mut(|l| reconcile(&mut l.vars, a.out));
        out
    }

    fn top(&self, _: &Scoped, _: &Label) -> bool {
        true
    }

    fn show(&self, l: &Label) -> String {
        let mut s = match l.class {
            Some(Ty::Is(c)) => format!("{c:?}").to_lowercase(),
            Some(Ty::Slot(v, m)) => format!("@{v}/{m:b}"),
            None => String::new(),
        };
        for (i, e) in l.vars.iter().enumerate() {
            match e {
                Free => {}
                Need(r) => s.push_str(&format!(" {i}?{r:?}").to_lowercase()),
                Has(c) => s.push_str(&format!(" {i}:{c:?}").to_lowercase()),
            }
        }
        s
    }

    fn project(
        &self,
        a: &Scoped,
        moved: Option<&Link>,
        l: &Label,
        _: super::Masks,
    ) -> Option<Label> {
        let Some(link) = moved else {
            return Some(l.clone());
        };
        let r = Relinked::new(&l.vars, &[], link, a.width())?;
        Some(Label {
            class: r.ty(0, l.class),
            vars: r.vars.clone(),
            kids: l.kids.iter().map(|k| r.ty(0, *k)).collect(),
            ..l.clone()
        })
    }
}
