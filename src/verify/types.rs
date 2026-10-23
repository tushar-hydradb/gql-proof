//! Static typing of value expressions in ISO/IEC 39075 (2024 + Cor 1), checked on a `Plain`
//! tree straight from the Syntax Rules, independently of the automaton in `src/types.rs`.
//!
//! Every expression gets a declared type from its own operator and its operands, never from the
//! category a parse put it in: the grammar derives a bare primary, `(e)`, `f(..)`, CASE and CAST
//! as every typed category (a <numeric primary> and a <character string primary> alike), so a
//! rule like 20.21 SR 3 ("a numeric primary shall be numeric") would hold on one tree of a
//! sentence and fail on another. A category constrains its operand only where an operator or a
//! function of that category is present, and then an operator accepts what any of its derivations
//! accepts: `a + b` is 20.21, Table 1 (4.16.6.4) or 20.28 by the operand types. Slots with one
//! derivation (a <search condition>, CHAR_LENGTH's argument) check their category directly.
//!
//! Variables carry the types they are bound to through the statements (16.3, 14.7, 14.8, 14.10,
//! 9.2, 15.1); a name nothing binds has the unknown type and scoping is `scope`'s concern. The
//! verdict is the same on every tree of a sentence whose names are in scope (`TABLE / a` also
//! derives as a division of two unbound variables), save one: `--` read as two minus signs needs
//! a separator between them (20.21 SR 4), which a `Plain` tree does not record.
//!
//! Readings where the text leaves room:
//! - the conformance claim is the minimal one: no GA04 (universal comparison, so comparison
//!   operands are comparable value types, 22.13-22.14 CR 1) and no GV65 (dynamic union types, so
//!   CASE, COALESCE, list constructors and list concatenation combine statically, 22.19)
//! - the null type (4.16.8) is a subtype of every nullable type, so it meets every "shall be"
//!   requirement on an operand; nullability is not otherwise inferred (4.17.4), only NULL itself
//!   is kept out of NOT NULL sites (10.3 SR 8, 20.8 SR 5)
//! - an operand of an unknown, open or dynamic type meets every requirement: 4.14.4 lets the
//!   implementation cure it with type tests at run time
//! - a property of a node or edge has the dynamic property value type: with no catalog every
//!   graph element type is open (20.11 SR 3 b, 20.12 SR 13 a, IW011)
//! - a datetime or duration operand that is no temporal instant or duration breaks 20.26 GR 1
//!   and Table 1 at every evaluation, so it is rejected statically; DURATION_BETWEEN's operands
//!   alike (20.28 SR 3 b already asks them to be essentially comparable)
//! - datetime ± duration has the zoned or local datetime type, as 20.26 SR 1 says, even when the
//!   instant is a date or a time
//! - a <result> that is just NULL specifies no <result expression> on any tree (20.7 SR 3)
//! - inside an aggregate function a group variable stands for one of its elements, as `scope`
//!   reads 20.1 SR 7 and 20.9; inside an element pattern WHERE clause, a parenthesized path
//!   pattern WHERE clause or a property specification of the pattern that declares it, a graph
//!   pattern variable is a single node or edge (20.12 SR 11 a ii)
//! - a <normalized predicate> takes a character or a byte string as its grammar says (20.23)
//! - 21.2 SR 73 is a condition on the <list literal> derivation, which a <list value constructor>
//!   derivation of the same text always escapes, so it is no violation
//! - texts with a second derivation that always types are read that way: `9.M`, `9.F`, `9.E+3`
//!   are numeric literals, not properties of 9 (20.1 SR 4-6 rules those out); `"g"` and `a.b` in
//!   a graph or binding table expression are catalog references, not values (11.1, 11.2)
//!
//! Unmodelled, typed unknown and checked for nothing about themselves:
//! - dynamic parameters (`$x`): their types come from the request (20.4 SR 2, 22.1)
//! - catalog-modifying statements, session commands, a <select statement> with a body, and the
//!   result of a named procedure call
//! - ELEMENT_ID (ID076), ELEMENTS' element type (ID005), the element type of an empty list
//!   (ID004), and closed graph, node and edge types, which only a catalog could interpret
//! - a <value type> with a union of several components in it: `INT | STRING LIST` derives as a
//!   union with a list and as a list of a union
//! - lengths, precisions and maximum cardinalities of string, number and list types
//! - grouping operations (22.15) and sort keys, whose operands are compared with themselves

use super::{Plain, Violation};
use std::collections::{BTreeMap, HashMap};
use std::fmt;

/// Declared types, cut down to what the Syntax Rules distinguish.
#[derive(Debug, Clone, PartialEq)]
enum Ty {
    /// Unknown, open or dynamic.
    Any,
    /// The null type.
    Null,
    /// The empty type.
    Nothing,
    Bool,
    /// Exact numeric; `int` when the scale is 0.
    Exact {
        int: bool,
    },
    Approx,
    /// Numeric, exact or approximate as the implementation decides.
    Number,
    Char,
    Bytes,
    Date,
    LocalTime,
    ZonedTime,
    LocalDatetime,
    ZonedDatetime,
    /// A duration of one unit group, or of either.
    Duration(Option<Unit>),
    List {
        elem: Box<Ty>,
        group: bool,
    },
    /// A record type, closed with these field types or open.
    Record(Option<Fields>),
    Path,
    Node,
    Edge,
    Graph,
    Table,
}

/// Temporal duration unit groups (4.16.6.3).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Unit {
    YearMonth,
    DayTime,
}

type Fields = BTreeMap<String, Ty>;

/// The categories the Syntax Rules require of operands.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Class {
    Bool,
    Numeric,
    Char,
    Bytes,
    Instant,
    Duration,
    List,
    Record,
    Path,
    Node,
    Edge,
    Graph,
    Table,
}

impl Ty {
    fn class(&self) -> Option<Class> {
        Some(match self {
            Ty::Any | Ty::Null | Ty::Nothing => return None,
            Ty::Bool => Class::Bool,
            Ty::Exact { .. } | Ty::Approx | Ty::Number => Class::Numeric,
            Ty::Char => Class::Char,
            Ty::Bytes => Class::Bytes,
            Ty::Date | Ty::LocalTime | Ty::ZonedTime | Ty::LocalDatetime | Ty::ZonedDatetime => {
                Class::Instant
            }
            Ty::Duration(_) => Class::Duration,
            Ty::List { .. } => Class::List,
            Ty::Record(_) => Class::Record,
            Ty::Path => Class::Path,
            Ty::Node => Class::Node,
            Ty::Edge => Class::Edge,
            Ty::Graph => Class::Graph,
            Ty::Table => Class::Table,
        })
    }

    /// A type that meets any requirement: unknown, or immaterial (4.16.8).
    fn wild(&self) -> bool {
        self.class().is_none()
    }

    fn is(&self, classes: &[Class]) -> bool {
        self.class().is_none_or(|c| classes.contains(&c))
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Ty::Any => write!(f, "ANY"),
            Ty::Null => write!(f, "NULL"),
            Ty::Nothing => write!(f, "NOTHING"),
            Ty::Bool => write!(f, "BOOLEAN"),
            Ty::Exact { int: true } => write!(f, "INTEGER"),
            Ty::Exact { int: false } => write!(f, "DECIMAL"),
            Ty::Approx => write!(f, "FLOAT"),
            Ty::Number => write!(f, "numeric"),
            Ty::Char => write!(f, "STRING"),
            Ty::Bytes => write!(f, "BYTES"),
            Ty::Date => write!(f, "DATE"),
            Ty::LocalTime => write!(f, "LOCAL TIME"),
            Ty::ZonedTime => write!(f, "ZONED TIME"),
            Ty::LocalDatetime => write!(f, "LOCAL DATETIME"),
            Ty::ZonedDatetime => write!(f, "ZONED DATETIME"),
            Ty::Duration(None) => write!(f, "DURATION"),
            Ty::Duration(Some(Unit::YearMonth)) => write!(f, "DURATION(YEAR TO MONTH)"),
            Ty::Duration(Some(Unit::DayTime)) => write!(f, "DURATION(DAY TO SECOND)"),
            Ty::List { elem, group } => {
                write!(f, "{}LIST<{elem}>", if *group { "GROUP " } else { "" })
            }
            Ty::Record(None) => write!(f, "ANY RECORD"),
            Ty::Record(Some(fields)) => {
                let fields: Vec<String> = fields.iter().map(|(n, t)| format!("{n} {t}")).collect();
                write!(f, "RECORD {{{}}}", fields.join(", "))
            }
            Ty::Path => write!(f, "PATH"),
            Ty::Node => write!(f, "NODE"),
            Ty::Edge => write!(f, "EDGE"),
            Ty::Graph => write!(f, "GRAPH"),
            Ty::Table => write!(f, "BINDING TABLE"),
        }
    }
}

/// A <value type> as a site's declared type.
#[derive(Debug, Clone)]
struct Declared {
    ty: Ty,
    nullable: bool,
}

impl fmt::Display for Declared {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.nullable {
            true => write!(f, "{}", self.ty),
            false => write!(f, "{} NOT NULL", self.ty),
        }
    }
}

/// Comparable value types (3.9.7) without GA04: their values are essentially comparable (4.4.2).
fn comparable(a: &Ty, b: &Ty) -> bool {
    if a.wild() || b.wild() {
        return true;
    }
    match (a, b) {
        // 4.15.3
        (Ty::List { elem: x, .. }, Ty::List { elem: y, .. }) => comparable(x, y),
        // 4.15.4: field-name equal, fields comparable
        (Ty::Record(Some(x)), Ty::Record(Some(y))) => {
            x.keys().eq(y.keys()) && x.iter().all(|(n, t)| comparable(t, &y[n]))
        }
        // 4.16.6.3: one unit group
        (Ty::Duration(Some(x)), Ty::Duration(Some(y))) => x == y,
        // 4.16.6.2: of the same most specific static value type
        _ if a.class() == Some(Class::Instant) => a == b,
        _ => a.class() == b.class(),
    }
}

/// 22.19 without GV65 (22.18 SR 2): the static combination of `types`, if there is one.
fn combine(types: &[Ty]) -> Option<Ty> {
    let material: Vec<&Ty> = types
        .iter()
        .filter(|t| !matches!(t, Ty::Null | Ty::Nothing))
        .collect();
    let Some(&first) = material.first() else {
        // SR 4 a
        return Some(Ty::Null);
    };
    if material.contains(&&Ty::Any) {
        return Some(Ty::Any);
    }
    let all = |c: Class| material.iter().all(|t| t.class() == Some(c));
    let any = |t: &Ty| material.contains(&t);
    let class = first.class()?;
    match class {
        // SR 4 d
        Class::Numeric if all(class) => Some(if any(&Ty::Approx) {
            Ty::Approx
        } else if any(&Ty::Number) {
            Ty::Number
        } else {
            Ty::Exact {
                int: material.iter().all(|t| **t == Ty::Exact { int: true }),
            }
        }),
        // SR 4 e-g
        Class::Instant => {
            let datetime = |t: &&Ty| matches!(t, Ty::LocalDatetime | Ty::ZonedDatetime);
            let time = |t: &&Ty| matches!(t, Ty::LocalTime | Ty::ZonedTime);
            if material.iter().all(datetime) {
                Some(if any(&Ty::ZonedDatetime) {
                    Ty::ZonedDatetime
                } else {
                    Ty::LocalDatetime
                })
            } else if material.iter().all(time) {
                Some(if any(&Ty::ZonedTime) {
                    Ty::ZonedTime
                } else {
                    Ty::LocalTime
                })
            } else {
                material.iter().all(|t| **t == Ty::Date).then_some(Ty::Date)
            }
        }
        // SR 4 h-i
        Class::Duration if all(class) => {
            let mut unit = None;
            for t in &material {
                if let Ty::Duration(Some(u)) = t {
                    if unit.is_some_and(|x| x != *u) {
                        return None;
                    }
                    unit = Some(*u);
                }
            }
            Some(Ty::Duration(unit))
        }
        // SR 4 k
        Class::List if all(class) => {
            let mut elems = Vec::new();
            let mut group = true;
            for t in &material {
                if let Ty::List { elem, group: g } = t {
                    elems.push((**elem).clone());
                    group &= g;
                }
            }
            Some(Ty::List {
                elem: Box::new(combine(&elems)?),
                group,
            })
        }
        // SR 4 m: closed record types with identical sets of field names
        Class::Record => {
            let mut closed = Vec::new();
            for t in &material {
                match t {
                    Ty::Record(Some(fields)) => closed.push(fields),
                    _ => return None,
                }
            }
            if closed.iter().any(|f| f.keys().ne(closed[0].keys())) {
                return None;
            }
            let mut out = Fields::new();
            for n in closed[0].keys() {
                let types: Vec<Ty> = closed.iter().map(|f| f[n].clone()).collect();
                out.insert(n.clone(), combine(&types)?);
            }
            Some(Ty::Record(Some(out)))
        }
        // SR 4 b, c, j, l, n
        _ => all(class).then(|| first.clone()),
    }
}

/// Assignability of a value of `src` to a site of `tgt` (3.9.6, 4.14-4.16, 4.17.3).
fn assignable(src: &Ty, tgt: &Declared) -> bool {
    match (src, &tgt.ty) {
        (Ty::Any | Ty::Nothing, _) | (_, Ty::Any) => true,
        // 4.16.8: the null value only goes to a nullable site
        (Ty::Null, _) => tgt.nullable,
        (_, Ty::Null | Ty::Nothing) => false,
        // 4.15.3
        (
            Ty::List { elem, group },
            Ty::List {
                elem: te,
                group: tg,
            },
        ) => {
            (!group || *tg)
                && assignable(
                    elem,
                    &Declared {
                        ty: (**te).clone(),
                        nullable: true,
                    },
                )
        }
        // 4.15.4
        (Ty::Record(_), Ty::Record(None)) => true,
        (Ty::Record(Some(s)), Ty::Record(Some(t))) => {
            s.keys().eq(t.keys())
                && s.iter().all(|(n, st)| {
                    assignable(
                        st,
                        &Declared {
                            ty: t[n].clone(),
                            nullable: true,
                        },
                    )
                })
        }
        (Ty::Record(None), Ty::Record(Some(_))) => false,
        // 4.16.6.2: a datetime to either datetime type, a time to either time type
        (Ty::LocalDatetime | Ty::ZonedDatetime, t) => {
            matches!(t, Ty::LocalDatetime | Ty::ZonedDatetime)
        }
        (Ty::LocalTime | Ty::ZonedTime, t) => matches!(t, Ty::LocalTime | Ty::ZonedTime),
        // 4.16.6.3
        (Ty::Duration(a), Ty::Duration(b)) => a.is_none() || b.is_none() || a == b,
        (s, t) if s.class() == Some(Class::Instant) => s == t,
        // 4.16.5: a number to any numeric site
        (s, t) => s.class() == t.class(),
    }
}

/// The class a type has in Table 4 (20.8).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CastClass {
    Numeric,
    C,
    D,
    T,
    Dt,
    Du,
    Bo,
    B,
    L,
    R,
    P,
    Dy,
    Gr,
    Nr,
    Er,
    Tr,
}

fn cast_class(t: &Ty) -> CastClass {
    match t {
        Ty::Any | Ty::Null | Ty::Nothing => CastClass::Dy,
        Ty::Bool => CastClass::Bo,
        Ty::Exact { .. } | Ty::Approx | Ty::Number => CastClass::Numeric,
        Ty::Char => CastClass::C,
        Ty::Bytes => CastClass::B,
        Ty::Date => CastClass::D,
        Ty::LocalTime | Ty::ZonedTime => CastClass::T,
        Ty::LocalDatetime | Ty::ZonedDatetime => CastClass::Dt,
        Ty::Duration(_) => CastClass::Du,
        Ty::List { .. } => CastClass::L,
        Ty::Record(_) => CastClass::R,
        Ty::Path => CastClass::P,
        Ty::Graph => CastClass::Gr,
        Ty::Node => CastClass::Nr,
        Ty::Edge => CastClass::Er,
        Ty::Table => CastClass::Tr,
    }
}

/// 20.8 SR 8-12: Table 4, with the "M" entries resolved by SR 9-12.
fn castable(sd: &Ty, td: &Ty) -> bool {
    use CastClass::*;
    let (s, t) = (cast_class(sd), cast_class(td));
    if s == Dy || t == Dy {
        // SR 9 (the open dynamic union type includes every type), SR 10 (left to run time)
        return true;
    }
    match s {
        Numeric => matches!(t, Numeric | C),
        C => matches!(t, Numeric | C | D | T | Dt | Du | Bo),
        D => matches!(t, C | D | Dt),
        T => matches!(t, C | T | Dt),
        Dt => matches!(t, C | D | T | Dt),
        Du => matches!(t, C | Du),
        Bo => matches!(t, C | Bo),
        B => t == B,
        L => match (sd, td) {
            (_, Ty::Path) => true,
            // SR 11
            (
                Ty::List { elem, group },
                Ty::List {
                    elem: te,
                    group: tg,
                },
            ) => (*group || !tg) && castable(elem, te),
            _ => false,
        },
        R => match (sd, td) {
            // SR 12
            (Ty::Record(Some(s)), Ty::Record(Some(t))) => t
                .iter()
                .all(|(n, tt)| s.get(n).is_some_and(|st| castable(st, tt))),
            _ => t == R,
        },
        P => t == P,
        Gr => t == Gr,
        Nr => matches!(t, P | Nr),
        Er => matches!(t, P | Er),
        Tr => matches!(t, P | Tr),
        Dy => true,
    }
}

/// What an expression sees.
#[derive(Debug, Clone, Default)]
struct Env {
    vars: Fields,
    /// Inside the argument of an aggregate function, where a group variable is one element.
    agg: bool,
}

impl Env {
    fn new(vars: Fields) -> Env {
        Env { vars, agg: false }
    }
}

#[derive(Debug, Clone, Default)]
struct Scope {
    record: Fields,
    table: Fields,
}

impl Scope {
    /// The record amended with the table, what an expression sees (16.13 SR 2, 14.8 SR 7).
    fn merged(&self) -> Fields {
        let mut all = self.record.clone();
        all.extend(self.table.clone());
        all
    }
}

const ELEMENT: &[Class] = &[Class::Node, Class::Edge];

/// Every static typing violation in a tree (2024 + Cor 1).
pub fn check(tree: &Plain) -> Vec<Violation> {
    let mut checker = Checker {
        parent: HashMap::new(),
        out: Vec::new(),
    };
    checker.parents(tree);
    checker.root(tree);
    checker.out
}

struct Checker<'t> {
    parent: HashMap<*const Plain, &'t Plain>,
    out: Vec<Violation>,
}

impl<'t> Checker<'t> {
    fn parents(&mut self, node: &'t Plain) {
        if let Plain::Def { children, .. } = node {
            for c in children {
                self.parent.insert(c, node);
                self.parents(c);
            }
        }
    }

    fn report(&mut self, at: &Plain, rule: &'static str, detail: String) {
        let mut names = Vec::new();
        let mut node = Some(at);
        while let Some(n) = node {
            if let Plain::Def {
                name,
                synthetic: false,
                ..
            } = n
            {
                names.push(format!("<{name}>"));
            }
            node = self.parent.get(&(n as *const Plain)).copied();
        }
        names.truncate(4);
        names.reverse();
        self.out.push(Violation {
            path: names.join(" > "),
            rule,
            detail,
        });
    }

    /// Report unless `t` is one of `classes`.
    fn expect(&mut self, at: &Plain, t: &Ty, classes: &[Class], rule: &'static str) {
        if !t.is(classes) {
            let want: Vec<String> = classes.iter().map(|c| format!("{c:?}")).collect();
            self.report(
                at,
                rule,
                format!("{} has type {t}, not {}", at.text(), want.join(" or ")),
            );
        }
    }

    fn root(&mut self, node: &'t Plain) {
        match name(node) {
            Some("procedure body") => {
                self.body(node, Scope::default());
            }
            Some(n) if n.starts_with("session") => {}
            _ => kids(node).into_iter().for_each(|k| self.root(k)),
        }
    }

    // --- statements ---------------------------------------------------------------------

    /// 9.2: the columns of the result of a procedure body, when known.
    fn body(&mut self, pb: &'t Plain, scope: Scope) -> Option<Fields> {
        let mut record = scope.record;
        if let Some(block) = own(pb, "binding variable definition block") {
            for def in owns(block, "binding variable definition") {
                let Some(def) = kids(def).into_iter().next() else {
                    continue;
                };
                // SR 2: each definition sees the record so far and a unit table.
                let env = Env::new(record.clone());
                let bound = match name(def) {
                    Some("graph variable definition") => {
                        self.walk(def, &env);
                        own(def, "binding variable").map(|bv| (bv.text(), Ty::Graph))
                    }
                    Some("binding table variable definition") => {
                        self.walk(def, &env);
                        own(def, "binding variable").map(|bv| (bv.text(), Ty::Table))
                    }
                    _ => self.value_definition(def, &env),
                };
                if let Some((n, t)) = bound {
                    record.insert(n, t);
                }
            }
        }
        let block = own(pb, "statement block")?;
        self.block(
            block,
            Scope {
                record,
                table: scope.table,
            },
        )
    }

    /// 9.2 SR 8-13: a statement and its NEXT statements.
    fn block(&mut self, sb: &'t Plain, scope: Scope) -> Option<Fields> {
        let mut result = self.statement(own(sb, "statement")?, scope.clone());
        for next in owns(sb, "next statement") {
            let mut table = result.unwrap_or_default();
            if let Some(yc) = own(next, "yield clause") {
                table = yield_columns(yc, &table);
            }
            result = own(next, "statement").and_then(|st| {
                self.statement(
                    st,
                    Scope {
                        record: scope.record.clone(),
                        table,
                    },
                )
            });
        }
        result
    }

    fn statement(&mut self, st: &'t Plain, scope: Scope) -> Option<Fields> {
        let inner = kids(st).into_iter().next()?;
        match name(inner)? {
            "composite query statement" => {
                self.composite(own(inner, "composite query expression")?, scope)
            }
            "linear data-modifying statement" => self.linear(inner, scope),
            // unmodelled, but its expressions are typed as the others' (a CALL derives as a
            // catalog-modifying statement too)
            _ => {
                self.walk(inner, &Env::new(scope.merged()));
                None
            }
        }
    }

    /// 14.2: every operand sees the same scope; the result is read off the first.
    fn composite(&mut self, cqe: &'t Plain, scope: Scope) -> Option<Fields> {
        let mut operands = Vec::new();
        conjuncts(cqe, &mut operands);
        let mut first = None;
        for (i, op) in operands.into_iter().enumerate() {
            let result = self.linear(op, scope.clone());
            if i == 0 {
                first = result;
            }
        }
        first
    }

    /// 14.3 and 13.1: the statements of a linear statement, left to right.
    fn linear(&mut self, node: &'t Plain, mut scope: Scope) -> Option<Fields> {
        let mut parts = Vec::new();
        steps(node, &mut parts);
        let mut result = None;
        for step in parts {
            result = None;
            match name(step) {
                Some("use graph clause") => self.walk(step, &Env::new(scope.record.clone())),
                Some("primitive result statement") => result = self.result(step, &scope),
                Some("nested query specification")
                | Some("nested data-modifying procedure specification") => {
                    result =
                        first(step, "procedure body").and_then(|pb| self.body(pb, scope.clone()));
                }
                Some("select statement") => result = self.select(step, &scope),
                _ => scope = self.simple(step, scope),
            }
        }
        result
    }

    fn simple(&mut self, step: &'t Plain, scope: Scope) -> Scope {
        let node = unwrap(step);
        match name(node) {
            Some("match statement") => self.match_statement(node, scope),
            Some("let statement") => self.let_statement(node, scope),
            Some("for statement") => self.for_statement(node, scope),
            Some("call procedure statement") => self.call(node, scope),
            Some("insert statement") => self.insert(node, scope),
            // 14.6, 14.9, 13.3-13.5: the scope passes through
            _ => {
                self.walk(node, &Env::new(scope.merged()));
                scope
            }
        }
    }

    /// 14.4.
    fn match_statement(&mut self, ms: &'t Plain, scope: Scope) -> Scope {
        let Some(inner) = kids(ms).into_iter().next() else {
            return scope;
        };
        match name(inner) {
            Some("simple match statement") => self.simple_match(inner, scope),
            Some("optional match statement") => {
                let Some(operand) = own(inner, "optional operand") else {
                    return scope;
                };
                // SR 4: the operand sees every incoming name and adds its new ones.
                let mut body = Scope {
                    record: scope.merged(),
                    table: Fields::new(),
                };
                match own(operand, "match statement block") {
                    Some(block) => {
                        for m in owns(block, "match statement") {
                            body = self.match_statement(m, body);
                        }
                    }
                    None => {
                        if let Some(sms) = own(operand, "simple match statement") {
                            body = self.simple_match(sms, body);
                        }
                    }
                }
                let mut scope = scope;
                scope.table.extend(body.table);
                scope
            }
            _ => scope,
        }
    }

    fn simple_match(&mut self, sms: &'t Plain, mut scope: Scope) -> Scope {
        let Some(gpbt) = own(sms, "graph pattern binding table") else {
            return scope;
        };
        let Some(gp) = own(gpbt, "graph pattern") else {
            return scope;
        };
        let incoming = scope.merged();
        let vars = self.graph_pattern(gp, &incoming);
        let yielded: Vec<String> = match own(gpbt, "graph pattern yield clause") {
            Some(yc) => {
                let mut refs = Vec::new();
                find(yc, "binding variable reference", &mut refs);
                refs.into_iter().map(Plain::text).collect()
            }
            None => vars.keys().cloned().collect(),
        };
        for n in yielded {
            if let Some(t) = vars.get(&n)
                && !incoming.contains_key(&n)
            {
                scope.table.insert(n, t.clone());
            }
        }
        scope
    }

    /// 16.3, 16.4: the variables a graph pattern declares, as its WHERE clause sees them, after
    /// checking the expressions in it.
    fn graph_pattern(&mut self, gp: &'t Plain, incoming: &Fields) -> Fields {
        let mut vars = Fields::new();
        pattern_vars(gp, None, false, &mut vars);
        // reading: inside the pattern a variable is one node or edge (20.12 SR 11 a ii)
        let mut single = incoming.clone();
        for (n, t) in &vars {
            single.insert(n.clone(), element_of(t));
        }
        let inner = Env::new(single);
        if let Some(list) = own(gp, "path pattern list") {
            self.walk(list, &inner);
        }
        let mut outer = incoming.clone();
        outer.extend(vars.clone());
        if let Some(wc) = own(gp, "graph pattern where clause") {
            self.walk(wc, &Env::new(outer));
        }
        vars
    }

    /// 14.7 as Cor 1 rewrites it: each definition sees the LET's incoming names only.
    fn let_statement(&mut self, ls: &'t Plain, mut scope: Scope) -> Scope {
        let env = Env::new(scope.merged());
        let defs = own(ls, "let variable definition list")
            .map(|l| owns(l, "let variable definition"))
            .unwrap_or_default();
        for def in defs {
            if let Some((n, t)) = self.value_definition(def, &env) {
                scope.table.insert(n, t);
            }
        }
        scope
    }

    /// 10.3 (and the LET shorthand, 14.7 SR 3): the variable and its declared type.
    fn value_definition(&mut self, def: &'t Plain, env: &Env) -> Option<(String, Ty)> {
        if let Some(inner) = own(def, "value variable definition") {
            return self.value_definition(inner, env);
        }
        let n = own(def, "binding variable")?.text();
        if let Some(ve) = own(def, "value expression") {
            return Some((n, self.ty(ve, env)));
        }
        let otvi = own(def, "opt typed value initializer")?;
        let ve = own(otvi, "value initializer").and_then(|vi| own(vi, "value expression"))?;
        let vit = self.ty(ve, env);
        let Some(vt) = own(otvi, "value type") else {
            return Some((n, vit));
        };
        let declared = value_type(vt);
        // SR 8 b i 1
        if !assignable(&vit, &declared) {
            self.report(
                def,
                "10.3 SR 8",
                format!("{vit} is not assignable to {declared}"),
            );
        }
        Some((n, declared.ty))
    }

    /// 14.8.
    fn for_statement(&mut self, fs: &'t Plain, mut scope: Scope) -> Scope {
        let env = Env::new(scope.merged());
        let Some(item) = own(fs, "for item") else {
            return scope;
        };
        let element = match own(item, "for item source") {
            Some(source) => {
                let t = self.ty(source, &env);
                // 20.15 SR 1 on the list derivation, 20.1 SR 3 on the table derivation
                self.expect(
                    source,
                    &t,
                    &[Class::List, Class::Table],
                    "20.15 SR 1, 20.1 SR 3",
                );
                // SR 10 a
                match t {
                    Ty::List { elem, .. } => *elem,
                    Ty::Table => Ty::Record(None),
                    _ => Ty::Any,
                }
            }
            None => Ty::Any,
        };
        if let Some(bv) = own(item, "for item alias").and_then(|a| own(a, "binding variable")) {
            scope.table.insert(bv.text(), element);
        }
        if let Some(bv) =
            own(fs, "for ordinality or offset").and_then(|f| own(f, "binding variable"))
        {
            // SR 10 c i 3 (ID057, ID058)
            scope.table.insert(bv.text(), Ty::Exact { int: true });
        }
        scope
    }

    /// 15.1-15.3.
    fn call(&mut self, cps: &'t Plain, mut scope: Scope) -> Scope {
        let Some(pc) = own(cps, "procedure call").and_then(|p| kids(p).into_iter().next()) else {
            return scope;
        };
        let incoming = scope.merged();
        let result = match name(pc) {
            Some("inline procedure call") => {
                let record = match own(pc, "variable scope clause") {
                    Some(vsc) => {
                        let mut refs = Vec::new();
                        find(vsc, "binding variable reference", &mut refs);
                        refs.iter()
                            .filter_map(|r| incoming.get(&r.text()).map(|t| (r.text(), t.clone())))
                            .collect()
                    }
                    None => incoming.clone(),
                };
                first(pc, "procedure body").and_then(|pb| {
                    self.body(
                        pb,
                        Scope {
                            record,
                            table: Fields::new(),
                        },
                    )
                })
            }
            Some("named procedure call") => {
                if let Some(args) = own(pc, "procedure argument list") {
                    self.walk(args, &Env::new(incoming.clone()));
                }
                // unmodelled: the catalog knows the result's column types
                own(pc, "yield clause").map(|yc| yield_columns(yc, &Fields::new()))
            }
            _ => None,
        };
        for (n, t) in result.unwrap_or_default() {
            if !incoming.contains_key(&n) {
                scope.table.insert(n, t);
            }
        }
        scope
    }

    /// 13.2: an insert pattern binds its new element variables.
    fn insert(&mut self, is: &'t Plain, mut scope: Scope) -> Scope {
        let incoming = scope.merged();
        self.walk(is, &Env::new(incoming.clone()));
        let mut patterns = Vec::new();
        find_any(
            is,
            &["insert node pattern", "insert edge pattern"],
            &mut patterns,
        );
        for p in patterns {
            let Some(bv) =
                first(p, "element variable declaration").and_then(|d| first(d, "binding variable"))
            else {
                continue;
            };
            let t = match name(p) {
                Some("insert edge pattern") => Ty::Edge,
                _ => Ty::Node,
            };
            if !incoming.contains_key(&bv.text()) {
                scope.table.insert(bv.text(), t);
            }
        }
        scope
    }

    /// 14.12 SR 27 a: without a body a SELECT is a RETURN of its items; with one it is
    /// unmodelled.
    fn select(&mut self, sel: &'t Plain, scope: &Scope) -> Option<Fields> {
        let env = Env::new(scope.merged());
        if own(sel, "select statement body").is_some() {
            return None;
        }
        let mut cols = Fields::new();
        for item in own(sel, "select item list")
            .map(|l| owns(l, "select item"))
            .unwrap_or_default()
        {
            let Some(ave) = own(item, "aggregating value expression") else {
                continue;
            };
            let t = self.ty(ave, &env);
            let alias = own(item, "select item alias")
                .and_then(|a| own(a, "identifier"))
                .map(Plain::text);
            if let Some(n) = alias.or_else(|| bare(ave)) {
                cols.insert(n, t);
            }
        }
        self.walk_except(sel, &env, &["select item list"]);
        Some(cols)
    }

    /// 14.10, 14.11: the columns a primitive result statement declares; FINISH declares none.
    fn result(&mut self, prs: &'t Plain, scope: &Scope) -> Option<Fields> {
        let incoming = scope.merged();
        let env = Env::new(incoming.clone());
        let mut cols = Fields::new();
        let body = own(prs, "return statement").and_then(|rs| own(rs, "return statement body"));
        if let Some(body) = body {
            if own(body, "asterisk").is_some() {
                cols = scope.table.clone();
            }
            for item in own(body, "return item list")
                .map(|l| owns(l, "return item"))
                .unwrap_or_default()
            {
                let Some(ave) = own(item, "aggregating value expression") else {
                    continue;
                };
                let t = self.ty(ave, &env);
                let alias = own(item, "return item alias")
                    .and_then(|a| own(a, "identifier"))
                    .map(Plain::text);
                if let Some(n) = alias.or_else(|| bare(ave)) {
                    cols.insert(n, t);
                }
            }
            if let Some(gbc) = own(body, "group by clause") {
                self.walk(gbc, &env);
            }
        }
        if let Some(ops) = own(prs, "order by and page statement") {
            let mut refs = incoming;
            refs.extend(cols.clone());
            self.walk(ops, &Env::new(refs));
        }
        body.map(|_| cols)
    }

    /// Check every expression in `node` that belongs to no enclosing expression.
    fn walk(&mut self, node: &'t Plain, env: &Env) {
        self.walk_except(node, env, &[]);
    }

    fn walk_except(&mut self, node: &'t Plain, env: &Env, skip: &[&str]) {
        for k in kids(node) {
            match name(k) {
                Some(n) if skip.contains(&n) => {}
                Some("search condition") => self.condition(k, env),
                // 13.5 SR 5: what DELETE deletes is a node or an edge.
                Some("delete item") => {
                    if let Some(ve) = own(k, "value expression") {
                        let t = self.ty(ve, env);
                        self.expect(k, &t, &[Class::Node, Class::Edge], "13.5 SR 5");
                    }
                }
                Some(
                    "value expression"
                    | "aggregating value expression"
                    | "graph expression"
                    | "binding table expression"
                    | "value expression primary",
                ) => {
                    self.ty(k, env);
                }
                Some("procedure body") => {
                    self.body(
                        k,
                        Scope {
                            record: env.vars.clone(),
                            table: Fields::new(),
                        },
                    );
                }
                Some("graph pattern") => {
                    self.graph_pattern(k, &env.vars);
                }
                Some(_) => self.walk_except(k, env, skip),
                None => {}
            }
        }
    }

    // --- expressions --------------------------------------------------------------------

    /// A <search condition>: 20.20 SR 3 on its <boolean predicand>.
    fn condition(&mut self, sc: &'t Plain, env: &Env) {
        let t = self.ty(sc, env);
        self.expect(sc, &t, &[Class::Bool], "20.20 SR 3");
    }

    /// The declared type of an expression, reporting what breaks the rules inside it.
    fn ty(&mut self, node: &'t Plain, env: &Env) -> Ty {
        let Some(n) = name(node) else {
            return Ty::Any;
        };
        let k = kids(node);
        match n {
            // 21.2 SR 18-19, 21, 53, 58, 60, 63, 65, 71
            "unsigned numeric literal" | "signed numeric literal" => numeric_literal(node),
            "boolean literal" => Ty::Bool,
            "character string literal" => Ty::Char,
            "byte string literal" => Ty::Bytes,
            "null literal" => Ty::Null,
            "date literal" | "SQL-datetime literal" => Ty::Date,
            "time literal" => {
                if zoned(node) {
                    Ty::ZonedTime
                } else {
                    Ty::LocalTime
                }
            }
            "datetime literal" => {
                if zoned(node) {
                    Ty::ZonedDatetime
                } else {
                    Ty::LocalDatetime
                }
            }
            "duration literal" => Ty::Duration(duration_unit(node)),
            // 20.3 SR 2; a parameter's type comes from the request (unmodelled)
            "general value specification" => {
                if k.iter().any(|c| keyword(c, "SESSION_USER")) {
                    Ty::Char
                } else {
                    Ty::Any
                }
            }
            "dynamic parameter specification" => Ty::Any,
            // 20.12 SR 9
            "binding variable reference" => match env.vars.get(&node.text()) {
                Some(Ty::List { elem, group: true }) if env.agg => (**elem).clone(),
                Some(t) => t.clone(),
                None => Ty::Any,
            },
            // 20.2, 20.20 SR 2
            "parenthesized value expression" | "parenthesized boolean value expression" => {
                match k
                    .iter()
                    .find(|c| name(c).is_some_and(|n| n.ends_with("expression")))
                {
                    Some(inner) => self.ty(inner, env),
                    None => Ty::Any,
                }
            }
            "numeric value expression"
            | "term"
            | "datetime value expression"
            | "duration addition and subtraction"
            | "duration term"
                if k.len() == 3 =>
            {
                self.arithmetic(node, k[0], k[1], k[2], env)
            }
            "factor" | "duration factor" if k.len() == 2 => {
                let t = self.ty(k[1], env);
                match t {
                    _ if t.wild() => Ty::Any,
                    Ty::Duration(_) => t,
                    _ if t.class() == Some(Class::Numeric) => t,
                    _ => {
                        // 20.21 SR 3 on <factor>, 20.28 on <duration factor>
                        self.expect(node, &t, &[Class::Numeric, Class::Duration], "20.21 SR 3");
                        Ty::Any
                    }
                }
            }
            "character string concatenation"
            | "byte string concatenation"
            | "list concatenation"
            | "path value concatenation"
                if k.len() == 3 =>
            {
                self.concatenation(node, k[0], k[2], env)
            }
            // 20.20 SR 3
            "boolean value expression" | "boolean term" if k.len() == 3 => {
                for operand in [k[0], k[2]] {
                    let t = self.ty(operand, env);
                    self.expect(operand, &t, &[Class::Bool], "20.20 SR 3");
                }
                Ty::Bool
            }
            "boolean factor" | "boolean test" if k.len() > 1 => {
                let operand = if n == "boolean factor" { k[1] } else { k[0] };
                let t = self.ty(operand, env);
                self.expect(operand, &t, &[Class::Bool], "20.20 SR 3");
                Ty::Bool
            }
            "comparison predicate" => {
                let left = self.ty(k[0], env);
                if let Some(part) = own(node, "comparison predicate part 2") {
                    self.comparison_part(part, &left, env);
                }
                Ty::Bool
            }
            "null predicate" | "value type predicate" => {
                self.ty(k[0], env);
                Ty::Bool
            }
            "normalized predicate" => {
                let t = self.ty(k[0], env);
                self.expect(k[0], &t, &[Class::Char, Class::Bytes], "20.23 SR 2, 4");
                Ty::Bool
            }
            // 19.8 SR 3
            "directed predicate" => {
                self.element(k[0], env, &[Class::Edge], "19.8 SR 3");
                Ty::Bool
            }
            "labeled predicate" | "property_exists predicate" => {
                for evr in owns(node, "element variable reference") {
                    self.element(evr, env, ELEMENT, "16.10 SR 3");
                }
                Ty::Bool
            }
            // 19.10 SR 2-3
            "source/destination predicate" => {
                if let Some(nr) = own(node, "node reference") {
                    self.element(kids(nr)[0], env, &[Class::Node], "19.10 SR 2");
                }
                if let Some(er) = first(node, "edge reference") {
                    self.element(kids(er)[0], env, &[Class::Edge], "19.10 SR 3");
                }
                Ty::Bool
            }
            // 22.13 SR 1 b-c
            "all_different predicate" | "same predicate" => {
                let evrs = owns(node, "element variable reference");
                let types: Vec<Ty> = evrs
                    .iter()
                    .map(|e| self.element(e, env, ELEMENT, "16.10 SR 3"))
                    .collect();
                for i in 1..types.len() {
                    if !comparable(&types[0], &types[i]) {
                        self.report(
                            evrs[i],
                            "22.13 CR 1",
                            format!("{} and {} are not comparable", types[0], types[i]),
                        );
                    }
                }
                Ty::Bool
            }
            "exists predicate" => {
                let scope = Scope {
                    record: env.vars.clone(),
                    table: Fields::new(),
                };
                if let Some(gp) = own(node, "graph pattern") {
                    self.graph_pattern(gp, &env.vars);
                } else if let Some(block) = own(node, "match statement block") {
                    let mut scope = scope;
                    for m in owns(block, "match statement") {
                        scope = self.match_statement(m, scope);
                    }
                } else if let Some(pb) = first(node, "procedure body") {
                    self.body(pb, scope);
                }
                Ty::Bool
            }
            "value query expression" => self.value_query(node, env),
            "case abbreviation" => self.case_abbreviation(node, env),
            "simple case" | "searched case" => self.case(node, env),
            "cast specification" => self.cast(node, env),
            "aggregate function" => self.aggregate(node, env),
            "property reference" => self.property(node, env),
            // 20.10 SR 3: implementation-defined
            "element_id function" => {
                if let Some(evr) = own(node, "element variable reference") {
                    self.element(evr, env, ELEMENT, "16.10 SR 3");
                }
                Ty::Any
            }
            "let value expression" => {
                // 20.5 SR 3, 5, 7: the definitions see the incoming record, the result all
                let mut inner = env.clone();
                if let Some(list) = own(node, "let variable definition list") {
                    for def in owns(list, "let variable definition") {
                        if let Some((n, t)) = self.value_definition(def, env) {
                            inner.vars.insert(n, t);
                        }
                    }
                }
                match own(node, "value expression") {
                    Some(rhs) => self.ty(rhs, &inner),
                    None => Ty::Any,
                }
            }
            "list value constructor by enumeration" => {
                let elems: Vec<&Plain> = own(node, "list element list")
                    .map(|l| owns(l, "list element"))
                    .unwrap_or_default();
                let types: Vec<Ty> = elems.iter().map(|e| self.ty(e, env)).collect();
                // 20.17 SR 3 b: ID004 or the empty type
                let elem = if types.is_empty() {
                    Ty::Any
                } else {
                    self.combined(node, &types, "20.17 SR 3")
                };
                Ty::List {
                    elem: Box::new(elem),
                    group: false,
                }
            }
            // 20.18, 20.19
            "record constructor" => {
                let mut fields = Fields::new();
                let mut items = Vec::new();
                find_fields(node, &mut items);
                for f in items {
                    let fname = own(f, "field name").map(ident).unwrap_or_default();
                    let t = own(f, "value expression").map_or(Ty::Any, |v| self.ty(v, env));
                    if fields.insert(fname.clone(), t).is_some() {
                        self.report(f, "20.19 SR 2", format!("field {fname} is specified twice"));
                    }
                }
                Ty::Record(Some(fields))
            }
            // 20.14, 20.1 SR 4-5
            "path value constructor by enumeration" => {
                if let Some(list) = own(node, "path element list") {
                    if let Some(start) = own(list, "path element list start") {
                        let t = self.ty(start, env);
                        self.expect(start, &t, &[Class::Node], "20.1 SR 4");
                    }
                    for step in owns(list, "path element list step") {
                        if let Some(e) = own(step, "edge reference value expression") {
                            let t = self.ty(e, env);
                            self.expect(e, &t, &[Class::Edge], "20.1 SR 5");
                        }
                        if let Some(v) = own(step, "node reference value expression") {
                            let t = self.ty(v, env);
                            self.expect(v, &t, &[Class::Node], "20.1 SR 4");
                        }
                    }
                }
                Ty::Path
            }
            // 20.22 SR 1, 3
            "char length expression" => {
                self.argument(node, env, &[Class::Char], "20.23 SR 2");
                Ty::Exact { int: true }
            }
            "byte length expression" => {
                self.argument(node, env, &[Class::Bytes], "20.23 SR 4");
                Ty::Exact { int: true }
            }
            "path length expression" => {
                self.argument(node, env, &[Class::Path], "20.13 SR 2");
                Ty::Exact { int: true }
            }
            "cardinality expression" => {
                if k.iter().any(|c| keyword(c, "SIZE")) {
                    self.argument(node, env, &[Class::List], "20.15 SR 1");
                } else {
                    self.argument(
                        node,
                        env,
                        &[Class::Table, Class::Path, Class::List, Class::Record],
                        "20.1 SR 3, 6, 20.13 SR 2, 20.15 SR 1",
                    );
                }
                Ty::Exact { int: true }
            }
            // 20.22 SR 4 and 20.29: ABS of a number or of a duration
            "absolute value expression" | "duration absolute value function" => {
                let t = self.argument(node, env, &[Class::Numeric, Class::Duration], "20.21 SR 3");
                if t.wild() { Ty::Any } else { t }
            }
            // 20.22 SR 5
            "modulus expression" => {
                let mut last = Ty::Any;
                for a in args(node) {
                    last = self.ty(a, env);
                    self.expect(a, &last, &[Class::Numeric], "20.21 SR 3");
                }
                if last.wild() { Ty::Number } else { last }
            }
            // 20.22 SR 6-10, 12-13
            "trigonometric function"
            | "general logarithm function"
            | "common logarithm"
            | "natural logarithm"
            | "exponential function"
            | "power function"
            | "square root" => {
                for a in args(node) {
                    let t = self.ty(a, env);
                    self.expect(a, &t, &[Class::Numeric], "20.21 SR 3");
                }
                Ty::Approx
            }
            // 20.22 SR 11
            "floor function" | "ceiling function" => {
                match self.argument(node, env, &[Class::Numeric], "20.21 SR 3") {
                    Ty::Exact { .. } => Ty::Exact { int: true },
                    Ty::Approx => Ty::Approx,
                    _ => Ty::Number,
                }
            }
            // 20.24 SR 1, 20.25 SR 1: LEFT and RIGHT of either string
            "substring function" | "byte string substring function" => {
                let a = args(node);
                let t = match a.first() {
                    Some(s) => {
                        let t = self.ty(s, env);
                        self.expect(s, &t, &[Class::Char, Class::Bytes], "20.23 SR 2, 4");
                        t
                    }
                    None => Ty::Any,
                };
                if let Some(len) = a.get(1) {
                    let lt = self.ty(len, env);
                    self.expect(len, &lt, &[Class::Numeric], "20.21 SR 3");
                }
                if t.wild() { Ty::Any } else { t }
            }
            // 20.24 SR 2, 5
            "fold" | "normalize function" => {
                self.argument(node, env, &[Class::Char], "20.23 SR 2");
                Ty::Char
            }
            // 20.24 SR 3-4, 20.25 SR 2
            "single-character trim function"
            | "byte string trim function"
            | "multi-character trim function" => self.trim(node, env),
            // 20.16 SR 1
            "trim list function" => {
                let a = args(node);
                let mut t = Ty::Any;
                if let Some(list) = a.first() {
                    t = self.ty(list, env);
                    self.expect(list, &t, &[Class::List], "20.15 SR 1");
                }
                if let Some(count) = a.get(1) {
                    let ct = self.ty(count, env);
                    if !ct.wild() && ct != (Ty::Exact { int: true }) {
                        self.report(
                            count,
                            "20.16 SR 1",
                            format!(
                                "{} has type {ct}, not an exact number of scale 0",
                                count.text()
                            ),
                        );
                    }
                }
                match t {
                    Ty::List { elem, .. } => Ty::List { elem, group: false },
                    _ => Ty::Any,
                }
            }
            // 20.16 SR 2 (ID005)
            "elements function" => {
                self.argument(node, env, &[Class::Path], "20.13 SR 2");
                Ty::List {
                    elem: Box::new(Ty::Any),
                    group: false,
                }
            }
            // 20.27 SR 6-10
            "date function"
            | "time function"
            | "localtime function"
            | "datetime function"
            | "localdatetime function" => {
                self.walk(node, env);
                match n {
                    "date function" => Ty::Date,
                    "time function" => Ty::ZonedTime,
                    "localtime function" => Ty::LocalTime,
                    "datetime function" => Ty::ZonedDatetime,
                    _ => Ty::LocalDatetime,
                }
            }
            "duration function" => {
                self.walk(node, env);
                Ty::Duration(duration_unit(node))
            }
            "datetime subtraction" => self.duration_between(node, env),
            "graph reference value expression" if k.iter().any(|c| keyword(c, "GRAPH")) => {
                self.walk(node, env);
                Ty::Graph
            }
            "binding table reference value expression" if k.iter().any(|c| keyword(c, "TABLE")) => {
                self.walk(node, env);
                Ty::Table
            }
            // 11.1 SR 3 a ii, 11.2 SR 4 b ii
            "graph expression" | "binding table expression" => {
                let (want, rule, ty) = if n == "graph expression" {
                    (Class::Graph, "11.1 SR 3", Ty::Graph)
                } else {
                    (Class::Table, "11.2 SR 4", Ty::Table)
                };
                if let Some(oep) = own(node, "object expression primary") {
                    // reading: `"g"` and `a.b` derive as a catalog reference too (a delimited
                    // name, a parent and a name), which always types
                    if !double_quoted(oep) && !dotted(oep) {
                        let inner = kids(oep)
                            .into_iter()
                            .find(|c| matches!(c, Plain::Def { .. }))
                            .map_or(Ty::Any, |v| self.ty(v, env));
                        self.expect(oep, &inner, &[want], rule);
                    }
                } else if let Some(onbv) = own(node, "object name or binding variable") {
                    // SR 2 a: a bound name is a variable reference, otherwise a catalog name
                    if let Some(t) = env.vars.get(&onbv.text()) {
                        let t = t.clone();
                        self.expect(onbv, &t, &[want], rule);
                    }
                } else {
                    self.walk(node, env);
                }
                ty
            }
            "nested query specification" => {
                if let Some(pb) = first(node, "procedure body") {
                    self.body(
                        pb,
                        Scope {
                            record: env.vars.clone(),
                            table: Fields::new(),
                        },
                    );
                }
                Ty::Table
            }
            _ => {
                let defs: Vec<&'t Plain> = k
                    .iter()
                    .copied()
                    .filter(|c| matches!(c, Plain::Def { .. }))
                    .collect();
                if k.len() == 1 && defs.len() == 1 {
                    return self.ty(defs[0], env);
                }
                for d in defs {
                    self.ty(d, env);
                }
                Ty::Any
            }
        }
    }

    /// The type of the single expression argument of a function, checked against `classes`.
    fn argument(&mut self, f: &'t Plain, env: &Env, classes: &[Class], rule: &'static str) -> Ty {
        match args(f).first() {
            Some(a) => {
                let t = self.ty(a, env);
                self.expect(a, &t, classes, rule);
                t
            }
            None => Ty::Any,
        }
    }

    /// An <element variable reference> (16.10 SR 3) that a predicate wants as `classes`.
    fn element(&mut self, evr: &'t Plain, env: &Env, classes: &[Class], rule: &'static str) -> Ty {
        let t = self.ty(evr, env);
        let group_of_elements = matches!(&t, Ty::List { elem, group: true } if elem.is(ELEMENT));
        if !(t.is(ELEMENT) || group_of_elements) {
            self.report(
                evr,
                "16.10 SR 3",
                format!("{} has type {t}, not a node or edge", evr.text()),
            );
        } else if classes != ELEMENT {
            self.expect(evr, &t, classes, rule);
        }
        t
    }

    /// `+ - * /` by Table 1 (4.16.6.4), 20.21, 20.26 and 20.28: the operator accepts what any of
    /// its derivations accepts.
    fn arithmetic(
        &mut self,
        node: &'t Plain,
        left: &'t Plain,
        op: &'t Plain,
        right: &'t Plain,
        env: &Env,
    ) -> Ty {
        use Class::{Duration as D, Instant as I, Numeric as N};
        let l = self.ty(left, env);
        let r = self.ty(right, env);
        let op = op.text();
        let rows: &[(Class, Class)] = match op.as_str() {
            "+" => &[(N, N), (I, D), (D, I), (D, D)],
            "-" => &[(N, N), (I, D), (D, D)],
            "*" => &[(N, N), (D, N), (N, D)],
            _ => &[(N, N), (D, N)],
        };
        let hits: Vec<(Class, Class)> = rows
            .iter()
            .copied()
            .filter(|(a, b)| l.is(&[*a]) && r.is(&[*b]))
            .collect();
        let temporal = [&l, &r].iter().any(|t| matches!(t.class(), Some(I | D)));
        match hits.as_slice() {
            [] => {
                let rule = if temporal { "4.16.6.4" } else { "20.21 SR 3" };
                self.report(node, rule, format!("no operator {l} {op} {r}"));
                Ty::Any
            }
            [(N, N)] => match (&l, &r) {
                (Ty::Approx, _) | (_, Ty::Approx) => Ty::Approx,
                // 20.21 SR 1 b ii-iv: scale max(S1, S2), S1 + S2, or implementation-defined
                (Ty::Exact { int: a }, Ty::Exact { int: b }) => Ty::Exact {
                    int: *a && *b && op != "/",
                },
                _ => Ty::Number,
            },
            // 20.26 SR 1
            [(I, D)] | [(D, I)] => {
                let instant = if l.class() == Some(I) { &l } else { &r };
                match instant {
                    Ty::ZonedDatetime => Ty::ZonedDatetime,
                    _ if instant.wild() => Ty::Any,
                    _ => Ty::LocalDatetime,
                }
            }
            // 20.28 SR 1
            [(D, D)] => match (&l, &r) {
                (Ty::Duration(Some(a)), Ty::Duration(Some(b))) if a != b => {
                    self.report(
                        node,
                        "20.28 SR 1",
                        format!("{l} and {r} are of different duration unit groups"),
                    );
                    Ty::Any
                }
                (Ty::Duration(Some(_)), _) => l,
                (_, Ty::Duration(Some(_))) => r,
                _ => Ty::Duration(None),
            },
            [(D, N)] => l,
            [(N, D)] => r,
            _ => Ty::Any,
        }
    }

    /// `||` of strings (20.23), lists (20.15) or paths (20.13).
    fn concatenation(
        &mut self,
        node: &'t Plain,
        left: &'t Plain,
        right: &'t Plain,
        env: &Env,
    ) -> Ty {
        let l = self.ty(left, env);
        let r = self.ty(right, env);
        let classes = [Class::Char, Class::Bytes, Class::List, Class::Path];
        let known: Vec<Class> = [&l, &r].iter().filter_map(|t| t.class()).collect();
        let fine =
            known.iter().all(|c| classes.contains(c)) && known.windows(2).all(|w| w[0] == w[1]);
        if !fine {
            let rule = if known.contains(&Class::List) {
                "20.15 SR 1"
            } else if known.contains(&Class::Path) {
                "20.13 SR 2"
            } else if known.contains(&Class::Bytes) {
                "20.23 SR 4"
            } else {
                "20.23 SR 2"
            };
            self.report(node, rule, format!("no operator {l} || {r}"));
            return Ty::Any;
        }
        match known.first() {
            // 20.15 SR 2: the regular variant of the combination
            Some(Class::List) => {
                let lists: Vec<Ty> = [l, r].into_iter().filter(|t| !t.wild()).collect();
                match self.combined(node, &lists, "20.15 SR 2") {
                    Ty::List { elem, .. } => Ty::List { elem, group: false },
                    t => t,
                }
            }
            Some(Class::Char) => Ty::Char,
            Some(Class::Bytes) => Ty::Bytes,
            Some(Class::Path) => Ty::Path,
            _ => Ty::Any,
        }
    }

    /// 22.18 applied for `rule`: the combination, or a report and the unknown type.
    fn combined(&mut self, at: &Plain, types: &[Ty], rule: &'static str) -> Ty {
        match combine(types) {
            Some(t) => t,
            None => {
                let names: Vec<String> = types.iter().map(Ty::to_string).collect();
                self.report(
                    at,
                    "22.19 SR 4",
                    format!("{rule}: {} do not combine", names.join(", ")),
                );
                Ty::Any
            }
        }
    }

    /// 19.3 SR 2 and the operations of 22.13-22.14: `<comp op> <comparison predicand>` against
    /// `left`.
    fn comparison_part(&mut self, part: &'t Plain, left: &Ty, env: &Env) {
        let Some(right) = own(part, "comparison predicand") else {
            return;
        };
        let r = self.ty(right, env);
        let equality = own(part, "comp op").is_some_and(|op| {
            first(op, "equals operator").is_some() || first(op, "not equals operator").is_some()
        });
        if !comparable(left, &r) {
            let rule = if equality { "22.13 CR 1" } else { "22.14 CR 1" };
            self.report(part, rule, format!("{left} and {r} are not comparable"));
        }
    }

    /// 20.6: the type of the single column of the nested query's result.
    fn value_query(&mut self, vqe: &'t Plain, env: &Env) -> Ty {
        let Some(pb) = first(vqe, "procedure body") else {
            return Ty::Any;
        };
        let cols = self.body(
            pb,
            Scope {
                record: env.vars.clone(),
                table: Fields::new(),
            },
        );
        match cols {
            // SR 13
            Some(cols) if cols.len() == 1 => cols.into_values().next().unwrap_or(Ty::Any),
            // SR 3
            Some(cols) => {
                self.report(
                    vqe,
                    "20.6 SR 3",
                    format!("the nested query returns {} columns", cols.len()),
                );
                Ty::Any
            }
            None => Ty::Any,
        }
    }

    /// 20.7 SR 1: NULLIF and COALESCE as the CASE they stand for.
    fn case_abbreviation(&mut self, ca: &'t Plain, env: &Env) -> Ty {
        let operands = owns(ca, "value expression");
        let types: Vec<Ty> = operands.iter().map(|o| self.ty(o, env)).collect();
        if kids(ca).first().is_some_and(|k| keyword(k, "NULLIF")) {
            // CASE WHEN V1 = V2 THEN NULL ELSE V1 END
            if types.len() == 2 && !comparable(&types[0], &types[1]) {
                self.report(
                    ca,
                    "22.13 CR 1",
                    format!("{} and {} are not comparable", types[0], types[1]),
                );
            }
            return types.into_iter().next().unwrap_or(Ty::Any);
        }
        self.combined(ca, &types, "20.7 SR 5")
    }

    /// 20.7 SR 2-5.
    fn case(&mut self, cs: &'t Plain, env: &Env) -> Ty {
        let operand = own(cs, "case operand").map(|co| (co, self.ty(co, env)));
        let mut results = Vec::new();
        for clause in owns(cs, "simple when clause")
            .into_iter()
            .chain(owns(cs, "searched when clause"))
        {
            if let Some(sc) = own(clause, "search condition") {
                self.condition(sc, env);
            }
            if let (Some((co, ct)), Some(list)) = (&operand, own(clause, "when operand list")) {
                for wo in owns(list, "when operand") {
                    self.when_operand(co, ct, wo, env);
                }
            }
            results.extend(own(clause, "result"));
        }
        results.extend(own(cs, "else clause").and_then(|e| own(e, "result")));
        let mut types = Vec::new();
        for r in results {
            // reading: a bare NULL is the <null literal> alternative on every tree
            if !null_literal(r) {
                types.push(self.ty(r, env));
            }
        }
        if types.is_empty() {
            self.report(cs, "20.7 SR 3", "every <result> is NULL".into());
            return Ty::Null;
        }
        self.combined(cs, &types, "20.7 SR 5")
    }

    /// 20.7 SR 2 e as Cor 1 leaves it: the predicate `CO <when operand>`, checked by Clause 19.
    fn when_operand(&mut self, co: &'t Plain, ct: &Ty, wo: &'t Plain, env: &Env) {
        let Some(inner) = kids(wo).into_iter().next() else {
            return;
        };
        match name(inner) {
            Some("non-parenthesized value expression primary") => {
                let t = self.ty(inner, env);
                if !comparable(ct, &t) {
                    self.report(wo, "22.13 CR 1", format!("{ct} and {t} are not comparable"));
                }
            }
            Some("comparison predicate part 2") => self.comparison_part(inner, ct, env),
            Some("normalized predicate part 2") => {
                self.expect(co, ct, &[Class::Char, Class::Bytes], "20.23 SR 2, 4")
            }
            Some("directed predicate part 2") => {
                self.case_element(co, ct, &[Class::Edge], "19.8 SR 3")
            }
            Some("labeled predicate part 2") => self.case_element(co, ct, ELEMENT, "16.10 SR 3"),
            Some("source predicate part 2" | "destination predicate part 2") => {
                self.case_element(co, ct, &[Class::Node], "19.10 SR 2");
                if let Some(er) = first(inner, "edge reference") {
                    self.element(kids(er)[0], env, &[Class::Edge], "19.10 SR 3");
                }
            }
            _ => {}
        }
    }

    fn case_element(&mut self, co: &Plain, ct: &Ty, classes: &[Class], rule: &'static str) {
        if !ct.is(ELEMENT) {
            self.report(
                co,
                "16.10 SR 3",
                format!("{} has type {ct}, not a node or edge", co.text()),
            );
        } else {
            self.expect(co, ct, classes, rule);
        }
    }

    /// 20.8 SR 3-12.
    fn cast(&mut self, cs: &'t Plain, env: &Env) -> Ty {
        let Some(target) = own(cs, "cast target") else {
            return Ty::Any;
        };
        let td = value_type(target);
        // SR 4
        if matches!(td.ty, Ty::Null | Ty::Nothing) {
            self.report(
                target,
                "20.8 SR 4",
                format!("{td} is an immaterial value type"),
            );
            return td.ty;
        }
        let Some(co) = own(cs, "cast operand") else {
            return td.ty;
        };
        let sd = if null_literal(co) {
            Ty::Null
        } else {
            self.ty(co, env)
        };
        if sd == Ty::Null {
            // SR 5, and its reading for an operand of the null type
            if !td.nullable {
                self.report(cs, "20.8 SR 5", format!("NULL cast to {td}"));
            }
        } else if !castable(&sd, &td.ty) {
            self.report(cs, "20.8 SR 8", format!("no cast from {sd} to {td}"));
        }
        td.ty
    }

    /// 20.9 SR 5-9.
    fn aggregate(&mut self, af: &'t Plain, env: &Env) -> Ty {
        let inner = Env {
            agg: true,
            ..env.clone()
        };
        if let Some(gsf) = own(af, "general set function") {
            let kind = own(gsf, "general set function type")
                .map(|t| t.text().to_uppercase())
                .unwrap_or_default();
            let Some(ve) = own(gsf, "value expression") else {
                return Ty::Any;
            };
            let dt = self.ty(ve, &inner);
            return match kind.as_str() {
                // SR 7 b
                "COUNT" => Ty::Exact { int: true },
                // SR 8 c
                "MIN" | "MAX" => dt,
                // SR 8 d
                "SUM" | "AVG" => {
                    self.expect(ve, &dt, &[Class::Numeric], "20.9 SR 8");
                    match dt {
                        Ty::Approx => Ty::Approx,
                        Ty::Exact { int } if kind == "SUM" => Ty::Exact { int },
                        Ty::Exact { .. } => Ty::Exact { int: false },
                        _ => Ty::Number,
                    }
                }
                // SR 8 e
                "STDDEV_SAMP" | "STDDEV_POP" => {
                    self.expect(ve, &dt, &[Class::Numeric], "20.9 SR 8");
                    Ty::Approx
                }
                // SR 8 f
                "COLLECT_LIST" => Ty::List {
                    elem: Box::new(dt),
                    group: false,
                },
                _ => Ty::Any,
            };
        }
        if let Some(bsf) = own(af, "binary set function") {
            // SR 9: both are <numeric value expression>s (20.21 SR 3); IVE sees no group
            if let Some(dve) = own(bsf, "dependent value expression") {
                for nve in owns(dve, "numeric value expression") {
                    let t = self.ty(nve, &inner);
                    self.expect(nve, &t, &[Class::Numeric], "20.21 SR 3");
                }
            }
            if let Some(ive) = own(bsf, "independent value expression") {
                let t = self.ty(ive, env);
                self.expect(ive, &t, &[Class::Numeric], "20.21 SR 3");
            }
            // SR 9 j
            return Ty::Approx;
        }
        // COUNT(*), SR 7 b
        Ty::Exact { int: true }
    }

    /// 20.11.
    fn property(&mut self, pr: &'t Plain, env: &Env) -> Ty {
        let Some(source) = own(pr, "property source") else {
            return Ty::Any;
        };
        let pn = own(pr, "property name").map(ident).unwrap_or_default();
        // reading: `9.M`, `9.F`, `9.E3` and `9.E+3` derive as a property of 9 and as a numeric
        // literal (21.2); no number has properties (20.1 SR 4-6), so the types pick the literal
        if let Some(t) = literal_continuation(source, &pn) {
            return t;
        }
        let psd = self.ty(source, env);
        match &psd {
            // SR 2 a
            Ty::Record(Some(fields)) => match fields.get(&pn) {
                Some(t) => t.clone(),
                None => {
                    self.report(pr, "20.11 SR 2", format!("{psd} has no field {pn}"));
                    Ty::Any
                }
            },
            // SR 2 b, SR 3 b: open types give a dynamic type
            Ty::Record(None) | Ty::Node | Ty::Edge => Ty::Any,
            // 21.2 SR 67: a bare NULL takes its type from a context that fixes one; a property
            // source fixes none of node, edge or record
            Ty::Null => {
                self.report(
                    source,
                    "20.1 SR 4-6",
                    "NULL fixes no node, edge or record type (21.2 SR 67)".into(),
                );
                Ty::Any
            }
            _ if psd.wild() => Ty::Any,
            // 20.1 SR 4-6 on the three derivations of <property source>
            _ => {
                self.report(
                    source,
                    "20.1 SR 4-6",
                    format!(
                        "{} has type {psd}, not a node, edge or record",
                        source.text()
                    ),
                );
                Ty::Any
            }
        }
    }

    /// 20.24 SR 3-4, 20.25 SR 2: the source of a trim, and a trim string comparable to it.
    fn trim(&mut self, f: &'t Plain, env: &Env) -> Ty {
        let mut sources = Vec::new();
        find_any(f, &["trim source", "byte string trim source"], &mut sources);
        let mut chars = Vec::new();
        find_any(
            f,
            &["trim character string", "trim byte string"],
            &mut chars,
        );
        let classes: &[Class] = if name(f) == Some("multi-character trim function") {
            &[Class::Char]
        } else {
            &[Class::Char, Class::Bytes]
        };
        let rule = if classes.len() == 1 {
            "20.23 SR 2"
        } else {
            "20.23 SR 2, 4"
        };
        let source = sources.first().map_or(Ty::Any, |s| {
            let t = self.ty(s, env);
            self.expect(s, &t, classes, rule);
            t
        });
        for c in chars {
            let t = self.ty(c, env);
            self.expect(c, &t, classes, rule);
            if !comparable(&source, &t) {
                self.report(
                    c,
                    "20.24 SR 3",
                    format!("{t} and {source} are not comparable"),
                );
            }
        }
        if source.wild() { Ty::Any } else { source }
    }

    /// 20.28 SR 3: DURATION_BETWEEN.
    fn duration_between(&mut self, ds: &'t Plain, env: &Env) -> Ty {
        let params: Vec<&Plain> = own(ds, "datetime subtraction parameters")
            .map(|p| {
                kids(p)
                    .into_iter()
                    .filter(|k| name(k).is_some_and(|n| n.starts_with("datetime value")))
                    .collect()
            })
            .unwrap_or_default();
        let types: Vec<Ty> = params
            .iter()
            .map(|p| {
                let t = self.ty(p, env);
                // reading: 20.26 GR 1 fails on every evaluation
                self.expect(p, &t, &[Class::Instant], "20.26 GR 1");
                t
            })
            .collect();
        if let [a, b] = types.as_slice()
            && a.is(&[Class::Instant])
            && b.is(&[Class::Instant])
            && !comparable(a, b)
        {
            self.report(
                ds,
                "20.28 SR 3",
                format!("{a} and {b} are not essentially comparable"),
            );
        }
        let qualifier = own(ds, "temporal duration qualifier").map(|q| q.text().to_uppercase());
        let year_month = qualifier.as_deref().is_some_and(|q| q.starts_with("YEAR"));
        let times = types
            .iter()
            .all(|t| matches!(t, Ty::LocalTime | Ty::ZonedTime));
        if year_month && times && !types.is_empty() {
            self.report(ds, "20.28 SR 3", "times subtracted as YEAR TO MONTH".into());
        }
        Ty::Duration(Some(if year_month {
            Unit::YearMonth
        } else {
            Unit::DayTime
        }))
    }
}

// --- types of literals and <value type>s -------------------------------------------------

/// 21.2 SR 12, 15, 18-19.
fn numeric_literal(node: &Plain) -> Ty {
    if contains(node, "approximate numeric literal") {
        return Ty::Approx;
    }
    let Some(enl) = first(node, "exact numeric literal") else {
        return Ty::Number;
    };
    let parts = kids(enl);
    match parts.first().and_then(|p| name(p)) {
        Some("unsigned integer" | "unsigned decimal integer") => Ty::Exact { int: true },
        // SR 15: the scale is the number of digits after the period
        Some("unsigned decimal in common notation") => {
            let inner = kids(parts[0]);
            let after = inner
                .iter()
                .position(|p| name(p) == Some("period"))
                .is_none_or(|i| i + 1 == inner.len());
            Ty::Exact { int: after }
        }
        _ => Ty::Exact { int: false },
    }
}

/// 21.2 SR 63, 65: a time or datetime string with a time zone displacement.
fn zoned(literal: &Plain) -> bool {
    let text = literal.text();
    let Some(body) = text.split_once('\'').map(|(_, b)| b.trim_end_matches('\'')) else {
        return false;
    };
    let time = body.rsplit_once(['T', 't']).map_or(body, |(_, t)| t);
    time.contains(['+', '-', 'Z', 'z'])
}

/// 21.2 SR 71: the unit group of a duration literal or of a DURATION function's string.
fn duration_unit(node: &Plain) -> Option<Unit> {
    if let Some(sql) = first(node, "SQL-interval literal") {
        let text = sql.text().to_uppercase();
        return Some(if text.ends_with("YEAR") || text.ends_with("MONTH") {
            Unit::YearMonth
        } else {
            Unit::DayTime
        });
    }
    let s = first(node, "duration string")?.text().to_uppercase();
    Some(if s.contains('T') || s.contains('D') {
        Unit::DayTime
    } else {
        Unit::YearMonth
    })
}

/// 18.9: the value type a <value type> (or a <cast target>) specifies.
fn value_type(node: &Plain) -> Declared {
    // reading: `A | B LIST` is a union with a list and a list of a union alike, so a type with a
    // union of several components in it is unmodelled
    let mut unions = Vec::new();
    find(node, "component type list", &mut unions);
    if unions.iter().any(|u| owns(u, "component type").len() > 1) {
        return Declared {
            ty: Ty::Any,
            nullable: true,
        };
    }
    let nullable = !not_null(node);
    let ty = match name(node) {
        Some("boolean type") => Ty::Bool,
        Some("character string type") => Ty::Char,
        Some("byte string type") => Ty::Bytes,
        Some(
            "signed binary exact numeric type"
            | "unsigned binary exact numeric type"
            | "verbose binary exact numeric type",
        ) => Ty::Exact { int: true },
        Some("decimal exact numeric type") => Ty::Exact {
            int: own(node, "scale").is_none_or(|s| s.text().trim_start_matches('0').is_empty()),
        },
        Some("approximate numeric type") => Ty::Approx,
        Some("datetime type") => Ty::ZonedDatetime,
        Some("localdatetime type") => Ty::LocalDatetime,
        Some("date type") => Ty::Date,
        Some("time type") => Ty::ZonedTime,
        Some("localtime type") => Ty::LocalTime,
        Some("temporal duration type") => Ty::Duration(Some(
            if own(node, "temporal duration qualifier")
                .is_some_and(|q| q.text().to_uppercase().starts_with("YEAR"))
            {
                Unit::YearMonth
            } else {
                Unit::DayTime
            },
        )),
        Some("null type") => Ty::Null,
        Some("empty type") => Ty::Nothing,
        Some("open graph reference value type" | "closed graph reference value type") => Ty::Graph,
        Some("binding table reference value type") => Ty::Table,
        Some("open node reference value type" | "closed node reference value type") => Ty::Node,
        Some("open edge reference value type" | "closed edge reference value type") => Ty::Edge,
        Some("path value type") => Ty::Path,
        Some("list value type") => Ty::List {
            elem: Box::new(own(node, "value type").map_or(Ty::Any, |v| value_type(v).ty)),
            group: own(node, "list value type name")
                .is_some_and(|n| kids(n).iter().any(|k| keyword(k, "GROUP"))),
        },
        Some("record type") => match own(node, "field types specification") {
            Some(spec) => {
                let mut fields = Fields::new();
                let mut items = Vec::new();
                find(spec, "field type", &mut items);
                for f in items {
                    let fname = own(f, "field name").map(ident).unwrap_or_default();
                    let t = own(f, "value type").map_or(Ty::Any, |v| value_type(v).ty);
                    fields.insert(fname, t);
                }
                Ty::Record(Some(fields))
            }
            None => Ty::Record(None),
        },
        // 4.14.3: a union of one component type is that type; others are unmodelled
        Some("closed dynamic union type") => {
            let mut comps = Vec::new();
            if let Some(list) = own(node, "component type list") {
                comps = owns(list, "component type");
            }
            match comps.as_slice() {
                [only] => return value_type(only),
                _ => Ty::Any,
            }
        }
        _ => match kids(node).as_slice() {
            [only @ Plain::Def { .. }] => return value_type(only),
            _ => Ty::Any,
        },
    };
    let nullable = nullable && ty != Ty::Nothing;
    Declared { ty, nullable }
}

/// A <not null> that belongs to this type, not to a type inside it.
fn not_null(node: &Plain) -> bool {
    const INNER: &[&str] = &[
        "value type",
        "field types specification",
        "binding table type",
        "nested graph type specification",
        "node type specification",
        "edge type specification",
        "component type list",
    ];
    kids(node).into_iter().any(|k| match name(k) {
        Some("not null") => true,
        Some(n) if INNER.contains(&n) => false,
        Some(_) => not_null(k),
        None => false,
    })
}

// --- tree helpers ------------------------------------------------------------------------

/// The variables a graph pattern declares (16.3, 16.4, 16.7 SR 22 e): element variables of a
/// quantified path primary are group lists.
fn pattern_vars(node: &Plain, kind: Option<Ty>, group: bool, out: &mut Fields) {
    let Plain::Def { .. } = node else { return };
    match name(node) {
        Some("node pattern") => {
            for k in kids(node) {
                pattern_vars(k, Some(Ty::Node), group, out);
            }
        }
        Some("edge pattern") => {
            for k in kids(node) {
                pattern_vars(k, Some(Ty::Edge), group, out);
            }
        }
        Some("quantified path primary") => {
            for k in kids(node) {
                pattern_vars(k, kind.clone(), true, out);
            }
        }
        Some("element variable declaration") => {
            if let (Some(bv), Some(t)) = (first(node, "binding variable"), kind) {
                let t = if group {
                    Ty::List {
                        elem: Box::new(t),
                        group: true,
                    }
                } else {
                    t
                };
                out.entry(bv.text()).or_insert(t);
            }
        }
        Some("path variable declaration") => {
            if let Some(bv) = first(node, "binding variable") {
                out.entry(bv.text()).or_insert(Ty::Path);
            }
        }
        // a subpath variable is not referenceable (4.11.5)
        Some("subpath variable declaration") => {}
        // the WHERE clause of a nested pattern binds nothing
        Some("graph pattern where clause" | "element pattern predicate") => {}
        _ => {
            for k in kids(node) {
                pattern_vars(k, kind.clone(), group, out);
            }
        }
    }
}

/// A node or edge for its group list.
fn element_of(t: &Ty) -> Ty {
    match t {
        Ty::List { elem, group: true } => (**elem).clone(),
        t => t.clone(),
    }
}

/// The columns of `table` a <yield clause> selects and renames (16.14).
fn yield_columns(yc: &Plain, table: &Fields) -> Fields {
    let mut out = Fields::new();
    let mut items = Vec::new();
    find(yc, "yield item", &mut items);
    for item in items {
        let Some(field) = own(item, "yield item name") else {
            continue;
        };
        let from = ident(field);
        let to = own(item, "yield item alias")
            .and_then(|a| own(a, "binding variable"))
            .map_or_else(|| from.clone(), Plain::text);
        out.insert(to, table.get(&from).cloned().unwrap_or(Ty::Any));
    }
    out
}

/// The expression arguments of a function: its kids that are neither keywords nor punctuation.
fn args(f: &Plain) -> Vec<&Plain> {
    const PUNCTUATION: &[&str] = &["left paren", "right paren", "comma"];
    kids(f)
        .into_iter()
        .filter(|k| name(k).is_some_and(|n| !PUNCTUATION.contains(&n) && !n.ends_with(" name")))
        .collect()
}

/// A <field>s of a record constructor, not of records nested in it.
fn find_fields<'t>(node: &'t Plain, out: &mut Vec<&'t Plain>) {
    for k in kids(node) {
        match name(k) {
            Some("field") => out.push(k),
            Some("fields specification" | "field list") => find_fields(k, out),
            _ => {}
        }
    }
}

/// The type of the numeric literal that `<integer>.<name>` spells, with an exponent's sign and
/// digits left to the enclosing `+` or `-`.
fn literal_continuation(source: &Plain, property: &str) -> Option<Ty> {
    let mut at = source;
    while name(at) != Some("unsigned numeric literal") {
        match kids(at).as_slice() {
            [only @ Plain::Def { .. }] => at = only,
            _ => return None,
        }
    }
    let digits = at.text();
    if digits.is_empty() || !digits.chars().all(|c| c.is_numeric() || c == '_') {
        return None;
    }
    let upper = property.to_uppercase();
    let exponent = upper.strip_prefix('E').map(|e| {
        let e = e.strip_suffix(['F', 'D', 'M']).unwrap_or(e);
        e.chars().all(|c| c.is_numeric() || c == '_')
    });
    match upper.as_str() {
        "M" => Some(Ty::Exact { int: true }),
        "F" | "D" => Some(Ty::Approx),
        _ if exponent == Some(true) => Some(if upper.ends_with('M') {
            Ty::Exact { int: false }
        } else {
            Ty::Approx
        }),
        _ => None,
    }
}

/// A <property reference> chain over a name, which reads as a catalog object parent and name.
fn dotted(node: &Plain) -> bool {
    let mut at = node;
    loop {
        match name(at) {
            Some("binding variable reference") => return true,
            Some("property reference") => match own(at, "property source") {
                Some(source) => at = source,
                None => return false,
            },
            _ => match kids(at).as_slice() {
                [only @ Plain::Def { .. }] => at = only,
                _ => return false,
            },
        }
    }
}

/// A double-quoted <character string literal> and nothing else, which reads as a <delimited
/// identifier> as well (21.3).
fn double_quoted(node: &Plain) -> bool {
    let mut at = node;
    loop {
        if name(at) == Some("character string literal") {
            return contains(at, "double quoted character sequence");
        }
        match kids(at).as_slice() {
            [only @ Plain::Def { .. }] => at = only,
            _ => return false,
        }
    }
}

/// Text that is a <null literal> whichever way it derives.
fn null_literal(node: &Plain) -> bool {
    let mut at = node;
    loop {
        if name(at) == Some("null literal") {
            return true;
        }
        match kids(at).as_slice() {
            [only @ Plain::Def { .. }] => at = only,
            _ => return false,
        }
    }
}

fn name(node: &Plain) -> Option<&str> {
    match node {
        Plain::Def { name, .. } => Some(name),
        _ => None,
    }
}

/// Children with desugaring groups flattened away.
fn kids(node: &Plain) -> Vec<&Plain> {
    fn flatten<'t>(children: &'t [Plain], out: &mut Vec<&'t Plain>) {
        for child in children {
            match child {
                Plain::Def {
                    synthetic: true,
                    children,
                    ..
                } => flatten(children, out),
                other => out.push(other),
            }
        }
    }
    let mut out = Vec::new();
    if let Plain::Def { children, .. } = node {
        flatten(children, &mut out);
    }
    out
}

fn own<'t>(node: &'t Plain, want: &str) -> Option<&'t Plain> {
    kids(node).into_iter().find(|c| name(c) == Some(want))
}

fn owns<'t>(node: &'t Plain, want: &str) -> Vec<&'t Plain> {
    kids(node)
        .into_iter()
        .filter(|c| name(c) == Some(want))
        .collect()
}

fn find<'t>(node: &'t Plain, want: &str, out: &mut Vec<&'t Plain>) {
    find_any(node, &[want], out)
}

/// Every `<want>` in `node`, in document order.
fn find_any<'t>(node: &'t Plain, want: &[&str], out: &mut Vec<&'t Plain>) {
    if let Plain::Def { name, children, .. } = node {
        if want.contains(&name.as_str()) {
            out.push(node);
        }
        children.iter().for_each(|c| find_any(c, want, out));
    }
}

fn first<'t>(node: &'t Plain, want: &str) -> Option<&'t Plain> {
    let mut found = Vec::new();
    find(node, want, &mut found);
    found.into_iter().next()
}

fn contains(node: &Plain, want: &str) -> bool {
    first(node, want).is_some()
}

fn keyword(node: &Plain, kw: &str) -> bool {
    matches!(node, Plain::Kw(t) if t.eq_ignore_ascii_case(kw))
}

/// The name `node` references when it is nothing but a <binding variable reference>.
fn bare(node: &Plain) -> Option<String> {
    let mut at = node;
    loop {
        if name(at) == Some("binding variable reference") {
            return Some(at.text());
        }
        match kids(at).as_slice() {
            [only @ Plain::Def { .. }] => at = only,
            _ => return None,
        }
    }
}

/// The name an <identifier> stands for: a delimited one without its quotes (21.3).
fn ident(node: &Plain) -> String {
    if !contains(node, "delimited identifier") {
        return node.text();
    }
    let mut reps = Vec::new();
    find_any(
        node,
        &[
            "double quoted character representation",
            "accent quoted character representation",
        ],
        &mut reps,
    );
    reps.iter()
        .map(|r| match r.text().as_str() {
            "\"\"" => "\"".to_string(),
            "``" => "`".to_string(),
            t => t.to_string(),
        })
        .collect()
}

/// The statements of a linear statement, its wrappers flattened away.
fn steps<'t>(node: &'t Plain, out: &mut Vec<&'t Plain>) {
    const WRAPPERS: &[&str] = &[
        "linear query statement",
        "focused linear query statement",
        "ambient linear query statement",
        "focused linear query statement part",
        "focused linear query and primitive result statement part",
        "focused primitive result statement",
        "focused nested query specification",
        "simple linear query statement",
        "linear data-modifying statement",
        "focused linear data-modifying statement",
        "focused linear data-modifying statement body",
        "focused nested data-modifying procedure specification",
        "ambient linear data-modifying statement",
        "ambient linear data-modifying statement body",
        "simple linear data-accessing statement",
        "simple data-accessing statement",
        "composite query primary",
    ];
    for k in kids(node) {
        match name(k) {
            Some(n) if WRAPPERS.contains(&n) => steps(k, out),
            Some(_) => out.push(k),
            None => {}
        }
    }
}

/// The statement inside the wrappers of a simple statement.
fn unwrap(mut node: &Plain) -> &Plain {
    const WRAPPERS: &[&str] = &[
        "simple query statement",
        "primitive query statement",
        "call query statement",
        "simple data-modifying statement",
        "primitive data-modifying statement",
        "call data-modifying procedure statement",
    ];
    while name(node).is_some_and(|n| WRAPPERS.contains(&n)) {
        match kids(node).into_iter().next() {
            Some(k) => node = k,
            None => break,
        }
    }
    node
}

/// The <linear query statement>s of a composite query expression, left to right.
fn conjuncts<'t>(cqe: &'t Plain, out: &mut Vec<&'t Plain>) {
    for k in kids(cqe) {
        match name(k) {
            Some("composite query expression") => conjuncts(k, out),
            Some("composite query primary") => out.extend(own(k, "linear query statement")),
            _ => {}
        }
    }
}
