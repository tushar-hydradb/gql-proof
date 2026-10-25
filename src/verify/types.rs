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
//!   CASE, COALESCE, list constructors, list concatenation and the columns of a composite query
//!   combine statically, 22.19, and a dynamic union type in a combination is reported, 22.19 SR
//!   2: right under GV65's absence, stricter than the text under it)
//! - the supported property value types (4.3.4) are, by hypothesis H2, the predefined types
//!   (boolean, string, numeric, temporal) and no others are known to be: a value SET as a
//!   property, a property type's value type (13.3 SR 3, 18.6-18.7 SR 4) is one of them, not the
//!   null or the empty type; a cast from the dynamic property value type (20.8 SR 10) reaches
//!   only what a predefined type casts to; the dynamic property value type holds values of
//!   non-comparable components (14.2 SR 10 a vii)
//! - a dynamic union type a cast targets takes only subtypes (20.8 SR 9), and nullability is not
//!   inferred, so a NOT NULL one takes nothing but is reported
//! - the null type (4.16.8) is a subtype of every nullable type, so it meets every "shall be"
//!   requirement on an operand; nullability is not otherwise inferred (4.17.4), only NULL itself
//!   is kept out of NOT NULL sites (10.3 SR 8, 20.8 SR 5)
//! - an operand of an unknown, open or dynamic type meets every requirement of an operator:
//!   4.14.4 lets the implementation cure it with type tests at run time
//! - a pattern or insert variable has an open node or edge type (IW011, IW012: with no catalog
//!   the open type is the one that holds every element), and its property the dynamic property
//!   value type (20.11 SR 3 b); a closed node or edge type comes from a <value type> (a CAST
//!   target, a declared type) and is followed through variables, lists, records and
//!   combinations; where it is not followed (different closed types combined) a property or a
//!   label of it is reported (20.11 SR 3 a, 16.8 SR 4 b ii)
//! - a graph's type is not followed, and a binding table's only as a nested query's columns: a
//!   closed declared type over any other initializer is reported (10.1-10.2 SR 8, 7.1 SR 6 c)
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
//!   (ID004), and the graph types a catalog gives
//! - lengths, precisions and maximum cardinalities of string, number and list types (so a
//!   subtype of a union's component is read by kind, 20.8 SR 9)
//!
//! A <value type> is read on its tree: `INT | STRING LIST` is a union with a list on one and a
//! list of a union on another (H3).

//! - grouping operations (22.15) and sort keys, whose operands are compared with themselves

use super::{Plain, Violation};
use std::collections::{BTreeMap, BTreeSet, HashMap};

use std::fmt;

/// Declared types, cut down to what the Syntax Rules distinguish.
#[derive(Debug, Clone, PartialEq)]
enum Ty {
    /// Unknown: what the environment (a parameter, a catalog object) or an implementation-defined
    /// choice gives, or what the checker does not model.
    Any,
    /// A dynamic union type (4.14).
    Dyn(Union),
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
    Node(Elem),
    Edge(Elem),
    Graph,
    Table,
}

/// The dynamic union types a declared type can be (4.14.3, 18.9 SR 80-88).
#[derive(Debug, Clone, PartialEq)]
enum Union {
    /// `ANY [VALUE]`, and the type of a property of an open record (20.11 SR 2 b): every value.
    Open,
    /// The dynamic property value type (4.3.4, 18.9 SR 82): its components are the supported
    /// property value types, which hypothesis H2 takes to include the predefined types and
    /// nothing else is known to (see `scalar`).
    Property,
    /// A <component type list> of these types (18.9 SR 84, 87).
    Closed(Vec<Ty>),
}

/// The constraining GQL-object type of a node or edge reference value type.
#[derive(Debug, Clone, PartialEq)]
enum Elem {
    /// An open graph element reference value type: a pattern or insert variable (IW011, IW012,
    /// read as open with no catalog), `NODE`, `EDGE`.
    Open,
    /// A closed one specified by a <node type specification> or <edge type specification>.
    Closed(Shape),
    /// Closed, or possibly closed, in a way the checker does not follow (a combination of
    /// different closed types, 22.19 SR 4 n v, IW019): every rule on it is reported.
    Unfollowed,
}

/// A node or edge type's label set and property types (18.2, 18.3, 18.4).
#[derive(Debug, Clone, PartialEq)]
struct Shape {
    labels: BTreeSet<String>,
    props: Fields,
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
            Ty::Any | Ty::Dyn(_) | Ty::Null | Ty::Nothing => return None,
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
            Ty::Node(_) => Class::Node,
            Ty::Edge(_) => Class::Edge,
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

    /// A predefined value type (18.9: boolean, string, numeric, temporal), the ones hypothesis H2
    /// takes to be supported property value types.
    fn scalar(&self) -> bool {
        matches!(
            self.class(),
            Some(
                Class::Bool
                    | Class::Numeric
                    | Class::Char
                    | Class::Bytes
                    | Class::Instant
                    | Class::Duration
            )
        )
    }
}

impl fmt::Display for Elem {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Elem::Open => Ok(()),
            Elem::Unfollowed => write!(f, " (a closed type not followed)"),
            Elem::Closed(s) => {
                let labels: Vec<&str> = s.labels.iter().map(String::as_str).collect();
                let props: Vec<String> = s.props.iter().map(|(n, t)| format!("{n} {t}")).collect();
                write!(f, " (:{} {{{}}})", labels.join("&"), props.join(", "))
            }
        }
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Ty::Any => write!(f, "unknown"),
            Ty::Dyn(Union::Open) => write!(f, "ANY"),
            Ty::Dyn(Union::Property) => write!(f, "ANY PROPERTY VALUE"),
            Ty::Dyn(Union::Closed(cs)) => {
                let cs: Vec<String> = cs.iter().map(Ty::to_string).collect();
                write!(f, "ANY<{}>", cs.join(" | "))
            }
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
            Ty::Node(e) => write!(f, "NODE{e}"),
            Ty::Edge(e) => write!(f, "EDGE{e}"),
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

/// Why a static combination fails.
enum Apart {
    /// SR 2: an input is a dynamic union type.
    Dynamic(Ty),
    /// SR 4: the inputs have no combination.
    Apart,
}

/// 22.19 without GV65 (22.18 SR 2): the static combination of `types`, if there is one.
///
/// SR 5 (the material variant when every input is material) is not inferred: every type the
/// checker computes stands for its nullable variant, and no rule here is read as needing a
/// material operand, so the nullable result is the stricter one.
fn combine(types: &[Ty]) -> Result<Ty, Apart> {
    let material: Vec<&Ty> = types
        .iter()
        .filter(|t| !matches!(t, Ty::Null | Ty::Nothing))
        .collect();
    // SR 2, read strictly: with GV65 (22.18 SR 3-5) a dynamic input is combined generally, but
    // the checker claims no feature, and without GV65 22.18 SR 2 applies 22.19 to every input
    if let Some(d) = material.iter().find(|t| matches!(t, Ty::Dyn(_))) {
        return Err(Apart::Dynamic((*d).clone()));
    }
    let Some(&first) = material.first() else {
        // SR 4 a
        return Ok(Ty::Null);
    };
    if material.contains(&&Ty::Any) {
        return Ok(Ty::Any);
    }
    let apart = Err(Apart::Apart);
    let all = |c: Class| material.iter().all(|t| t.class() == Some(c));
    let any = |t: &Ty| material.contains(&t);
    let class = first.class().ok_or(Apart::Apart)?;
    match class {
        // SR 4 d
        Class::Numeric if all(class) => Ok(if any(&Ty::Approx) {
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
                Ok(if any(&Ty::ZonedDatetime) {
                    Ty::ZonedDatetime
                } else {
                    Ty::LocalDatetime
                })
            } else if material.iter().all(time) {
                Ok(if any(&Ty::ZonedTime) {
                    Ty::ZonedTime
                } else {
                    Ty::LocalTime
                })
            } else if material.iter().all(|t| **t == Ty::Date) {
                Ok(Ty::Date)
            } else {
                apart
            }
        }
        // SR 4 h-i
        Class::Duration if all(class) => {
            let mut unit = None;
            for t in &material {
                if let Ty::Duration(Some(u)) = t {
                    if unit.is_some_and(|x| x != *u) {
                        return apart;
                    }
                    unit = Some(*u);
                }
            }
            Ok(Ty::Duration(unit))
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
            Ok(Ty::List {
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
                    _ => return apart,
                }
            }
            if closed.iter().any(|f| f.keys().ne(closed[0].keys())) {
                return apart;
            }
            let mut out = Fields::new();
            for n in closed[0].keys() {
                let types: Vec<Ty> = closed.iter().map(|f| f[n].clone()).collect();
                out.insert(n.clone(), combine(&types)?);
            }
            Ok(Ty::Record(Some(out)))
        }
        // SR 4 n v: a supertype of every input of the base type, chosen by IW019. A supertype of
        // an open type is open; of one closed type, that type is read; of different closed
        // types, it is not followed
        Class::Node | Class::Edge if all(class) => {
            let elems: Vec<&Elem> = material
                .iter()
                .filter_map(|t| match t {
                    Ty::Node(e) | Ty::Edge(e) => Some(e),
                    _ => None,
                })
                .collect();
            let elem = if elems.contains(&&Elem::Open) {
                Elem::Open
            } else if elems.iter().all(|e| *e == elems[0]) {
                elems[0].clone()
            } else {
                Elem::Unfollowed
            };
            Ok(match class {
                Class::Node => Ty::Node(elem),
                _ => Ty::Edge(elem),
            })
        }
        // SR 4 b, c, j, l, n
        _ if all(class) => Ok(first.clone()),
        _ => apart,
    }
}

/// Assignability of a value of `src` to a site of `tgt` (3.9.6, 4.14-4.16, 4.17.3).
fn assignable(src: &Ty, tgt: &Declared) -> bool {
    // 4.17.4.2: the nullabilities are assignment-aligned, so a known not nullable site takes a
    // known not nullable value. The checker infers no value known not nullable (every computed
    // type is its nullable variant, and IW022 inference is not assumed), so only NOTHING goes
    // to a NOT NULL site (reading).
    if !tgt.nullable && !matches!(src, Ty::Nothing) {
        return false;
    }
    match (src, &tgt.ty) {
        // a dynamic source: 4.14.4 lets the implementation test the value at run time
        (Ty::Any | Ty::Dyn(_) | Ty::Nothing, _) | (_, Ty::Any) => true,
        // 4.16.8: the null value only goes to a nullable site
        (Ty::Null, _) => tgt.nullable,
        (_, Ty::Null | Ty::Nothing) => false,
        // 4.14.3: a value goes to a dynamic union site when it goes to one of its components
        (_, Ty::Dyn(Union::Open)) => true,
        (s, Ty::Dyn(Union::Property)) => s.scalar(),
        (s, Ty::Dyn(Union::Closed(cs))) => cs.iter().any(|c| {
            assignable(
                s,
                &Declared {
                    ty: c.clone(),
                    nullable: true,
                },
            )
        }),
        // 4.16.7: the referent's type is the constraining type; an open or unknown source is not
        // known to be of a closed one
        (Ty::Node(s) | Ty::Edge(s), Ty::Node(t) | Ty::Edge(t)) if src.class() == tgt.ty.class() => {
            match t {
                Elem::Open => true,
                Elem::Closed(_) => s == t,
                Elem::Unfollowed => false,
            }
        }

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
        Ty::Any | Ty::Dyn(_) | Ty::Null | Ty::Nothing => CastClass::Dy,
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
        Ty::Node(_) => CastClass::Nr,
        Ty::Edge(_) => CastClass::Er,
        Ty::Table => CastClass::Tr,
    }
}

/// The predefined types standing for the dynamic property value type's components in a cast
/// from it (20.8 SR 10): hypothesis H2 takes the supported property value types to include the
/// predefined types; no other type is known to be one.
const PROPERTY_COMPONENTS: &[Ty] = &[
    Ty::Bool,
    Ty::Exact { int: false },
    Ty::Approx,
    Ty::Char,
    Ty::Bytes,
    Ty::Date,
    Ty::LocalTime,
    Ty::LocalDatetime,
    Ty::Duration(None),
];

/// 20.8 SR 9: every value of `s` is a value of the dynamic union type `u` (nullability aside):
/// `s` is a subtype of one of its components, or a union of such.
fn within(s: &Ty, u: &Union) -> bool {
    match (s, u) {
        (_, Union::Open) | (Ty::Null | Ty::Nothing, _) => true,
        (Ty::Dyn(Union::Property), Union::Property) => true,
        (Ty::Dyn(Union::Closed(ss)), _) => ss.iter().all(|c| within(c, u)),
        // unknown, or a union with components the target may lack
        (Ty::Any | Ty::Dyn(_), _) => false,
        (s, Union::Property) => s.scalar(),
        (s, Union::Closed(cs)) => cs.iter().any(|c| subtype(s, c)),
    }
}

/// `s` is a subtype of `t` (4.12, 4.14-4.16), nullability aside; lengths and precisions are
/// not modelled (the module's documented gap), so types of one kind are read as one type.
fn subtype(s: &Ty, t: &Ty) -> bool {
    match (s, t) {
        (Ty::Null | Ty::Nothing, _) => true,
        (_, Ty::Dyn(u)) => within(s, u),
        (Ty::Any | Ty::Dyn(_), _) => false,
        (
            Ty::List { elem, group },
            Ty::List {
                elem: te,
                group: tg,
            },
        ) => group == tg && subtype(elem, te),
        (Ty::Record(_), Ty::Record(None)) => true,
        (Ty::Record(Some(a)), Ty::Record(Some(b))) => {
            a.keys().eq(b.keys()) && a.iter().all(|(n, at)| subtype(at, &b[n]))
        }
        (Ty::Node(_), Ty::Node(Elem::Open)) | (Ty::Edge(_), Ty::Edge(Elem::Open)) => true,
        (Ty::Node(Elem::Unfollowed), _) | (Ty::Edge(Elem::Unfollowed), _) => false,
        _ => s == t,
    }
}

/// 20.8 SR 8-12: the rule a cast from `sd` to `td` breaks, if any, by Table 4 with the "M"
/// entries resolved by SR 9-12. Nullability is the caller's (SR 5, SR 9).
fn cast_fault(sd: &Ty, td: &Ty) -> Option<&'static str> {
    use CastClass::*;
    match (sd, td) {
        // SR 11 a: a regular list casts to a regular list only (not to PATH, not to a dynamic
        // union)
        (Ty::List { group: false, .. }, t) if !matches!(t, Ty::List { group: false, .. }) => {
            return Some("20.8 SR 11");
        }
        // SR 9
        (_, Ty::Dyn(u)) => return (!within(sd, u)).then_some("20.8 SR 9"),
        // SR 10: a component of the source casts to the target
        (Ty::Dyn(u), _) => {
            let some = match u {
                // 4.14.3: a largest supertype of every static base type
                Union::Open => true,
                Union::Property => PROPERTY_COMPONENTS
                    .iter()
                    .any(|c| cast_fault(c, td).is_none()),
                Union::Closed(cs) => cs.iter().any(|c| cast_fault(c, td).is_none()),
            };
            return (!some).then_some("20.8 SR 10");
        }
        _ => {}
    }
    let (s, t) = (cast_class(sd), cast_class(td));
    if s == Dy || t == Dy {
        // an unknown operand (the environment's, H1), or an immaterial one (SR 4, 5)
        return None;
    }
    let ok = match s {
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
            ) => {
                if !*group && *tg {
                    return Some("20.8 SR 8");
                }
                // SR 11 d: the element types; the generator does not follow them, the gate keeps
                // a breaking cast out (verify::GATE_ONLY).
                return cast_fault(elem, te).map(|_| "20.8 SR 11 d");
            }
            _ => false,
        },
        R => match (sd, td) {
            // SR 12
            (Ty::Record(Some(s)), Ty::Record(Some(t))) => {
                for (n, tt) in t {
                    match s.get(n) {
                        Some(st) => {
                            if let Some(rule) = cast_fault(st, tt) {
                                return Some(rule);
                            }
                        }
                        None => return Some("20.8 SR 8"),
                    }
                }
                true
            }
            _ => t == R,
        },
        P => t == P,
        Gr => t == Gr,
        Nr => matches!(t, P | Nr),
        Er => matches!(t, P | Er),
        Tr => matches!(t, P | Tr),
        Dy => true,
    };
    (!ok).then_some("20.8 SR 8")
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
    checker.value_types(tree);
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

    /// The rules on a <value type> wherever it is, a session command or a graph type
    /// included: 18.9 SR 68, 88; 18.6 SR 4, 18.7 SR 4.
    fn value_types(&mut self, node: &'t Plain) {
        match name(node) {
            // SR 68
            Some("list value type")
                if own(node, "list value type name")
                    .is_some_and(|n| kids(n).iter().any(|k| keyword(k, "GROUP"))) =>
            {
                if let Some(vt) = own(node, "value type")
                    && !element_reference(vt)
                {
                    self.report(
                        vt,
                        "18.9 SR 68",
                        format!("a group list of {}", value_type(vt).ty),
                    );
                }
            }
            // SR 88, nullability by SR 4, 85-86
            Some("component type list") => {
                let comps = owns(node, "component type");
                let material: Vec<bool> = comps.iter().map(|c| known_not_null(c)).collect();
                if material.iter().any(|m| *m) && material.iter().any(|m| !m) {
                    self.report(
                        node,
                        "18.9 SR 88",
                        "some components are known not nullable and some possibly nullable".into(),
                    );
                }
            }
            // 18.6 SR 4, 18.7 SR 4. Reading: H2 takes the predefined types to be supported
            // property value types and no others; the immaterial types are not (4.3.4)
            Some("property value type") => {
                let t = value_type(node).ty;
                if !t.scalar() {
                    let why = if matches!(t, Ty::Null | Ty::Nothing) {
                        format!("{t} is an immaterial value type")
                    } else {
                        format!("(reading) {t} is not known to be a supported property value type")
                    };
                    self.report(node, "18.7 SR 4", why.clone());
                    let at = self
                        .parent
                        .get(&(node as *const Plain))
                        .copied()
                        .unwrap_or(node);
                    self.report(at, "18.6 SR 4", why);
                }
            }
            _ => {}
        }
        for k in kids(node) {
            self.value_types(k);
        }
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
            // 7.1 SR 6 c: a typed graph or binding table session parameter; the other session
            // commands are unmodelled
            Some("session set graph parameter clause") => {
                if let Some(otgi) = own(node, "opt typed graph initializer") {
                    self.graph_initializer(otgi, &Env::default(), "7.1 SR 6");
                }
            }
            Some("session set binding table parameter clause") => {
                if let Some(otbti) = own(node, "opt typed binding table initializer") {
                    if own(otbti, "binding table reference value type").is_some() {
                        self.table_initializer(otbti, &Env::default(), "7.1 SR 6");
                    } else {
                        // Untyped, its body is still typed (found by the fifth review).
                        self.walk(otbti, &Env::new(Default::default()));
                    }
                }
            }
            // 7.1 SR 6 c iii 3 A I: the initializer of a typed value parameter is assignable
            Some("session set value parameter clause") => {
                let Some(otvi) = own(node, "opt typed value initializer") else {
                    return;
                };
                let env = Env::default();
                let Some(ve) =
                    own(otvi, "value initializer").and_then(|vi| own(vi, "value expression"))
                else {
                    return;
                };
                let t = self.ty(ve, &env);
                if let Some(vt) = own(otvi, "value type") {
                    let declared = value_type(vt);
                    if bounded_string(vt) {
                        self.report(
                            node,
                            "7.1 SR 6",
                            "(reading) a length-bounded string type is not known to take every value of the initializer".into(),
                        );
                    }
                    if !assignable(&t, &declared) {
                        self.report(
                            node,
                            "7.1 SR 6",
                            format!("{t} is not assignable to {declared}"),
                        );
                    }
                }
            }
            Some("session activity") => {
                kids(node).into_iter().for_each(|k| self.root(k));
                self.session_parameters(node);
            }
            Some("session set command" | "session set parameter clause") => {
                kids(node).into_iter().for_each(|k| self.root(k))
            }
            // 11.1 SR 3 and the rest: a session command's own expressions are typed too.
            Some("session set graph clause" | "session set schema clause" | "session set time zone clause") => {
                self.walk(node, &Env::new(Default::default()));
            }
            Some(n) if n.starts_with("session") => {}
            _ => kids(node).into_iter().for_each(|k| self.root(k)),
        }
    }

    /// 7.1 SR 6 d ii 1 B: a session parameter an earlier <session set command> of the program
    /// set takes, in a later one, a value type assignable to the declared type the earlier one
    /// gave it; by SR 6 d ii 1 C that is the first command's, whatever came between. Readings:
    /// the rule is applied whether or not the session already defines the parameter (SR 6 b, d i
    /// leave a defined one to the environment, H1); nullability is not inferred, so a type not
    /// declared NOT NULL does not go to a NOT NULL one; a closed graph or binding table type is
    /// matched only by the same written type.
    fn session_parameters(&mut self, activity: &'t Plain) {
        let mut clauses = Vec::new();
        find_any(
            activity,
            &[
                "session set graph parameter clause",
                "session set binding table parameter clause",
                "session set value parameter clause",
            ],
            &mut clauses,
        );
        // the declared type of each parameter, with the written type when closed
        let mut declared: HashMap<String, (Declared, Option<String>)> = HashMap::new();
        for clause in clauses {
            let Some(sps) = first(clause, "session parameter specification") else {
                continue;
            };
            let pn = first(sps, "parameter name").map_or_else(|| sps.text(), ident);
            let (pvt, closed) = self.parameter_value_type(clause);
            match declared.get(&pn) {
                None => {
                    declared.insert(pn, (pvt, closed));
                }
                Some((dt, dt_closed)) => {
                    let fine = match dt_closed {
                        Some(written) => closed.as_deref() == Some(written.as_str()),
                        None => {
                            assignable(&pvt.ty, dt)
                                && (dt.nullable || !pvt.nullable || matches!(pvt.ty, Ty::Nothing))
                        }
                    };
                    if !fine {
                        self.report(
                            clause,
                            "7.1 SR 6",
                            format!(
                                "(reading) ${pn} set as {pvt} is not known to be assignable to {dt}, its type from an earlier SESSION SET"
                            ),
                        );
                    }
                }
            }
        }
    }

    /// 7.1 SR 6 c: the value type PVT a session set parameter clause gives its parameter, and
    /// the written type when it is a closed graph or binding table type. An undeclared one is
    /// the initializer's type, nullable (4.17.4.3).
    fn parameter_value_type(&mut self, clause: &'t Plain) -> (Declared, Option<String>) {
        let env = Env::default();
        let unknown = |ty| Declared { ty, nullable: true };
        match name(clause) {
            Some("session set graph parameter clause") => {
                match first(clause, "graph reference value type") {
                    Some(grvt) => (
                        Declared {
                            ty: Ty::Graph,
                            nullable: !not_null(grvt),
                        },
                        contains(grvt, "closed graph reference value type").then(|| grvt.text()),
                    ),
                    None => (unknown(Ty::Graph), None),
                }
            }
            Some("session set binding table parameter clause") => {
                match first(clause, "binding table reference value type") {
                    Some(btrvt) => (
                        Declared {
                            ty: Ty::Table,
                            nullable: !not_null(btrvt),
                        },
                        Some(btrvt.text()),
                    ),
                    None => (unknown(Ty::Table), None),
                }
            }
            _ => {
                let Some(otvi) = own(clause, "opt typed value initializer") else {
                    return (unknown(Ty::Any), None);
                };
                if let Some(vt) = own(otvi, "value type") {
                    return (value_type(vt), None);
                }
                let t = own(otvi, "value initializer")
                    .and_then(|vi| own(vi, "value expression"))
                    .map_or(Ty::Any, |ve| {
                        if null_literal(ve) {
                            Ty::Null
                        } else {
                            // typed again here only for its type: the clause was checked once
                            let mut quiet = Checker {
                                parent: HashMap::new(),
                                out: Vec::new(),
                            };
                            quiet.ty(ve, &env)
                        }
                    });
                (unknown(t), None)
            }
        }
    }

    /// 10.1 SR 8 b i 1, 7.1 SR 6 c i 3 A I: the initializer's graph type is assignable to a
    /// declared graph reference value type. An open one (`ANY GRAPH`) takes every graph; the
    /// checker follows no graph's type, so a closed one is reported (reading).
    fn graph_initializer(&mut self, otgi: &'t Plain, env: &Env, rule: &'static str) {
        self.walk(otgi, env);
        let Some(grvt) = own(otgi, "graph reference value type") else {
            return;
        };
        if contains(grvt, "closed graph reference value type") {
            self.report(
                grvt,
                rule,
                "(reading) the initializer's graph type is not followed, so it is not known to be assignable to a closed graph reference value type".into(),
            );
        }
    }

    /// 10.2 SR 8 b i 1, 7.1 SR 6 c ii 3 A I: the initializer's binding table type is assignable
    /// to the declared binding table reference value type: when the initializer is a nested
    /// query whose columns are known, column name-equal and each column assignable; otherwise
    /// not followed and reported (reading).
    fn table_initializer(&mut self, otbti: &'t Plain, env: &Env, rule: &'static str) {
        let bte = own(otbti, "binding table initializer")
            .and_then(|bti| own(bti, "binding table expression"));
        let cols = match bte {
            Some(bte) => match own(bte, "nested binding table query specification")
                .and_then(|n| first(n, "procedure body"))
            {
                Some(pb) => self.body(
                    pb,
                    Scope {
                        record: env.vars.clone(),
                        table: Fields::new(),
                    },
                ),
                None => {
                    self.ty(bte, env);
                    None
                }
            },
            None => None,
        };
        let Some(btrvt) = own(otbti, "binding table reference value type") else {
            return;
        };
        let declared = table_fields(btrvt);
        match cols {
            None => self.report(
                btrvt,
                rule,
                "(reading) the initializer's binding table type is not followed, so it is not known to be assignable to the declared one".into(),
            ),
            Some(cols) => {
                if !cols.keys().eq(declared.keys()) {
                    let have: Vec<&String> = cols.keys().collect();
                    let want: Vec<&String> = declared.keys().collect();
                    self.report(
                        btrvt,
                        rule,
                        format!("columns {have:?} are not the declared columns {want:?}"),
                    );
                    return;
                }
                for (n, d) in &declared {
                    if !assignable(&cols[n], d) {
                        self.report(
                            btrvt,
                            rule,
                            format!("column {n} of type {} is not assignable to {d}", cols[n]),
                        );
                    }
                }
            }
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
                        match own(def, "opt typed graph initializer") {
                            Some(otgi) => self.graph_initializer(otgi, &env, "10.1 SR 8"),
                            None => self.walk(def, &env),
                        }
                        own(def, "binding variable").map(|bv| (bv.text(), Ty::Graph))
                    }
                    Some("binding table variable definition") => {
                        match own(def, "opt typed binding table initializer") {
                            Some(otbti)
                                if own(otbti, "binding table reference value type").is_some() =>
                            {
                                self.table_initializer(otbti, &env, "10.2 SR 8")
                            }
                            _ => self.walk(def, &env),
                        }
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

    /// 14.2: every operand sees the same scope (SR 8-9, 10 a ii-iii); with a query conjunction
    /// the result is the combined columns (SR 10 a vi, 4.13.3).
    fn composite(&mut self, cqe: &'t Plain, scope: Scope) -> Option<Fields> {
        let primary =
            own(cqe, "composite query primary").and_then(|p| own(p, "linear query statement"));
        let Some(qc) = own(cqe, "query conjunction") else {
            return primary.and_then(|lqs| self.linear(lqs, scope));
        };
        let left = own(cqe, "composite query expression")
            .and_then(|inner| self.composite(inner, scope.clone()));
        let right = primary.and_then(|lqs| self.linear(lqs, scope));
        let (Some(left), Some(right)) = (left, right) else {
            return None;
        };
        // SR 1: DISTINCT is implicit; SR 10 a vii: every set operator but UNION ALL
        let distinct = own(qc, "set operator").is_some_and(|so| {
            !(kids(so).iter().any(|k| keyword(k, "UNION"))
                && own(so, "set quantifier").is_some_and(|q| contains_kw(q, "ALL")))
        });
        let mut cols = Fields::new();
        for (n, lt) in &left {
            // column name-equality is `scope`'s (14.2 SR 10)
            let Some(rt) = right.get(n) else {
                continue;
            };
            // SR 10 a v: column-combinable is field type-combinable (4.10.3, 4.15.4): the
            // column types are comparable and have a combination (22.18)
            if !comparable(lt, rt) {
                self.report(
                    qc,
                    "14.2 SR 10",
                    format!("column {n}: {lt} and {rt} are not comparable"),
                );
            }
            let t = match combine(&[lt.clone(), rt.clone()]) {
                Ok(t) => t,
                Err(Apart::Dynamic(d)) => {
                    self.report(
                        qc,
                        "22.19 SR 2",
                        format!(
                            "(reading, without GV65) 14.2 SR 10: column {n} has the dynamic union type {d}"
                        ),
                    );
                    Ty::Any
                }
                Err(Apart::Apart) => {
                    self.report(
                        qc,
                        "14.2 SR 10",
                        format!("column {n}: {lt} and {rt} do not combine"),
                    );
                    Ty::Any
                }
            };
            // SR 10 a vii 1: no column of a union type with two non-comparable components; a
            // dynamic operand column makes the combined column dynamic (22.18 SR 3-5)
            if distinct {
                for t in [lt, rt] {
                    if let Ty::Dyn(u) = t
                        && !match u {
                            Union::Closed(cs) => {
                                cs.iter().all(|a| cs.iter().all(|b| comparable(a, b)))
                            }
                            // H2: the predefined types include non-comparable ones
                            Union::Open | Union::Property => false,
                        }
                    {
                        self.report(
                            qc,
                            "14.2 SR 10",
                            format!(
                                "column {n} has the dynamic union type {t}, with non-comparable components, under {}",
                                qc.text()
                            ),
                        );
                    }
                }
            }
            cols.insert(n.clone(), t);
        }
        Some(cols)
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
            Some("set statement") => {
                self.set_statement(node, &Env::new(scope.merged()));
                scope
            }
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
        // 21.2 SR 67: a NULL to a declared type DT is CAST(NULL AS DT), which 20.8 SR 4 refuses
        // for an immaterial DT (the null type, the empty type).
        if matches!(declared.ty, Ty::Null | Ty::Nothing) || contains(vt, "immaterial value type") {
            self.report(
                def,
                "20.8 SR 4",
                format!("a declared {} type: its initializer is cast to an immaterial type", declared.ty),
            );
        }
        // SR 8 b i 1, by 4.16.x a type is assignable when every value of it is: a character or
        // byte string type bounded in length (CHAR, BINARY, any written length) is not known
        // to take every value of the initializer, whose length is not followed (reading).
        if bounded_string(vt) {
            self.report(
                def,
                "10.3 SR 8",
                "(reading) a length-bounded string type is not known to take every value of the initializer".into(),
            );
        }
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

    /// 13.3 SR 3 a iv, b iii 2: a value set as a property has a supported property value type.
    /// Reading: H2 takes the predefined types to be supported property value types and no
    /// others; the null type and the empty type are not (4.3.4: material); an unknown or a
    /// dynamic value is tested at run time (4.14.4). And SR 3 a v, b iii 3: a property of a
    /// closed type names one of its property types.
    fn set_statement(&mut self, ss: &'t Plain, env: &Env) {
        let mut items = Vec::new();
        find_any(
            ss,
            &["set property item", "set all properties item"],
            &mut items,
        );
        for item in items {
            let bt = own(item, "binding variable reference").map(|b| self.ty(b, env));
            let mut pairs: Vec<(String, &'t Plain)> = Vec::new();
            if name(item) == Some("set property item") {
                if let Some(ve) = own(item, "value expression") {
                    pairs.push((
                        own(item, "property name").map(ident).unwrap_or_default(),
                        ve,
                    ));
                }
            } else {
                let mut kvs = Vec::new();
                find(item, "property key value pair", &mut kvs);
                for kv in kvs {
                    if let Some(ve) = own(kv, "value expression") {
                        pairs.push((own(kv, "property name").map(ident).unwrap_or_default(), ve));
                    }
                }
            }
            for (pn, ve) in pairs {
                let t = if null_literal(ve) {
                    Ty::Null
                } else {
                    self.ty(ve, env)
                };
                if !(t.scalar() || matches!(t, Ty::Any | Ty::Dyn(_))) {
                    self.report(
                        ve,
                        "13.3 SR 3",
                        format!(
                            "(reading) {pn} is set to {t}, not a supported property value type"
                        ),
                    );
                }
                match &bt {
                    Some(Ty::Node(Elem::Closed(s)) | Ty::Edge(Elem::Closed(s)))
                        if !s.props.contains_key(&pn) =>
                    {
                        self.report(item, "13.3 SR 3", format!("no property type {pn}"));
                    }
                    Some(Ty::Node(Elem::Unfollowed) | Ty::Edge(Elem::Unfollowed)) => self.report(
                        item,
                        "13.3 SR 3",
                        format!("(reading) whether {pn} is a property type is not known"),
                    ),
                    _ => {}
                }
            }
        }
    }

    /// 13.2: an insert pattern binds its new element variables.
    fn insert(&mut self, is: &'t Plain, mut scope: Scope) -> Scope {
        let incoming = scope.merged();
        self.walk(is, &Env::new(incoming.clone()));
        // 16.5 SR 6 c: an inserted property's value has a supported property value type; as
        // for SET (13.3 SR 3), the predefined scalars (H2), a dynamic one under the 4.14.4 cure.
        let mut kvs = Vec::new();
        find(is, "property key value pair", &mut kvs);
        for kv in kvs {
            if let Some(ve) = own(kv, "value expression") {
                let t = if null_literal(ve) {
                    Ty::Null
                } else {
                    self.ty(ve, &Env::new(incoming.clone()))
                };
                if !(t.scalar() || matches!(t, Ty::Any | Ty::Dyn(_))) {
                    self.report(
                        ve,
                        "16.5 SR 6",
                        format!("(reading) an inserted property of {t}, not a supported property value type"),
                    );
                }
            }
        }
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
                Some("insert edge pattern") => Ty::Edge(Elem::Open),
                _ => Ty::Node(Elem::Open),
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
        // 14.12 SR 27 b-c: a body is a USE and MATCH, or a nested query, ahead of the items
        let mut scope = scope.clone();
        if let Some(body) = own(sel, "select statement body") {
            if let Some(list) = own(body, "select graph match list") {
                for gm in owns(list, "select graph match") {
                    if let Some(ge) = own(gm, "graph expression") {
                        self.ty(ge, &Env::new(scope.record.clone()));
                    }
                    if let Some(ms) = own(gm, "match statement") {
                        scope = self.match_statement(ms, scope);
                    }
                }
            } else if let Some(qs) = own(body, "select query specification") {
                if let Some(ge) = own(qs, "graph expression") {
                    self.ty(ge, &Env::new(scope.record.clone()));
                }
                let cols = own(qs, "nested query specification")
                    .and_then(|n| first(n, "procedure body"))
                    .and_then(|pb| self.body(pb, scope.clone()));
                if let Some(cols) = cols {
                    scope.table.extend(cols);
                }
            }
        }
        let env = Env::new(scope.merged());
        let mut cols = Fields::new();
        if own(sel, "asterisk").is_some() {
            cols = scope.table.clone();
        }
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
        self.walk_except(sel, &env, &["select item list", "select statement body"]);
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
                // 14.11 SR 10 a ii as Cor 1 has it: no item is both grouping (its alias is a
                // grouping element) and aggregating
                let mut refs = Vec::new();
                find(gbc, "binding variable reference", &mut refs);
                let grouping: Vec<String> = refs.into_iter().map(Plain::text).collect();
                for item in own(body, "return item list")
                    .map(|l| owns(l, "return item"))
                    .unwrap_or_default()
                {
                    let Some(ave) = own(item, "aggregating value expression") else {
                        continue;
                    };
                    let alias = own(item, "return item alias")
                        .and_then(|a| own(a, "identifier"))
                        .map(ident)
                        .or_else(|| bare(ave));
                    if let Some(n) = alias
                        && grouping.contains(&n)
                        && directly(ave, "aggregate function")
                    {
                        self.report(
                            item,
                            "14.11 SR 10",
                            format!("{n} is both a grouping and an aggregating item"),
                        );
                    }
                }
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
                    let t = self.element(evr, env, ELEMENT, "16.10 SR 3");
                    if let Some(part) = own(node, "labeled predicate part 2") {
                        self.labels(part, &t);
                    }
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
                        // H3: the tree's own form, character or byte string.
                        let class = if n == "substring function" { Class::Char } else { Class::Bytes };
                        self.expect(s, &t, &[class], "20.23 SR 2, 4");
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
            // 20.1 SR 2, 3 on this tree's derivation: a <value expression primary> that derives
            // as a graph (binding table) reference value expression has a graph (binding table)
            // type; an unknown, dynamic or null one passes (4.14.4), as everywhere
            "graph reference value expression" | "binding table reference value expression" => {
                let Some(primary) = own(node, "value expression primary") else {
                    return Ty::Any;
                };
                let t = self.ty(primary, env);
                let (class, rule) = if n == "graph reference value expression" {
                    (Class::Graph, "20.1 SR 2")
                } else {
                    (Class::Table, "20.1 SR 3")
                };
                self.expect(primary, &t, &[class], rule);
                t
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
            Ok(t) => t,
            Err(Apart::Dynamic(d)) => {
                self.report(
                    at,
                    "22.19 SR 2",
                    format!(
                        "(reading, without GV65) {rule}: {d} is a dynamic union type in a static combination"
                    ),
                );
                Ty::Any
            }
            Err(Apart::Apart) => {
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
            // CASE WHEN V1 = V2 THEN NULL ELSE V1 END: 20.7 SR 3 when V1 is NULL
            if operands.first().is_some_and(|v| null_literal(v)) {
                self.report(
                    ca,
                    "20.7 SR 3",
                    "NULLIF of NULL: every <result> is NULL".into(),
                );
            }
            if types.len() == 2 && !comparable(&types[0], &types[1]) {
                self.report(
                    ca,
                    "22.13 CR 1",
                    format!("{} and {} are not comparable", types[0], types[1]),
                );
            }
            // 20.7 SR 1 b: the CASE's one result expression is V1, its type the combination
            // of {V1} (22.19 SR 2: no dynamic one, the strict reading).
            let first = types.into_iter().next().unwrap_or(Ty::Any);
            return self.combined(ca, &[first], "20.7 SR 5");
        }
        // COALESCE (.., Vn-1, Vn) ends in CASE WHEN NOT Vn-1 IS NULL THEN Vn-1 ELSE Vn END
        if let [.., a, b] = operands.as_slice()
            && null_literal(a)
            && null_literal(b)
        {
            self.report(
                ca,
                "20.7 SR 3",
                "COALESCE ending in two NULLs: every <result> of its last CASE is NULL".into(),
            );
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
            Some("labeled predicate part 2") => {
                self.case_element(co, ct, ELEMENT, "16.10 SR 3");
                self.labels(inner, ct);
            }
            Some("source predicate part 2" | "destination predicate part 2") => {
                self.case_element(co, ct, &[Class::Node], "19.10 SR 2");
                if let Some(er) = first(inner, "edge reference") {
                    self.element(kids(er)[0], env, &[Class::Edge], "19.10 SR 3");
                }
            }
            _ => {}
        }
    }

    /// 16.8 SR 4 b ii: the labels a <labeled predicate part 2> names on a value of type `t` are
    /// labels of its constraining type when that is closed.
    fn labels(&mut self, part: &Plain, t: &Ty) {
        let elem = match t {
            Ty::Node(e) | Ty::Edge(e) => e,
            Ty::List { elem, group: true } => match &**elem {
                Ty::Node(e) | Ty::Edge(e) => e,
                _ => return,
            },
            _ => return,
        };
        let mut names = Vec::new();
        find(part, "label name", &mut names);
        for n in names {
            let label = ident(n);
            match elem {
                Elem::Open => {}
                Elem::Closed(shape) if shape.labels.contains(&label) => {}
                Elem::Closed(_) => self.report(n, "16.8 SR 4", format!("{t} has no label {label}")),
                Elem::Unfollowed => self.report(
                    n,
                    "16.8 SR 4",
                    format!("(reading) whether {t} has label {label} is not known"),
                ),
            }
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
        // SR 4, read strictly: TD specifies every type it contains, so no immaterial type
        // anywhere in it (`NOTHING LIST`, `NULL | PATH`)
        if matches!(td.ty, Ty::Null | Ty::Nothing) || contains(target, "immaterial value type") {
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
            return td.ty;
        }
        if matches!(td.ty, Ty::Dyn(_)) && !td.nullable {
            // SR 9 with nullability (4.17.4.2): a material union has only material subtypes, and
            // a declared type is nullable unless a rule says otherwise (4.17.4.3), which the
            // checker does not infer
            self.report(
                cs,
                "20.8 SR 9",
                format!("(reading) {sd} is not known to be material, cast to {td}"),
            );
        }
        match cast_fault(&sd, &td.ty) {
            Some(rule @ "20.8 SR 9") => self.report(
                cs,
                rule,
                format!("{sd} is not known to be a subtype of {td}"),
            ),

            Some(rule @ "20.8 SR 10") => self.report(
                cs,
                rule,
                format!("no component of {sd} casts to {td} (reading: H2 takes only the predefined types to be supported property value types)"),
            ),
            Some(rule) => self.report(cs, rule, format!("no cast from {sd} to {td}")),
            None => {}
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
            // SR 2 b: the open dynamic union type
            Ty::Record(None) => Ty::Dyn(Union::Open),
            // SR 3 b: the dynamic property value type
            Ty::Node(Elem::Open) | Ty::Edge(Elem::Open) => Ty::Dyn(Union::Property),
            // SR 3 a
            Ty::Node(Elem::Closed(shape)) | Ty::Edge(Elem::Closed(shape)) => {
                match shape.props.get(&pn) {
                    Some(t) => t.clone(),
                    None => {
                        self.report(pr, "20.11 SR 3", format!("{psd} has no property type {pn}"));
                        Ty::Any
                    }
                }
            }
            Ty::Node(Elem::Unfollowed) | Ty::Edge(Elem::Unfollowed) => {
                self.report(
                    pr,
                    "20.11 SR 3",
                    format!(
                        "(reading) {pn} of {psd}: whether it names a property type is not known"
                    ),
                );
                Ty::Any
            }
            // a property of a dynamic value: dynamic (4.14.4)
            Ty::Dyn(_) => Ty::Dyn(Union::Open),

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
        // H3: the tree's own form; a byte string trim function takes bytes, the others
        // character strings.
        let classes: &[Class] = if name(f) == Some("byte string trim function") {
            &[Class::Bytes]
        } else {
            &[Class::Char]
        };
        let rule = if name(f) == Some("multi-character trim function") {
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

/// 18.9: the value type a <value type> (or a <cast target>) specifies, on this tree (`A | B
/// LIST` is a union with a list on one tree and a list of a union on another, H3).
fn value_type(node: &Plain) -> Declared {
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
        Some("open node reference value type") => Ty::Node(Elem::Open),
        Some("open edge reference value type") => Ty::Edge(Elem::Open),
        Some("closed node reference value type") => {
            Ty::Node(Elem::Closed(shape(node, "node type filler")))
        }
        Some("closed edge reference value type") => {
            Ty::Edge(Elem::Closed(shape(node, "edge type filler")))
        }
        // SR 80, 83
        Some("open dynamic union type") => Ty::Dyn(Union::Open),
        // SR 82
        Some("dynamic property value type") => Ty::Dyn(Union::Property),
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
        // SR 84-87; 4.14.3: a union of one component type is that type
        Some("closed dynamic union type") => {
            let mut comps = Vec::new();
            if let Some(list) = own(node, "component type list") {
                comps = owns(list, "component type");
            }
            if let [only] = comps.as_slice() {
                return value_type(only);
            }
            let comps: Vec<Declared> = comps.into_iter().map(value_type).collect();
            return Declared {
                nullable: comps.iter().any(|c| c.nullable),
                ty: Ty::Dyn(Union::Closed(comps.into_iter().map(|c| c.ty).collect())),
            };
        }
        _ => match kids(node).as_slice() {
            [only @ Plain::Def { .. }] => return value_type(only),
            _ => Ty::Any,
        },
    };
    let nullable = nullable && ty != Ty::Nothing;
    Declared { ty, nullable }
}

/// The label set and property types of the node or edge type a <node type specification> or
/// <edge type specification> specifies: the labels and property types of its own `filler`
/// (an edge's endpoints have fillers of their own kind).
fn shape(node: &Plain, filler: &str) -> Shape {
    let mut labels = BTreeSet::new();
    let mut props = Fields::new();
    if let Some(f) = first(node, filler) {
        let mut names = Vec::new();
        find_outside(f, "label name", "property types specification", &mut names);
        labels = names.into_iter().map(ident).collect();
        let mut types = Vec::new();
        find(f, "property type", &mut types);
        // the outermost first: a property type's own value type may hold property types
        let mut seen: Vec<&Plain> = Vec::new();
        for pt in types {
            if seen.iter().any(|o| first_ptr(o, pt)) {
                continue;
            }
            seen.push(pt);
            let n = own(pt, "property name").map(ident).unwrap_or_default();
            let t = own(pt, "property value type").map_or(Ty::Any, |v| value_type(v).ty);
            props.insert(n, t);
        }
    }
    Shape { labels, props }
}

/// `inner` is a node of `outer`'s subtree other than `outer`.
fn first_ptr(outer: &Plain, inner: &Plain) -> bool {
    kids(outer)
        .into_iter()
        .any(|k| std::ptr::eq(k, inner) || first_ptr(k, inner))
}

/// Every `<want>` in `node` that is not inside a `<fence>`.
fn find_outside<'t>(node: &'t Plain, want: &str, fence: &str, out: &mut Vec<&'t Plain>) {
    if let Plain::Def { name, children, .. } = node {
        if name == want {
            out.push(node);
        }
        if name != fence {
            children
                .iter()
                .for_each(|c| find_outside(c, want, fence, out));
        }
    }
}

/// The columns a <binding table reference value type> declares (18.9, 18.10).
fn table_fields(btrvt: &Plain) -> BTreeMap<String, Declared> {
    let mut out = BTreeMap::new();
    if let Some(spec) = first(btrvt, "field types specification") {
        let mut items = Vec::new();
        find(spec, "field type", &mut items);
        let mut seen: Vec<&Plain> = Vec::new();
        for f in items {
            if seen.iter().any(|o| first_ptr(o, f)) {
                continue;
            }
            seen.push(f);
            let fname = own(f, "field name").map(ident).unwrap_or_default();
            let d = own(f, "value type").map_or(
                Declared {
                    ty: Ty::Any,
                    nullable: true,
                },
                value_type,
            );
            out.insert(fname, d);
        }
    }
    out
}

/// A <value type> that specifies a node or an edge reference value type (18.9 SR 68): one that
/// derives as one, not a union of them.
fn element_reference(vt: &Plain) -> bool {
    let mut at = vt;
    loop {
        match name(at) {
            Some("node reference value type" | "edge reference value type") => return true,
            Some("dynamic union type") => return false,
            _ => {}
        }
        match kids(at)
            .into_iter()
            .filter(|k| matches!(k, Plain::Def { .. }))
            .collect::<Vec<_>>()
            .as_slice()
        {
            [only] => at = only,
            _ => return false,
        }
    }
}

/// 18.9 SR 4, 85, 86: a <value type> (or <component type>) specifies known not nullable.
fn known_not_null(vt: &Plain) -> bool {
    let mut at = vt;
    loop {
        match name(at) {
            Some("closed dynamic union type") => {
                return own(at, "component type list")
                    .is_some_and(|l| owns(l, "component type").iter().all(|c| known_not_null(c)));
            }
            Some("empty type") => return true,
            _ => {}
        }
        match kids(at)
            .into_iter()
            .filter(|k| matches!(k, Plain::Def { .. }))
            .collect::<Vec<_>>()
            .as_slice()
        {
            [only] if !matches!(name(only), Some("not null")) => at = only,
            _ => return not_null(at),
        }
    }
}

/// `node` holds a `<want>` outside any nested <procedure body>.
fn directly(node: &Plain, want: &str) -> bool {
    match node {
        Plain::Def { name, .. } if name == want => true,
        Plain::Def { name, .. } if name == "procedure body" => false,
        Plain::Def { children, .. } => children.iter().any(|c| directly(c, want)),
        _ => false,
    }
}

fn contains_kw(node: &Plain, kw: &str) -> bool {
    match node {
        Plain::Kw(_) => keyword(node, kw),
        Plain::Def { children, .. } => children.iter().any(|c| contains_kw(c, kw)),
        _ => false,
    }
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
                pattern_vars(k, Some(Ty::Node(Elem::Open)), group, out);
            }
        }
        Some("edge pattern") => {
            for k in kids(node) {
                pattern_vars(k, Some(Ty::Edge(Elem::Open)), group, out);
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

/// A character or byte string type bounded in length: a written length, or CHAR and BINARY,
/// whose fixed length 1 is implicit (18.9 SR 11). STRING, VARCHAR, BYTES and VARBINARY without a
/// length take the implementation's maximum, which every string of the implementation fits (H2).
fn bounded_string(vt: &Plain) -> bool {
    let mut types = Vec::new();
    find_any(vt, &["character string type", "byte string type"], &mut types);
    types.iter().any(|t| {
        contains(t, "min length")
            || contains(t, "max length")
            || contains(t, "fixed length")
            || kids(t).iter().any(|k| keyword(k, "CHAR") || keyword(k, "BINARY"))
    })
}
