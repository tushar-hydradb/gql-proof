//! The reference evaluator for the pattern core (theorem 2 of
//! `research/oracle-witness-2026-10-23.md`): a query run on a finite graph by the general
//! rules, literally. Patterns follow 22.3 (local matches by concatenation, union and power of
//! sets of path bindings), 22.2 (consistency, REDUCE), 22.4 (selective patterns), 16.4 (the
//! match), 16.3 (the binding table); statements follow clause 14; expressions follow clauses
//! 19 and 20 for a core of literal classes.
//!
//! Where the rules leave something to the implementation (which N paths ANY keeps, the order
//! of ties under SHORTEST k, SESSION_USER, ELEMENT_ID's spelling, the current time) or where
//! this evaluator does not reach yet, it stops with `Stop::Unsupported` and the reason, and
//! the record falls back to the witness tier. A data exception the rules raise is
//! `Stop::Exception` with its class, and is the expected outcome.

use super::{
    EdgeKind, Graph, LabelExpr, Mode, Value, child, declared, def_name, edge_kind, exactly,
    find_all, has_kw, identifier, label_expr, literal, logical, path_mode, simplified_kind,
    simplified_label, unsigned,
};
use crate::MatchModeDefault;
use crate::verify::Plain;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

/// A value of the evaluator.
#[derive(Clone, Debug, PartialEq, Serialize)]
#[serde(tag = "kind", content = "value")]
pub enum Val {
    Null,
    Bool(bool),
    Int(i128),
    Float(f64),
    Str(String),
    Node(usize),
    Edge(usize),
    /// Nodes and edges alternating, by id.
    Path(Vec<usize>),
    List(Vec<Val>),
    Record(BTreeMap<String, Val>),
    /// A value the rules leave to the implementation or the clock (SESSION_USER,
    /// CURRENT_DATE, a temporal or byte string literal): known to be non-null and to raise
    /// nothing, never compared or returned.
    Opaque(String),
}

impl Val {
    fn has_opaque(&self) -> bool {
        match self {
            Val::Opaque(_) => true,
            Val::List(l) => l.iter().any(Val::has_opaque),
            Val::Record(r) => r.values().any(Val::has_opaque),
            _ => false,
        }
    }

    fn from_ir(v: &Value) -> Val {
        match v {
            Value::Null => Val::Null,
            Value::Bool(b) => Val::Bool(*b),
            Value::Int(i) => Val::Int(*i),
            Value::Float(f) => Val::Float(*f),
            Value::Str(s) => Val::Str(s.clone()),
        }
    }

    fn is_null(&self) -> bool {
        matches!(self, Val::Null)
    }

    /// A canonical form for set semantics (DISTINCT, deduplication of matches).
    fn key(&self) -> String {
        serde_json::to_string(self).unwrap_or_default()
    }
}

/// Why evaluation stopped: outside the evaluator, or a data exception the rules raise.
#[derive(Clone, Debug, PartialEq)]
pub enum Stop {
    Unsupported(String),
    Exception(String),
}

fn unsupported<T>(why: impl Into<String>) -> R<T> {
    Err(Stop::Unsupported(why.into()))
}

type R<T> = Result<T, Stop>;
pub type Row = BTreeMap<String, Val>;

#[derive(Clone, Debug, Serialize)]
pub struct Table {
    pub rows: Vec<Row>,
    /// Whether row order is part of the result (an `ORDER BY` last).
    pub ordered: bool,
}

/// What a query does on the graph.
#[derive(Clone, Debug)]
pub enum Outcome {
    /// Status 00000 or 00001, with a result table.
    Table(Table),
    /// Status 00000 or 00001, no result (`FINISH`).
    NoResult,
    /// A data exception of this class.
    Exception(String),
}

/// Evaluates the whole sentence on `graph`; `Err` with the reason where the evaluator does
/// not reach.
pub fn evaluate(
    tree: &Plain,
    graph: &Graph,
    params: &BTreeMap<String, Value>,
    mode: MatchModeDefault,
) -> Result<Outcome, String> {
    let params: BTreeMap<String, Val> = params.iter().map(|(k, v)| (k.clone(), Val::from_ir(v))).collect();
    let env = Env { graph, params: &params, mode, observing: false, group: Default::default() };
    env.run(tree)
}

/// The same with a final `FINISH` read as `RETURN *`: the working table the query had when
/// it finished, for the observation query of a `FINISH` sentence.
pub fn evaluate_observing(
    tree: &Plain,
    graph: &Graph,
    params: &BTreeMap<String, Value>,
    mode: MatchModeDefault,
) -> Result<Outcome, String> {
    let params: BTreeMap<String, Val> = params.iter().map(|(k, v)| (k.clone(), Val::from_ir(v))).collect();
    let env = Env { graph, params: &params, mode, observing: true, group: Default::default() };
    env.run(tree)
}

struct Env<'a> {
    graph: &'a Graph,
    params: &'a BTreeMap<String, Val>,
    mode: MatchModeDefault,
    /// A final FINISH returns the working table instead of nothing.
    observing: bool,
    /// The members of the group a RETURN item is evaluated over, while it is.
    group: std::cell::RefCell<Option<Vec<Row>>>,
}

impl Env<'_> {
    fn run(&self, tree: &Plain) -> Result<Outcome, String> {
        let mut blocks = Vec::new();
        find_all(tree, "procedure body", &mut blocks);
        let Some(body) = blocks.first() else {
            return Err("no procedure body".to_string());
        };
        match self.procedure_body(body, &Table { rows: vec![Row::new()], ordered: false }) {
            Ok(Some(table)) => Ok(Outcome::Table(table)),
            Ok(None) => Ok(Outcome::NoResult),
            Err(Stop::Exception(status)) => Ok(Outcome::Exception(status)),
            Err(Stop::Unsupported(why)) => Err(why),
        }
    }
}

// ---------------------------------------------------------------------------------------------
// statements (clause 14)

impl Env<'_> {
    /// A procedure body on an incoming table: the statement block, each statement on the
    /// table the previous one left. `None` is an omitted result (`FINISH` last).
    fn procedure_body(&self, body: &Plain, incoming: &Table) -> R<Option<Table>> {
        if child(body, "at schema clause").is_some() {
            return unsupported("a procedure body with AT SCHEMA");
        }
        // 9.x: the definitions amend the working record; every row of the incoming table
        // gets the fields.
        let mut incoming = incoming.clone();
        if let Some(defs) = child(body, "binding variable definition block") {
            let mut definitions = Vec::new();
            find_all(defs, "binding variable definition", &mut definitions);
            for d in definitions {
                let Some(vvd) = child(d, "value variable definition") else {
                    return unsupported("a graph or binding table variable definition");
                };
                let (name, expr, declared_type) = self.value_definition(vvd)?;
                let mut rows = Vec::new();
                for row in incoming.rows {
                    let mut row = row;
                    let v = self.eval(expr, &row)?;
                    if let Some(t) = &declared_type {
                        check_declared_type(&v, t)?;
                    }
                    row.insert(name.clone(), v);
                    rows.push(row);
                }
                incoming.rows = rows;
            }
        }
        let incoming = &incoming;
        let Some(block) = child(body, "statement block") else {
            return unsupported("no statement block");
        };
        let mut statements = Vec::new();
        for c in logical(block) {
            match def_name(c) {
                Some("statement") => statements.push((None, c)),
                Some("next statement") => {
                    let yield_clause = child(c, "yield clause");
                    let Some(s) = child(c, "statement") else { continue };
                    statements.push((yield_clause, s));
                }
                _ => {}
            }
        }
        let mut table = Some(incoming.clone());
        let last = statements.len().saturating_sub(1);
        for (i, (yield_clause, s)) in statements.into_iter().enumerate() {
            let Some(current) = table.take() else {
                // FINISH gave no table; what follows works on the unit table (14.x: an
                // omitted result makes the next incoming table the unit table).
                table = Some(Table { rows: vec![Row::new()], ordered: false });
                continue;
            };
            let current = match yield_clause {
                Some(y) => self.yield_clause(y, current)?,
                None => current,
            };
            let before = current.clone();
            table = self.statement(s, current)?;
            if table.is_none() && self.observing && i == last {
                // RETURN * of the table FINISH would have dropped, after this statement's
                // own simple query statements.
                return Ok(Some(self.observed_table(s, before)?));
            }
        }
        Ok(table)
    }

    /// The working table just before a final FINISH: the statement's simple query
    /// statements run on `incoming`.
    fn observed_table(&self, s: &Plain, incoming: Table) -> R<Table> {
        let mut table = incoming;
        let mut simples = Vec::new();
        find_all(s, "simple query statement", &mut simples);
        // Only the top level linear query's statements: those under a nested query or an
        // EXISTS are inside expressions, which `find_all` does not enter past a match.
        for q in simples {
            table = self.simple_query(q, table)?;
        }
        Ok(table)
    }

    fn yield_clause(&self, y: &Plain, table: Table) -> R<Table> {
        let mut items = Vec::new();
        find_all(y, "yield item", &mut items);
        let mut map: Vec<(String, String)> = Vec::new();
        for item in items {
            let Some(name) = child(item, "yield item name") else { continue };
            let from = identifier(name);
            let to = child(item, "yield item alias")
                .and_then(|a| child(a, "binding variable"))
                .map(identifier)
                .unwrap_or_else(|| from.clone());
            map.push((from, to));
        }
        let rows = table
            .rows
            .iter()
            .map(|r| {
                map.iter()
                    .map(|(from, to)| (to.clone(), r.get(from).cloned().unwrap_or(Val::Null)))
                    .collect()
            })
            .collect();
        Ok(Table { rows, ordered: table.ordered })
    }

    /// One `<statement>`: a linear query (its simple query statements then its result
    /// statement). Composite, catalog and data modifying statements are not reached.
    fn statement(&self, s: &Plain, incoming: Table) -> R<Option<Table>> {
        let Some(composite) = child(s, "composite query statement") else {
            return unsupported(format!("a statement that is not a query: {}", head(s)));
        };
        let Some(expr) = child(composite, "composite query expression") else {
            return unsupported("no composite query expression");
        };
        self.composite(expr, incoming)
    }

    fn composite(&self, expr: &Plain, incoming: Table) -> R<Option<Table>> {
        let kids = logical(expr);
        if kids.iter().any(|k| matches!(k, Plain::Kw(k) if k == "UNION" || k == "EXCEPT" || k == "INTERSECT" || k == "OTHERWISE")) {
            return unsupported("a composite query (UNION, EXCEPT, INTERSECT, OTHERWISE)");
        }
        let Some(primary) = child(expr, "composite query primary") else {
            return unsupported("no composite query primary");
        };
        let Some(linear) = child(primary, "linear query statement") else {
            return unsupported("no linear query statement");
        };
        self.linear(linear, incoming)
    }

    fn linear(&self, linear: &Plain, incoming: Table) -> R<Option<Table>> {
        if child(linear, "focused linear query statement").is_some() {
            return unsupported("a focused linear query statement (USE)");
        }
        let Some(ambient) = child(linear, "ambient linear query statement") else {
            return unsupported("no ambient linear query statement");
        };
        if let Some(nested) = child(ambient, "nested query specification") {
            let Some(spec) = child(nested, "query specification") else {
                return unsupported("an empty nested query");
            };
            let Some(body) = child(spec, "procedure body") else {
                return unsupported("a nested query without a body");
            };
            return self.procedure_body(body, &incoming);
        }
        let mut table = incoming;
        if let Some(simple) = child(ambient, "simple linear query statement") {
            let mut simples = Vec::new();
            find_all(simple, "simple query statement", &mut simples);
            for q in simples {
                table = self.simple_query(q, table)?;
            }
        }
        let Some(result) = child(ambient, "primitive result statement") else {
            return unsupported("no primitive result statement");
        };
        self.result_statement(result, table)
    }

    fn simple_query(&self, q: &Plain, table: Table) -> R<Table> {
        if child(q, "call query statement").is_some() {
            return unsupported("a CALL statement");
        }
        let Some(primitive) = child(q, "primitive query statement") else {
            return unsupported("no primitive query statement");
        };
        for c in logical(primitive) {
            return match def_name(c) {
                Some("match statement") => self.match_statement(c, table),
                Some("filter statement") => {
                    let cond = child(c, "search condition")
                        .or_else(|| child(c, "where clause").and_then(|w| child(w, "search condition")));
                    let Some(cond) = cond else {
                        return unsupported("a FILTER without a condition");
                    };
                    let mut rows = Vec::new();
                    for row in table.rows {
                        if self.truth(cond, &row)? == Some(true) {
                            rows.push(row);
                        }
                    }
                    Ok(Table { rows, ordered: table.ordered })
                }
                Some("let statement") => self.let_statement(c, table),
                Some("for statement") => self.for_statement(c, table),
                Some("order by and page statement") => self.order_and_page(c, table),
                Some(other) => unsupported(format!("a {other}")),
                None => continue,
            };
        }
        unsupported("an empty primitive query statement")
    }

    fn let_statement(&self, s: &Plain, table: Table) -> R<Table> {
        let mut defs = Vec::new();
        find_all(s, "let variable definition", &mut defs);
        let mut rows = Vec::new();
        for row in table.rows {
            let mut row = row;
            for d in &defs {
                let (name, expr, declared_type) = self.let_definition(d)?;
                let v = self.eval(expr, &row)?;
                if let Some(t) = &declared_type {
                    check_declared_type(&v, t)?;
                }
                row.insert(name, v);
            }
            rows.push(row);
        }
        Ok(Table { rows, ordered: table.ordered })
    }

    /// A `VALUE x [type] = expr` definition: the variable, the expression and the declared
    /// type's spelling, if any.
    fn value_definition<'p>(&self, vvd: &'p Plain) -> R<(String, &'p Plain, Option<String>)> {
        let Some(var) = child(vvd, "binding variable") else {
            return unsupported("a VALUE definition without a variable");
        };
        let Some(opt) = child(vvd, "opt typed value initializer") else {
            return unsupported("a VALUE definition without an initializer");
        };
        let Some(init) = child(opt, "value initializer") else {
            return unsupported("a VALUE definition without an initializer");
        };
        let Some(expr) = child(init, "value expression") else {
            return unsupported("a VALUE initializer without an expression");
        };
        let declared_type = child(opt, "value type").map(|t| t.text());
        Ok((identifier(var), expr, declared_type))
    }

    /// The variable, expression and declared type of a LET definition.
    fn let_definition<'p>(&self, d: &'p Plain) -> R<(String, &'p Plain, Option<String>)> {
        if let Some(vvd) = child(d, "value variable definition") {
            return self.value_definition(vvd);
        }
        let Some(var) = child(d, "binding variable") else {
            return unsupported("a LET definition without a variable");
        };
        let Some(expr) = child(d, "value expression") else {
            return unsupported("a LET definition without an expression");
        };
        Ok((identifier(var), expr, None))
    }

    fn for_statement(&self, s: &Plain, table: Table) -> R<Table> {
        let Some(item) = child(s, "for item") else {
            return unsupported("a FOR without an item");
        };
        let Some(alias) = child(item, "for item alias").and_then(|a| child(a, "binding variable")) else {
            return unsupported("a FOR without an alias");
        };
        let Some(source) = child(item, "for item source") else {
            return unsupported("a FOR without a source");
        };
        let ordinal = child(s, "for ordinality or offset").and_then(|o| {
            child(o, "binding variable").map(|v| (identifier(v), has_kw(o, "ORDINALITY")))
        });
        let name = identifier(alias);
        let mut rows = Vec::new();
        for row in table.rows {
            let list = self.eval(source, &row)?;
            let items = match list {
                Val::List(items) => items,
                Val::Null => Vec::new(),
                _ => return unsupported("FOR over something not a list"),
            };
            for (i, v) in items.into_iter().enumerate() {
                let mut r = row.clone();
                r.insert(name.clone(), v);
                if let Some((o, ordinality)) = &ordinal {
                    r.insert(o.clone(), Val::Int(if *ordinality { i as i128 + 1 } else { i as i128 }));
                }
                rows.push(r);
            }
        }
        Ok(Table { rows, ordered: table.ordered })
    }

    fn result_statement(&self, result: &Plain, table: Table) -> R<Option<Table>> {
        if has_kw(result, "FINISH") || result.text() == "FINISH" {
            return Ok(None);
        }
        let Some(ret) = child(result, "return statement") else {
            return unsupported(format!("a result statement that is not RETURN: {}", head(result)));
        };
        let mut table = self.return_statement(ret, table)?;
        if let Some(page) = child(result, "order by and page statement") {
            table = self.order_and_page(page, table)?;
        }
        Ok(Some(table))
    }

    fn return_statement(&self, ret: &Plain, table: Table) -> R<Table> {
        let Some(body) = child(ret, "return statement body") else {
            return unsupported("RETURN without a body");
        };
        if has_kw(body, "NO") {
            return Ok(Table { rows: vec![Row::new(); table.rows.len().min(1)], ordered: false });
        }
        let distinct = child(body, "set quantifier").is_some_and(|q| has_kw(q, "DISTINCT"));
        let group_by = child(body, "group by clause");
        let mut rows: Vec<Row> = Vec::new();
        if child(body, "return item list").is_none() {
            // RETURN *: every column of the incoming table.
            if group_by.is_some() {
                return unsupported("RETURN * with GROUP BY");
            }
            rows = table.rows.clone();
        } else {
            let mut items = Vec::new();
            find_all(child(body, "return item list").expect("checked"), "return item", &mut items);
            let mut columns: Vec<(String, &Plain)> = Vec::new();
            for item in items {
                let kids = logical(item);
                let Some(expr) = kids.first() else { continue };
                let col = child(item, "return item alias")
                    .and_then(|a| child(a, "identifier"))
                    .map(identifier)
                    .or_else(|| exactly(expr, "binding variable reference").map(identifier))
                    .or_else(|| exactly(expr, "property reference").map(|_| expr.text()));
                let Some(col) = col else {
                    return unsupported(format!("a return item with no name and no alias: {}", head(expr)));
                };
                columns.push((col, expr));
            }
            let aggregated = columns.iter().any(|(_, e)| has_aggregate(e)) || group_by.is_some();
            if aggregated {
                // 14.11: rows grouped by the GROUP BY keys (every non-aggregated reference
                // must be one); without GROUP BY, one group of the whole table.
                let keys: Vec<String> = match group_by {
                    Some(g) => {
                        let mut refs = Vec::new();
                        find_all(g, "binding variable reference", &mut refs);
                        refs.iter().map(|r| identifier(r)).collect()
                    }
                    None => Vec::new(),
                };
                let mut groups: BTreeMap<String, (Row, Vec<Row>)> = BTreeMap::new();
                for row in &table.rows {
                    let key_vals: Vec<Val> = keys.iter().map(|k| row.get(k).cloned().unwrap_or(Val::Null)).collect();
                    let key = Val::List(key_vals.clone()).key();
                    let mut key_row = Row::new();
                    for (k, v) in keys.iter().zip(key_vals) {
                        key_row.insert(k.clone(), v);
                    }
                    groups.entry(key).or_insert_with(|| (key_row, Vec::new())).1.push(row.clone());
                }
                if groups.is_empty() && keys.is_empty() {
                    groups.insert(String::new(), (Row::new(), Vec::new()));
                }
                for (_, (key_row, members)) in groups {
                    let mut out = Row::new();
                    for (col, expr) in &columns {
                        let v = self.eval_grouped(expr, &key_row, &members)?;
                        out.insert(col.clone(), v);
                    }
                    rows.push(out);
                }
            } else {
                for row in &table.rows {
                    let mut out = Row::new();
                    for (col, expr) in &columns {
                        out.insert(col.clone(), self.eval(expr, row)?);
                    }
                    rows.push(out);
                }
            }
        }
        if distinct {
            let mut seen = BTreeSet::new();
            rows.retain(|r| seen.insert(Val::Record(r.clone()).key()));
        }
        if let Some(what) = rows.iter().flat_map(|r| r.values()).find(|v| v.has_opaque()) {
            return unsupported(format!("{} in the result", class_of(what)));
        }
        Ok(Table { rows, ordered: false })
    }

    fn order_and_page(&self, page: &Plain, table: Table) -> R<Table> {
        let mut rows = table.rows;
        let mut ordered = table.ordered;
        if let Some(order) = child(page, "order by clause") {
            let mut specs = Vec::new();
            find_all(order, "sort specification", &mut specs);
            // Each sort key evaluated per row; rows compared key by key.
            let mut keyed: Vec<(Vec<(Val, bool, bool)>, Row)> = Vec::new();
            for row in rows {
                let mut keys = Vec::new();
                for spec in &specs {
                    let Some(key) = child(spec, "sort key") else { continue };
                    let v = self.eval(key, &row)?;
                    let desc = child(spec, "ordering specification").is_some_and(|o| o.text().starts_with("DESC"));
                    let nulls_first = match child(spec, "null ordering") {
                        Some(n) => has_kw(n, "FIRST"),
                        // 14.9: without a null ordering, nulls sort as if larger than every
                        // value (last under ASC, first under DESC).
                        None => desc,
                    };
                    keys.push((v, desc, nulls_first));
                }
                keyed.push((keys, row));
            }
            let mut problem: Option<Stop> = None;
            keyed.sort_by(|a, b| {
                for ((va, desc, nulls_first), (vb, _, _)) in a.0.iter().zip(&b.0) {
                    let o = match (va.is_null(), vb.is_null()) {
                        (true, true) => std::cmp::Ordering::Equal,
                        (true, false) => if *nulls_first { std::cmp::Ordering::Less } else { std::cmp::Ordering::Greater },
                        (false, true) => if *nulls_first { std::cmp::Ordering::Greater } else { std::cmp::Ordering::Less },
                        (false, false) => match order_values(va, vb) {
                            Ok(o) => if *desc { o.reverse() } else { o },
                            Err(e) => {
                                problem.get_or_insert(e);
                                std::cmp::Ordering::Equal
                            }
                        },
                    };
                    if o != std::cmp::Ordering::Equal {
                        return o;
                    }
                }
                std::cmp::Ordering::Equal
            });
            if let Some(p) = problem {
                return Err(p);
            }
            // Ties are unordered; an order is claimed only when every adjacent pair differs.
            let ties = keyed.windows(2).any(|w| {
                w[0].0.iter().zip(&w[1].0).all(|((a, _, _), (b, _, _))| a.key() == b.key())
            });
            if ties && keyed.len() > 1 {
                return unsupported("ORDER BY with ties: the order between equal keys is implementation-dependent");
            }
            rows = keyed.into_iter().map(|(_, r)| r).collect();
            ordered = true;
        }
        if let Some(offset) = child(page, "offset clause") {
            let n = self.non_negative(offset)?;
            rows = rows.into_iter().skip(n).collect();
        }
        if let Some(limit) = child(page, "limit clause") {
            let n = self.non_negative(limit)?;
            if rows.len() > n && !ordered {
                return unsupported("LIMIT below the row count without an order: which rows stay is implementation-dependent");
            }
            rows.truncate(n);
        }
        Ok(Table { rows, ordered })
    }

    fn non_negative(&self, clause: &Plain) -> R<usize> {
        let Some(spec) = child(clause, "non-negative integer specification") else {
            return unsupported("a page clause without a count");
        };
        let v = if let Some(i) = child(spec, "unsigned integer") {
            Val::Int(unsigned(&i.text()).ok_or_else(|| Stop::Unsupported("an integer out of range".into()))? as i128)
        } else {
            self.eval(spec, &Row::new())?
        };
        match v {
            Val::Int(i) if i >= 0 => Ok(i as usize),
            Val::Int(_) => Err(Stop::Exception("22G0G".to_string())),
            _ => unsupported("a count that is not an integer"),
        }
    }
}

/// A nonterminal that spells one delimiter (`<left paren>`, `<comma>`): not an operand.
fn punctuation(p: &Plain) -> bool {
    matches!(
        def_name(p),
        Some(
            "left paren" | "right paren" | "comma" | "left bracket" | "right bracket"
                | "left brace" | "right brace" | "period" | "colon" | "double colon"
                | "concatenation operator" | "vertical bar" | "asterisk" | "solidus"
                | "plus sign" | "minus sign" | "equals operator"
        )
    )
}

/// The first few tokens of a subtree, for reasons.
fn head(p: &Plain) -> String {
    let t = p.text();
    t.chars().take(40).collect()
}

fn has_aggregate(p: &Plain) -> bool {
    let mut found = Vec::new();
    find_all(p, "aggregate function", &mut found);
    !found.is_empty()
}

// ---------------------------------------------------------------------------------------------
// matching (16.3, 16.4, 22.2, 22.3, 22.4)

/// A symbol of the alphabet (22.2): a variable, an anonymous element, or a bracket.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Sym {
    Var(String),
    Temp(String),
    Anon,
    /// A bracket binding opening a parenthesized pattern: its index, subpath variable and
    /// path mode.
    Open(usize, Option<String>, ModeTag),
    Close(usize),
    /// The system subpath symbol of a multiset alternation's operand (16.7 SR 10 d): it
    /// survives REDUCE, so the same path through two operands is two matches.
    Alternative(usize, usize),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum ModeTag {
    Walk,
    Trail,
    Simple,
    Acyclic,
}

impl From<Mode> for ModeTag {
    fn from(m: Mode) -> Self {
        match m {
            Mode::Walk => ModeTag::Walk,
            Mode::Trail => ModeTag::Trail,
            Mode::Simple => ModeTag::Simple,
            Mode::Acyclic => ModeTag::Acyclic,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Elem {
    Node(usize),
    /// An edge and the kind of the pattern that bound it (its directionality constraint).
    Edge(usize, Kind),
    None,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Kind {
    Left,
    Undirected,
    Right,
    LeftOrUndirected,
    UndirectedOrRight,
    LeftOrRight,
    Any,
}

impl From<EdgeKind> for Kind {
    fn from(k: EdgeKind) -> Self {
        match k {
            EdgeKind::Left => Kind::Left,
            EdgeKind::Undirected => Kind::Undirected,
            EdgeKind::Right => Kind::Right,
            EdgeKind::LeftOrUndirected => Kind::LeftOrUndirected,
            EdgeKind::UndirectedOrRight => Kind::UndirectedOrRight,
            EdgeKind::LeftOrRight => Kind::LeftOrRight,
            EdgeKind::Any => Kind::Any,
        }
    }
}

/// A path binding (22.2 GR 13).
type PB = Vec<(Sym, Elem)>;

/// An item of a path term at one depth, after the 16.7 and 16.12 rewrites.
enum EItem<'a> {
    Node(Option<&'a Plain>),
    Edge {
        kind: Kind,
        filler: Option<&'a Plain>,
        label: Option<LabelExpr>,
    },
    Group(&'a Plain),
    SParen(&'a Plain, Kind),
    SQuant(&'a Plain, Kind, u64, Option<u64>),
}

impl EItem<'_> {
    fn is_edge(&self) -> bool {
        matches!(self, EItem::Edge { .. })
    }
    fn is_node(&self) -> bool {
        matches!(self, EItem::Node(_))
    }
}

/// The matcher of one `<graph pattern>` against the graph under an incoming row.
struct Matcher<'e, 'a> {
    env: &'e Env<'a>,
    /// The incoming working record: a variable already bound binds the same element.
    row: &'e Row,
    different_edges: bool,
    brackets: std::cell::Cell<usize>,
    /// The variables the pattern exposes as unconditional singletons, and as groups.
    singletons: BTreeSet<String>,
    groups: BTreeSet<String>,
    /// Every element, path and subpath variable the pattern declares.
    declared: BTreeSet<String>,
    /// Path variables seen so far, marked on their bindings' opening bracket.
    path_vars: std::cell::RefCell<BTreeSet<String>>,
}

impl Env<'_> {
    fn match_statement(&self, m: &Plain, table: Table) -> R<Table> {
        let Some(simple) = child(m, "simple match statement") else {
            return self.optional_match(m, table);
        };
        let Some(gpbt) = child(simple, "graph pattern binding table") else {
            return unsupported("MATCH without a binding table");
        };
        if child(gpbt, "graph pattern yield clause").is_some() {
            return unsupported("a graph pattern YIELD");
        }
        let Some(gp) = child(gpbt, "graph pattern") else {
            return unsupported("MATCH without a graph pattern");
        };
        // 16.3 GR 6: for each incoming record, the matches joined to it.
        let mut rows = Vec::new();
        for outer in &table.rows {
            for inner in self.matches(gp, outer)? {
                rows.push(join(outer, &inner));
            }
        }
        Ok(Table { rows, ordered: false })
    }

    fn optional_match(&self, m: &Plain, table: Table) -> R<Table> {
        let Some(operand) = child(m, "optional match statement").and_then(|o| child(o, "optional operand")) else {
            return unsupported("a match statement that is neither simple nor optional");
        };
        // 14.4 SR 4: OPTIONAL CALL { block RETURN new columns }: rows without a match keep
        // their columns, the new ones null.
        let mut inner_matches = Vec::new();
        find_all(operand, "simple match statement", &mut inner_matches);
        let mut rows = Vec::new();
        for outer in &table.rows {
            let mut inner = Table { rows: vec![outer.clone()], ordered: false };
            for sm in &inner_matches {
                let Some(gp) = child(sm, "graph pattern binding table").and_then(|t| child(t, "graph pattern")) else {
                    return unsupported("OPTIONAL MATCH without a graph pattern");
                };
                let mut next = Vec::new();
                for r in &inner.rows {
                    for found in self.matches(gp, r)? {
                        next.push(join(r, &found));
                    }
                }
                inner.rows = next;
            }
            if inner.rows.is_empty() {
                // The columns the block declares, null.
                let mut declared = BTreeSet::new();
                for sm in &inner_matches {
                    let mut decls = Vec::new();
                    find_all(sm, "element variable declaration", &mut decls);
                    for d in decls {
                        if let Some(v) = child(d, "element variable") {
                            declared.insert(identifier(v));
                        }
                    }
                    let mut pvs = Vec::new();
                    find_all(sm, "path variable", &mut pvs);
                    find_all(sm, "subpath variable", &mut pvs);
                    declared.extend(pvs.iter().map(|p| identifier(p)));
                }
                let mut r = outer.clone();
                for d in declared {
                    r.entry(d).or_insert(Val::Null);
                }
                rows.push(r);
            } else {
                rows.extend(inner.rows);
            }
        }
        Ok(Table { rows, ordered: false })
    }

    /// 16.4: the set of reduced matches of a graph pattern as records (22.8), under the
    /// incoming record `outer`.
    fn matches(&self, gp: &Plain, outer: &Row) -> R<Vec<Row>> {
        let different_edges = match child(gp, "match mode") {
            Some(m) => child(m, "different edges match mode").is_some(),
            None => match self.mode {
                MatchModeDefault::DifferentEdges => true,
                MatchModeDefault::RepeatableElements => false,
                MatchModeDefault::Portable => {
                    return unsupported("the match mode default (ID086) is not declared");
                }
            },
        };
        let (singletons, groups, declared) = exposure(gp);
        let matcher = Matcher {
            env: self,
            row: outer,
            different_edges,
            brackets: std::cell::Cell::new(0),
            singletons,
            groups,
            declared,
            path_vars: std::cell::RefCell::new(BTreeSet::new()),
        };
        matcher.graph_pattern(gp)
    }
}

/// Joins an incoming record and a match record: equal on shared columns, else dropped.
fn join(outer: &Row, inner: &Row) -> Row {
    let mut r = outer.clone();
    for (k, v) in inner {
        r.insert(k.clone(), v.clone());
    }
    r
}

/// The degree of exposure of every variable a graph pattern declares (16.7 SR 22): the
/// unconditional singletons, the group variables, and all declared names.
fn exposure(gp: &Plain) -> (BTreeSet<String>, BTreeSet<String>, BTreeSet<String>) {
    let mut singletons = BTreeSet::new();
    let mut groups = BTreeSet::new();
    let mut conditional = BTreeSet::new();
    let mut declared = BTreeSet::new();
    fn walk(
        p: &Plain,
        under_group: bool,
        under_union: bool,
        singletons: &mut BTreeSet<String>,
        groups: &mut BTreeSet<String>,
        conditional: &mut BTreeSet<String>,
        declared: &mut BTreeSet<String>,
    ) {
        match def_name(p) {
            Some("element variable declaration") => {
                if let Some(v) = child(p, "element variable") {
                    let name = identifier(v);
                    declared.insert(name.clone());
                    if has_kw(p, "TEMP") {
                        return;
                    }
                    if under_group {
                        groups.insert(name);
                    } else if under_union {
                        conditional.insert(name);
                    } else {
                        singletons.insert(name);
                    }
                }
                return;
            }
            Some("path variable") | Some("subpath variable") => {
                let name = identifier(p);
                declared.insert(name.clone());
                singletons.insert(name);
                return;
            }
            Some("quantified path primary") => {
                for c in logical(p) {
                    walk(c, true, under_union, singletons, groups, conditional, declared);
                }
                return;
            }
            Some("questioned path primary") => {
                for c in logical(p) {
                    walk(c, under_group, true, singletons, groups, conditional, declared);
                }
                return;
            }
            Some("path pattern union") | Some("path multiset alternation") => {
                // A variable every operand declares as a singleton is one (SR 22 d i).
                let terms: Vec<&Plain> = logical(p).into_iter().filter(|c| def_name(c) == Some("path term")).collect();
                let mut per: Vec<BTreeSet<String>> = Vec::new();
                for t in &terms {
                    let (mut s, mut g, mut c, mut d) = (BTreeSet::new(), BTreeSet::new(), BTreeSet::new(), BTreeSet::new());
                    walk(t, under_group, false, &mut s, &mut g, &mut c, &mut d);
                    groups.extend(g);
                    conditional.extend(c);
                    declared.extend(d);
                    per.push(s);
                }
                let mut all: Option<BTreeSet<String>> = None;
                for s in &per {
                    all = Some(match all {
                        None => s.clone(),
                        Some(a) => a.intersection(s).cloned().collect(),
                    });
                }
                let all = all.unwrap_or_default();
                for s in per {
                    for v in s {
                        if all.contains(&v) && !under_union {
                            singletons.insert(v);
                        } else {
                            conditional.insert(v);
                        }
                    }
                }
                return;
            }
            _ => {}
        }
        if let Plain::Def { children, .. } = p {
            for c in children {
                walk(c, under_group, under_union, singletons, groups, conditional, declared);
            }
        }
    }
    walk(gp, false, false, &mut singletons, &mut groups, &mut conditional, &mut declared);
    for c in &conditional {
        singletons.remove(c);
    }
    for g in &groups {
        singletons.remove(g);
    }
    (singletons, groups, declared)
}

impl Matcher<'_, '_> {
    fn graph_pattern(&self, gp: &Plain) -> R<Vec<Row>> {
        let keep = child(gp, "keep clause").and_then(|k| child(k, "path pattern prefix"));
        let Some(list) = child(gp, "path pattern list") else {
            return unsupported("a graph pattern without a path pattern list");
        };
        let mut patterns = Vec::new();
        find_all(list, "path pattern", &mut patterns);
        // 16.4 GR 5, 6: the local matches of each path pattern, then their cross product.
        let mut cross: Vec<Vec<PB>> = vec![Vec::new()];
        for pp in &patterns {
            let sm = self.path_pattern(pp, keep)?;
            let mut next = Vec::new();
            for mpb in &cross {
                for pb in &sm {
                    let mut m = mpb.clone();
                    m.push(pb.clone());
                    next.push(m);
                }
            }
            cross = next;
            if cross.len() > 200_000 {
                return unsupported("more than 200,000 candidate multi-path bindings");
            }
        }
        let where_clause = child(gp, "graph pattern where clause").and_then(|w| child(w, "search condition"));
        let mut records: BTreeMap<String, Row> = BTreeMap::new();
        for mpb in cross {
            // GR 7: every unconditional singleton binds one element across the binding.
            if !self.singletons_unique(&mpb) {
                continue;
            }
            // GR 8: different edges.
            if self.different_edges && !different_edges(&mpb) {
                continue;
            }
            let record = self.record(&mpb)?;
            // GR 9 b: the where clause on the match.
            if let Some(cond) = where_clause {
                let row = join(self.row, &record);
                if self.env.truth(cond, &row)? != Some(true) {
                    continue;
                }
            }
            // GR 10, 11: REDUCE and set semantics.
            let reduced: Vec<PB> = mpb.iter().map(|pb| reduce(pb)).collect();
            let key = format!("{reduced:?}");
            records.entry(key).or_insert(record);
        }
        Ok(records.into_values().collect())
    }

    fn singletons_unique(&self, mpb: &[PB]) -> bool {
        let mut bound: BTreeMap<&str, &Elem> = BTreeMap::new();
        for pb in mpb {
            for (sym, elem) in pb {
                if let Sym::Var(v) = sym {
                    if !self.singletons.contains(v) {
                        continue;
                    }
                    match bound.get(v.as_str()) {
                        Some(e) if !same_element(e, elem) => return false,
                        Some(_) => {}
                        None => {
                            bound.insert(v, elem);
                        }
                    }
                }
            }
        }
        true
    }

    /// 22.8: the record of a match: singletons their element, groups the list of theirs,
    /// conditional singletons unbound null, paths their compressed path.
    fn record(&self, mpb: &[PB]) -> R<Row> {
        let mut row = Row::new();
        for name in &self.declared {
            if self.groups.contains(name) {
                let mut list = Vec::new();
                for pb in mpb {
                    for (sym, elem) in pb {
                        if matches!(sym, Sym::Var(v) if v == name) {
                            list.push(elem_value(elem));
                        }
                    }
                }
                row.insert(name.clone(), Val::List(list));
                continue;
            }
            let mut value = Val::Null;
            'outer: for pb in mpb {
                for (i, (sym, elem)) in pb.iter().enumerate() {
                    match sym {
                        Sym::Var(v) if v == name => {
                            value = elem_value(elem);
                            break 'outer;
                        }
                        Sym::Open(j, Some(v), _) if v == name => {
                            value = Val::Path(compressed(&pb[i..=close_of(pb, i, *j)]));
                            break 'outer;
                        }
                        _ => {}
                    }
                }
            }
            row.insert(name.clone(), value);
        }
        // Path variables: bound by `path_pattern` as a leading Open with the path's name is
        // not how 22.2 does it; they are recorded there instead (see `path_pattern`).
        for pb in mpb {
            if let Some((Sym::Open(_, Some(v), _), Elem::None)) = pb.first() {
                if self.path_vars.borrow().contains(v) {
                    row.insert(v.clone(), Val::Path(compressed(pb)));
                }
            }
        }
        Ok(row)
    }
}

fn close_of(pb: &PB, open: usize, j: usize) -> usize {
    pb.iter()
        .enumerate()
        .skip(open + 1)
        .find(|(_, (s, _))| matches!(s, Sym::Close(k) if *k == j))
        .map(|(i, _)| i)
        .unwrap_or(pb.len() - 1)
}

fn same_element(a: &Elem, b: &Elem) -> bool {
    match (a, b) {
        (Elem::Node(x), Elem::Node(y)) => x == y,
        (Elem::Edge(x, _), Elem::Edge(y, _)) => x == y,
        _ => false,
    }
}

fn elem_value(e: &Elem) -> Val {
    match e {
        Elem::Node(n) => Val::Node(*n),
        Elem::Edge(e, _) => Val::Edge(*e),
        Elem::None => Val::Null,
    }
}

/// 16.4 GR 4: no edge bound at two positions.
fn different_edges(mpb: &[PB]) -> bool {
    let mut seen = BTreeSet::new();
    for pb in mpb {
        for (_, elem) in pb {
            if let Elem::Edge(e, _) = elem {
                if !seen.insert(*e) {
                    return false;
                }
            }
        }
    }
    true
}

/// 22.2 GR 13 d: the extracted path, consecutive node bindings collapsed, brackets dropped.
fn compressed(pb: &[(Sym, Elem)]) -> Vec<usize> {
    let mut out = Vec::new();
    let mut last_node = false;
    for (_, elem) in pb {
        match elem {
            Elem::Node(n) => {
                if !last_node {
                    out.push(*n);
                }
                last_node = true;
            }
            Elem::Edge(e, _) => {
                out.push(*e);
                last_node = false;
            }
            Elem::None => {}
        }
    }
    out
}

/// 22.2 GR 14: brackets removed, temporaries anonymous, redundant anonymous nodes removed.
fn reduce(pb: &PB) -> PB {
    let mut out: PB = pb
        .iter()
        .filter(|(s, _)| !matches!(s, Sym::Open(..) | Sym::Close(_)))
        .map(|(s, e)| match s {
            Sym::Temp(_) => (Sym::Anon, e.clone()),
            other => (other.clone(), e.clone()),
        })
        .collect();
    loop {
        let mut removed = false;
        let mut i = 0;
        while i + 1 < out.len() {
            let a_anon_node = matches!(out[i], (Sym::Anon, Elem::Node(_)));
            let b_anon_node = matches!(out[i + 1], (Sym::Anon, Elem::Node(_)));
            let a_var_node = matches!(out[i], (Sym::Var(_), Elem::Node(_)));
            let b_var_node = matches!(out[i + 1], (Sym::Var(_), Elem::Node(_)));
            if a_anon_node && b_anon_node {
                out.remove(i + 1);
                removed = true;
            } else if a_var_node && b_anon_node {
                out.remove(i + 1);
                removed = true;
            } else if a_anon_node && b_var_node {
                out.remove(i);
                removed = true;
            } else {
                i += 1;
            }
        }
        if !removed {
            break;
        }
    }
    out
}

impl Matcher<'_, '_> {
    /// 22.3 over one path pattern, then 22.4 if it is selective, then its path variable.
    fn path_pattern(&self, pp: &Plain, keep: Option<&Plain>) -> R<Vec<PB>> {
        let prefix = child(pp, "path pattern prefix").or(keep);
        let Some(expr) = child(pp, "path pattern expression") else {
            return unsupported("a path pattern without an expression");
        };
        let mut mode = Mode::Walk;
        let mut selective: Option<&Plain> = None;
        if let Some(prefix) = prefix {
            let mut modes = Vec::new();
            find_all(prefix, "path mode", &mut modes);
            if let Some(m) = modes.first() {
                mode = path_mode(m);
            }
            if let Some(s) = child(prefix, "path search prefix") {
                if child(s, "all path search").is_none() {
                    selective = Some(s);
                }
            }
        }
        // 16.4 SR: the path pattern expression is wrapped in a parenthesized one carrying the
        // prefix's mode (16.6 SR 1: WALK when none).
        let j = self.bracket();
        let inner = self.expression(expr)?;
        let mut sm: Vec<PB> = Vec::new();
        for pb in inner {
            let mut wrapped: PB = vec![(Sym::Open(j, None, mode.into()), Elem::None)];
            wrapped.extend(pb);
            wrapped.push((Sym::Close(j), Elem::None));
            if self.consistent(&wrapped) {
                sm.push(wrapped);
            }
        }
        if let Some(sel) = selective {
            sm = self.selective(sel, sm)?;
        }
        if let Some(decl) = child(pp, "path variable declaration") {
            if let Some(v) = child(decl, "path variable") {
                let name = identifier(v);
                self.path_vars.borrow_mut().insert(name.clone());
                // Mark the binding with its path variable: an Open with the name in front.
                sm = sm
                    .into_iter()
                    .map(|mut pb| {
                        pb[0] = (Sym::Open(j, Some(name.clone()), mode.into()), Elem::None);
                        pb
                    })
                    .collect();
            }
        }
        Ok(sm)
    }

    /// 22.4: the partitions by end nodes, ANY N kept whole when N or fewer, SHORTEST N by edge
    /// count when the cut is clean, SHORTEST N GROUPS by length groups.
    fn selective(&self, sel: &Plain, sm: Vec<PB>) -> R<Vec<PB>> {
        // 16.4 GR 5 c i: under DIFFERENT EDGES only different-edges-matched bindings.
        let sm: Vec<PB> = sm
            .into_iter()
            .filter(|pb| !self.different_edges || different_edges(std::slice::from_ref(pb)))
            .filter(|pb| self.singletons_unique(std::slice::from_ref(pb)))
            .collect();
        let count = |p: &Plain, names: &[&str]| -> R<usize> {
            for n in names {
                if let Some(c) = child(p, n) {
                    let v = if let Some(i) = child(c, "non-negative integer specification") {
                        self.env.non_negative_spec(i)?
                    } else {
                        return unsupported("a path count that is not a literal or parameter");
                    };
                    if v == 0 {
                        return Err(Stop::Exception("22G0F".to_string()));
                    }
                    return Ok(v);
                }
            }
            Ok(1)
        };
        enum Search {
            Any(usize),
            ShortestPaths(usize),
            ShortestGroups(usize),
        }
        let search = if let Some(any) = child(sel, "any path search") {
            Search::Any(count(any, &["number of paths"])?)
        } else if let Some(sp) = child(sel, "shortest path search") {
            if child(sp, "all shortest path search").is_some() {
                Search::ShortestGroups(1)
            } else if child(sp, "any shortest path search").is_some() {
                Search::ShortestPaths(1)
            } else if let Some(c) = child(sp, "counted shortest path search") {
                Search::ShortestPaths(count(c, &["number of paths"])?)
            } else if let Some(g) = child(sp, "counted shortest group search") {
                Search::ShortestGroups(count(g, &["number of groups"])?)
            } else {
                return unsupported("an unknown shortest path search");
            }
        } else {
            return Ok(sm);
        };
        // Reduced and deduplicated candidates, partitioned by first and last node.
        let mut partitions: BTreeMap<(usize, usize), Vec<PB>> = BTreeMap::new();
        let mut seen = BTreeSet::new();
        for pb in sm {
            let path = compressed(&pb);
            let (Some(first), Some(last)) = (path.first(), path.last()) else { continue };
            if !seen.insert(format!("{:?}", reduce(&pb))) {
                continue;
            }
            partitions.entry((*first, *last)).or_default().push(pb);
        }
        let mut out = Vec::new();
        for (_, mut part) in partitions {
            let length = |pb: &PB| pb.iter().filter(|(_, e)| matches!(e, Elem::Edge(..))).count();
            match search {
                Search::Any(n) => {
                    if part.len() > n {
                        return unsupported(format!("ANY {n} with {} matches: which are kept is implementation-dependent", part.len()));
                    }
                    out.extend(part);
                }
                Search::ShortestPaths(n) => {
                    if part.len() <= n {
                        out.extend(part);
                        continue;
                    }
                    part.sort_by_key(length);
                    if length(&part[n - 1]) == length(&part[n]) {
                        return unsupported(format!("SHORTEST {n} with a tie at the cut: which are kept is implementation-dependent"));
                    }
                    out.extend(part.into_iter().take(n));
                }
                Search::ShortestGroups(n) => {
                    let mut lengths: Vec<usize> = part.iter().map(length).collect();
                    lengths.sort();
                    lengths.dedup();
                    let keep: BTreeSet<usize> = lengths.into_iter().take(n).collect();
                    out.extend(part.into_iter().filter(|pb| keep.contains(&length(pb))));
                }
            }
        }
        Ok(out)
    }

    fn bracket(&self) -> usize {
        let j = self.brackets.get() + 1;
        self.brackets.set(j);
        j
    }

    /// 22.3 GR 3 h, j: a term, or the union of terms.
    fn expression(&self, p: &Plain) -> R<Vec<PB>> {
        let kids = logical(p);
        let Some(first) = kids.first() else {
            return Ok(Vec::new());
        };
        match def_name(first) {
            Some("path term") => self.term(first),
            Some("path pattern union") => {
                let mut out = Vec::new();
                for t in logical(first).into_iter().filter(|c| def_name(c) == Some("path term")) {
                    out.extend(self.term(t)?);
                }
                Ok(out)
            }
            Some("path multiset alternation") => {
                let mut out = Vec::new();
                let j = self.bracket();
                for (i, t) in logical(first).into_iter().filter(|c| def_name(c) == Some("path term")).enumerate() {
                    for mut pb in self.term(t)? {
                        pb.insert(0, (Sym::Alternative(j, i), Elem::None));
                        out.push(pb);
                    }
                }
                Ok(out)
            }
            _ => Ok(Vec::new()),
        }
    }

    fn items<'p>(&self, p: &'p Plain, out: &mut Vec<EItem<'p>>) -> R<()> {
        match def_name(p) {
            Some("path term") | Some("path concatenation") | Some("path factor") | Some("path primary") => {
                for c in logical(p) {
                    self.items(c, out)?;
                }
            }
            Some("element pattern") => {
                if let Some(ep) = child(p, "edge pattern") {
                    let (kind, filler) = edge_kind(ep);
                    out.push(EItem::Edge { kind: kind.into(), filler, label: None });
                } else {
                    out.push(EItem::Node(Some(p)));
                }
            }
            Some("quantified path primary") | Some("questioned path primary") | Some("parenthesized path pattern expression") => {
                out.push(EItem::Group(p));
            }
            Some("simplified path pattern expression") => {
                let kind = simplified_kind(p).into();
                let mut found = Vec::new();
                find_all(p, "simplified contents", &mut found);
                if let Some(contents) = found.first().copied() {
                    out.push(EItem::SParen(contents, kind));
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn simplified_items<'p>(&self, p: &'p Plain, kind: Kind, out: &mut Vec<EItem<'p>>) -> R<()> {
        let kids = logical(p);
        let Some(first) = kids.first() else { return Ok(()) };
        match def_name(p) {
            Some("simplified contents") | Some("simplified term") | Some("simplified factor low")
            | Some("simplified factor high") | Some("simplified tertiary") | Some("simplified secondary") => {
                match def_name(first) {
                    Some("simplified path union") | Some("simplified multiset alternation") => {
                        // Each operand is an alternative: handled by the caller as a union of
                        // sequences. Represented as one group item here.
                        out.push(EItem::SParen(p, kind));
                        Ok(())
                    }
                    Some("simplified concatenation") => {
                        for c in logical(first) {
                            if def_name(c).is_some() {
                                self.simplified_items(c, kind, out)?;
                            }
                        }
                        Ok(())
                    }
                    Some("simplified conjunction") | Some("simplified negation") => match simplified_label(first) {
                        Some(e) => {
                            out.push(EItem::Edge { kind, filler: None, label: Some(e) });
                            Ok(())
                        }
                        None => unsupported("a simplified conjunction that is not a label expression"),
                    },
                    Some("simplified quantified") => {
                        let (Some(t), Some(q)) = (child(first, "simplified tertiary"), child(first, "graph pattern quantifier")) else {
                            return unsupported("a simplified quantifier that could not be read");
                        };
                        let (lower, upper) = quantifier_bounds(q)?;
                        out.push(EItem::SQuant(t, kind, lower, upper));
                        Ok(())
                    }
                    Some("simplified questioned") => {
                        let Some(t) = child(first, "simplified tertiary") else {
                            return unsupported("a simplified ? without contents");
                        };
                        out.push(EItem::SQuant(t, kind, 0, Some(1)));
                        Ok(())
                    }
                    Some("simplified direction override") => {
                        let mut overridden = kind;
                        let mut secondary = None;
                        for o in logical(first) {
                            overridden = match def_name(o) {
                                Some("simplified override left") => Kind::Left,
                                Some("simplified override undirected") => Kind::Undirected,
                                Some("simplified override right") => Kind::Right,
                                Some("simplified override left or undirected") => Kind::LeftOrUndirected,
                                Some("simplified override undirected or right") => Kind::UndirectedOrRight,
                                Some("simplified override left or right") => Kind::LeftOrRight,
                                Some("simplified override any direction") => Kind::Any,
                                _ => continue,
                            };
                            secondary = child(o, "simplified secondary");
                        }
                        match secondary.and_then(simplified_label) {
                            Some(e) => {
                                out.push(EItem::Edge { kind: overridden, filler: None, label: Some(e) });
                                Ok(())
                            }
                            None => unsupported("a direction override whose contents are not a label expression"),
                        }
                    }
                    Some("simplified primary") => {
                        if let Some(n) = child(first, "label name") {
                            out.push(EItem::Edge { kind, filler: None, label: Some(LabelExpr::Name(identifier(n))) });
                        } else if let Some(inner) = child(first, "simplified contents") {
                            out.push(EItem::SParen(inner, kind));
                        }
                        Ok(())
                    }
                    Some(_) => self.simplified_items(first, kind, out),
                    None => Ok(()),
                }
            }
            Some("simplified path union") | Some("simplified multiset alternation") => {
                out.push(EItem::SParen(p, kind));
                Ok(())
            }
            _ => {
                for c in kids {
                    if def_name(c).is_some() {
                        self.simplified_items(c, kind, out)?;
                    }
                }
                Ok(())
            }
        }
    }

    /// The alternatives of a simplified contents (a union's or alternation's operands, else
    /// itself) and whether they form a multiset alternation.
    fn simplified_alternatives<'p>(&self, contents: &'p Plain) -> (Vec<&'p Plain>, bool) {
        let kids = logical(contents);
        let first = match def_name(contents) {
            Some("simplified path union") | Some("simplified multiset alternation") => Some(contents),
            _ => kids.first().copied().filter(|f| matches!(def_name(f), Some("simplified path union") | Some("simplified multiset alternation"))),
        };
        match first {
            Some(u) => (
                logical(u).into_iter().filter(|c| def_name(c) == Some("simplified term")).collect(),
                def_name(u) == Some("simplified multiset alternation"),
            ),
            None => (vec![contents], false),
        }
    }

    fn term(&self, p: &Plain) -> R<Vec<PB>> {
        let mut items = Vec::new();
        self.items(p, &mut items)?;
        self.sequence(items)
    }

    /// 22.3 GR 3 f over the items of one depth, 16.7 SR 14's implicit nodes added.
    fn sequence(&self, items: Vec<EItem<'_>>) -> R<Vec<PB>> {
        let mut seq: Vec<EItem<'_>> = Vec::new();
        let mut prev_node = false;
        for item in items {
            let edge = item.is_edge();
            if edge && !prev_node {
                seq.push(EItem::Node(None));
            }
            prev_node = item.is_node();
            seq.push(item);
            if edge {
                seq.push(EItem::Node(None));
                prev_node = true;
            }
        }
        // Two implicit/explicit nodes in a row after an edge's implicit node and an explicit
        // node pattern: the implicit one is the explicit one (SR 14 d applies only when no
        // node pattern follows). Drop an implicit node directly before an explicit one.
        let mut cleaned: Vec<EItem<'_>> = Vec::new();
        let mut iter = seq.into_iter().peekable();
        while let Some(item) = iter.next() {
            if matches!(item, EItem::Node(None)) && iter.peek().is_some_and(|n| matches!(n, EItem::Node(Some(_)))) {
                continue;
            }
            cleaned.push(item);
        }
        let mut acc: Vec<PB> = vec![Vec::new()];
        for item in cleaned {
            let set: Vec<PB> = match item {
                EItem::Node(pattern) => self.node_set(pattern)?,
                EItem::Edge { kind, filler, label } => self.edge_set(kind, filler, label.as_ref())?,
                EItem::Group(g) => self.group(g)?,
                EItem::SParen(contents, kind) => {
                    let j = self.bracket();
                    let (alternatives, multiset) = self.simplified_alternatives(contents);
                    let mut out = Vec::new();
                    for (i, alt) in alternatives.into_iter().enumerate() {
                        let mut items = Vec::new();
                        self.simplified_items(alt, kind, &mut items)?;
                        for pb in self.sequence(items)? {
                            let mut wrapped: PB = vec![(Sym::Open(j, None, ModeTag::Walk), Elem::None)];
                            if multiset {
                                wrapped.push((Sym::Alternative(j, i), Elem::None));
                            }
                            wrapped.extend(pb);
                            wrapped.push((Sym::Close(j), Elem::None));
                            out.push(wrapped);
                        }
                    }
                    out
                }
                EItem::SQuant(tertiary, kind, lower, upper) => {
                    let j = self.bracket();
                    let mut items = Vec::new();
                    self.simplified_items(tertiary, kind, &mut items)?;
                    let mut unit = Vec::new();
                    for pb in self.sequence(items)? {
                        let mut wrapped: PB = vec![(Sym::Open(j, None, ModeTag::Walk), Elem::None)];
                        wrapped.extend(pb);
                        wrapped.push((Sym::Close(j), Elem::None));
                        unit.push(wrapped);
                    }
                    self.power(unit, lower, upper)?
                }
            };
            let mut next = Vec::new();
            for pb in &acc {
                for s in &set {
                    let mut c = pb.clone();
                    c.extend(s.iter().cloned());
                    if self.consistent(&c) {
                        next.push(c);
                    }
                }
            }
            acc = next;
            if acc.len() > 200_000 {
                return unsupported("more than 200,000 candidate path bindings");
            }
        }
        Ok(acc)
    }

    /// 22.3 GR 3 b for a node pattern: every node whose label set satisfies the label
    /// expression, with the pattern's symbol; properties and an element where clause as the
    /// requirements 16.7 SR 12 makes of them.
    fn node_set(&self, pattern: Option<&Plain>) -> R<Vec<PB>> {
        let filler = pattern.and_then(|p| child(p, "node pattern")).and_then(|np| child(np, "element pattern filler"));
        let mut out = Vec::new();
        for n in &self.env.graph.nodes {
            let (sym, ok) = self.filler_matches(filler, true, n.id, &n.labels, &n.properties)?;
            if ok {
                out.push(vec![(sym, Elem::Node(n.id))]);
            }
        }
        Ok(out)
    }

    fn edge_set(&self, kind: Kind, filler: Option<&Plain>, label: Option<&LabelExpr>) -> R<Vec<PB>> {
        let filler = filler.and_then(|f| child(f, "element pattern filler"));
        let mut out = Vec::new();
        for e in &self.env.graph.edges {
            if let Some(l) = label {
                if !l.holds(&e.labels) {
                    continue;
                }
            }
            let (sym, ok) = self.filler_matches(filler, false, e.id, &e.labels, &e.properties)?;
            if ok {
                out.push(vec![(sym, Elem::Edge(e.id, kind))]);
            }
        }
        Ok(out)
    }

    /// The symbol a filler declares and whether element `id` satisfies it: labels by 22.5,
    /// `{k: v}` as `x.k = v` (16.7 SR 12 makes it a where clause), a where clause with the
    /// variable bound to the element (22.2 GR 12). A variable bound in the incoming record
    /// must bind the same element (16.3's join).
    fn filler_matches(
        &self,
        filler: Option<&Plain>,
        node: bool,
        id: usize,
        labels: &BTreeSet<String>,
        properties: &BTreeMap<String, Value>,
    ) -> R<(Sym, bool)> {
        let Some(filler) = filler else {
            return Ok((Sym::Anon, true));
        };
        let sym = match declared(filler) {
            Some((v, true)) => Sym::Temp(v),
            Some((v, false)) => Sym::Var(v),
            None => Sym::Anon,
        };
        if let Sym::Var(v) = &sym {
            match self.row.get(v) {
                Some(Val::Node(n)) if node => {
                    if *n != id {
                        return Ok((sym, false));
                    }
                }
                Some(Val::Edge(e)) if !node => {
                    if *e != id {
                        return Ok((sym, false));
                    }
                }
                Some(Val::Null) | None => {}
                Some(_) => return Ok((sym, false)),
            }
        }
        if let Some(ile) = child(filler, "is label expression") {
            match child(ile, "label expression").and_then(label_expr) {
                Some(e) => {
                    if !e.holds(labels) {
                        return Ok((sym, false));
                    }
                }
                None => return unsupported("a label expression that could not be read"),
            }
        }
        if let Some(pred) = child(filler, "element pattern predicate") {
            if let Some(spec) = child(pred, "element property specification") {
                let mut pairs = Vec::new();
                find_all(spec, "property key value pair", &mut pairs);
                for pair in pairs {
                    let kids = logical(pair);
                    let (Some(name), Some(expr)) = (kids.first(), kids.get(2)) else { continue };
                    let key = identifier(name);
                    let mut row = self.row.clone();
                    if let Sym::Var(v) = &sym {
                        row.insert(v.clone(), if node { Val::Node(id) } else { Val::Edge(id) });
                    }
                    let wanted = self.env.eval(expr, &row)?;
                    let have = properties.get(&key).map(Val::from_ir).unwrap_or(Val::Null);
                    if compare(&have, &wanted)? != Some(std::cmp::Ordering::Equal) {
                        return Ok((sym, false));
                    }
                }
            }
            if let Some(w) = child(pred, "element pattern where clause") {
                let Some(cond) = child(w, "search condition") else {
                    return unsupported("an element where clause without a condition");
                };
                let mut row = self.row.clone();
                if let Sym::Var(v) | Sym::Temp(v) = &sym {
                    row.insert(v.clone(), if node { Val::Node(id) } else { Val::Edge(id) });
                }
                if self.env.truth(cond, &row)? != Some(true) {
                    return Ok((sym, false));
                }
            }
        }
        Ok((sym, true))
    }

    /// A quantified, questioned or parenthesized primary (22.3 GR 3 a, c, d).
    fn group(&self, p: &Plain) -> R<Vec<PB>> {
        match def_name(p) {
            Some("parenthesized path pattern expression") => self.parenthesized(p),
            Some("questioned path primary") => {
                let Some(primary) = child(p, "path primary") else { return Ok(vec![Vec::new()]) };
                let unit = self.primary(primary)?;
                let mut out = vec![Vec::new()];
                out.extend(unit);
                Ok(out)
            }
            Some("quantified path primary") => {
                let (Some(primary), Some(q)) = (child(p, "path primary"), child(p, "graph pattern quantifier")) else {
                    return unsupported("a quantifier that could not be read");
                };
                let (lower, upper) = quantifier_bounds(q)?;
                let unit = self.primary(primary)?;
                self.power(unit, lower, upper)
            }
            _ => Ok(Vec::new()),
        }
    }

    /// `S^lower ∪ ... ∪ S^upper`, each power's bindings consistent; an unbounded power is
    /// bounded by the graph under DIFFERENT EDGES (an edge binds once) and otherwise by a
    /// cap that the selective pattern or the mode must justify.
    fn power(&self, unit: Vec<PB>, lower: u64, upper: Option<u64>) -> R<Vec<PB>> {
        let edges = self.env.graph.edges.len() as u64;
        let bound = match upper {
            Some(u) => u,
            None if self.different_edges => edges.max(lower),
            None => {
                // Under REPEATABLE ELEMENTS an unbounded quantifier is only valid in a
                // selective pattern (16.11 SR); walks can repeat, so paths up to twice the
                // edge count plus one cover every shortest path.
                (2 * edges + 1).max(lower)
            }
        };
        if bound > 512 {
            return unsupported(format!("a quantifier bound of {bound}"));
        }
        let mut out: Vec<PB> = Vec::new();
        let mut current: Vec<PB> = vec![Vec::new()];
        for m in 0..=bound {
            if m >= lower {
                out.extend(current.iter().cloned());
            }
            if m == bound {
                break;
            }
            let mut next = Vec::new();
            for pb in &current {
                for u in &unit {
                    let mut c = pb.clone();
                    c.extend(u.iter().cloned());
                    if self.consistent(&c) {
                        next.push(c);
                    }
                }
            }
            if next.is_empty() {
                break;
            }
            if next.len() > 200_000 {
                return unsupported("more than 200,000 candidate path bindings under a quantifier");
            }
            current = next;
        }
        Ok(out)
    }

    fn primary(&self, p: &Plain) -> R<Vec<PB>> {
        for c in logical(p) {
            match def_name(c) {
                Some("parenthesized path pattern expression") => return self.parenthesized(c),
                Some("element pattern") | Some("simplified path pattern expression") => {
                    // 16.7 SR 14 a: a quantified edge is a parenthesized one.
                    let j = self.bracket();
                    let mut out = Vec::new();
                    for pb in self.term(c)? {
                        let mut wrapped: PB = vec![(Sym::Open(j, None, ModeTag::Walk), Elem::None)];
                        wrapped.extend(pb);
                        wrapped.push((Sym::Close(j), Elem::None));
                        out.push(wrapped);
                    }
                    return Ok(out);
                }
                _ => {}
            }
        }
        Ok(Vec::new())
    }

    fn parenthesized(&self, p: &Plain) -> R<Vec<PB>> {
        let mode = child(p, "path mode prefix").and_then(|m| child(m, "path mode")).map_or(Mode::Walk, path_mode);
        let subpath = child(p, "subpath variable declaration").and_then(|d| child(d, "subpath variable")).map(identifier);
        let j = self.bracket();
        let Some(expr) = child(p, "path pattern expression") else {
            return unsupported("a parenthesized pattern without an expression");
        };
        let inner = self.expression(expr)?;
        let where_clause = child(p, "parenthesized path pattern where clause").and_then(|w| child(w, "search condition"));
        let mut out = Vec::new();
        for pb in inner {
            let mut wrapped: PB = vec![(Sym::Open(j, subpath.clone(), mode.into()), Elem::None)];
            wrapped.extend(pb);
            wrapped.push((Sym::Close(j), Elem::None));
            if !self.consistent(&wrapped) {
                continue;
            }
            if let Some(cond) = where_clause {
                // 16.4 GR 9 a ii: the condition under the local bindings of this group.
                let local = self.local_record(&wrapped);
                let row = join(self.row, &local);
                if self.env.truth(cond, &row)? != Some(true) {
                    continue;
                }
            }
            out.push(wrapped);
        }
        Ok(out)
    }

    /// The variables one binding binds, as a record: singletons their element, others the
    /// list of what they bind.
    fn local_record(&self, pb: &PB) -> Row {
        let mut row = Row::new();
        let mut lists: BTreeMap<String, Vec<Val>> = BTreeMap::new();
        for (sym, elem) in pb {
            if let Sym::Var(v) = sym {
                lists.entry(v.clone()).or_default().push(elem_value(elem));
            }
        }
        for (v, vals) in lists {
            if self.groups.contains(&v) {
                row.insert(v, Val::List(vals));
            } else {
                row.insert(v, vals[0].clone());
            }
        }
        row
    }

    /// 22.2 GR 16: the extracted path is a path (every edge connects its neighbours as its
    /// pattern's kind allows), non-separable node bindings bind one node, and every
    /// bracketed span respects its path mode.
    fn consistent(&self, pb: &PB) -> bool {
        let graph = self.env.graph;
        // (b) and (c): walk the elements, remembering the last node and a pending edge.
        let mut last_node: Option<usize> = None;
        let mut pending: Option<(usize, Kind)> = None;
        for (_, elem) in pb {
            match elem {
                Elem::Node(n) => {
                    if let Some((e, kind)) = pending.take() {
                        let left = last_node.expect("a node before an edge");
                        let edge = &graph.edges[graph.edges.iter().position(|x| x.id == e).expect("an edge of the graph")];
                        let l = edge.directed && edge.target == left && edge.source == *n;
                        let u = !edge.directed && ((edge.source == left && edge.target == *n) || (edge.source == *n && edge.target == left));
                        let r = edge.directed && edge.source == left && edge.target == *n;
                        let ok = match kind {
                            Kind::Left => l,
                            Kind::Undirected => u,
                            Kind::Right => r,
                            Kind::LeftOrUndirected => l || u,
                            Kind::UndirectedOrRight => u || r,
                            Kind::LeftOrRight => l || r,
                            Kind::Any => l || u || r,
                        };
                        if !ok {
                            return false;
                        }
                    } else if let Some(prev) = last_node {
                        if prev != *n {
                            return false;
                        }
                    }
                    last_node = Some(*n);
                }
                Elem::Edge(e, kind) => {
                    if pending.is_some() || last_node.is_none() {
                        return false;
                    }
                    pending = Some((*e, *kind));
                }
                Elem::None => {}
            }
        }
        // (d): path modes over each bracketed span.
        let mut stack: Vec<(usize, ModeTag, usize)> = Vec::new();
        for (i, (sym, _)) in pb.iter().enumerate() {
            match sym {
                Sym::Open(j, _, mode) => stack.push((*j, *mode, i)),
                Sym::Close(j) => {
                    if let Some(pos) = stack.iter().rposition(|(k, _, _)| k == j) {
                        let (_, mode, start) = stack.remove(pos);
                        if !mode_holds(&pb[start..=i], mode) {
                            return false;
                        }
                    }
                }
                _ => {}
            }
        }
        // An open span (the binding is still being built) is checked when it closes.
        true
    }
}

/// 22.2 GR 16 d over one bracketed span.
fn mode_holds(span: &[(Sym, Elem)], mode: ModeTag) -> bool {
    let path = compressed(span);
    let nodes: Vec<usize> = path.iter().step_by(2).copied().collect();
    let edges: Vec<usize> = path.iter().skip(1).step_by(2).copied().collect();
    let repeats = |xs: &[usize]| xs.iter().collect::<BTreeSet<_>>().len() < xs.len();
    match mode {
        ModeTag::Walk => true,
        ModeTag::Trail => !repeats(&edges),
        ModeTag::Acyclic => !repeats(&nodes),
        ModeTag::Simple => {
            if nodes.len() <= 2 {
                return true;
            }
            let inner = &nodes[1..nodes.len() - 1];
            !repeats(inner) && !inner.contains(&nodes[0]) && !inner.contains(&nodes[nodes.len() - 1])
        }
    }
}

/// `*` (0, none), `+` (1, none), `{n}` (n, n), `{m,n}` (m, n), `{m,}` (m, none), `{,n}` (0, n).
fn quantifier_bounds(q: &Plain) -> R<(u64, Option<u64>)> {
    for c in logical(q) {
        match def_name(c) {
            Some("asterisk") => return Ok((0, None)),
            Some("plus sign") => return Ok((1, None)),
            Some("fixed quantifier") => {
                let n = child(c, "unsigned integer").and_then(|u| unsigned(&u.text()));
                return n.map(|n| (n, Some(n))).ok_or_else(|| Stop::Unsupported("a fixed quantifier that could not be read".into()));
            }
            Some("general quantifier") => {
                let lower = match child(c, "lower bound") {
                    Some(l) => unsigned(&l.text()).ok_or_else(|| Stop::Unsupported("a lower bound that could not be read".into()))?,
                    None => 0,
                };
                let upper = match child(c, "upper bound") {
                    Some(u) => Some(unsigned(&u.text()).ok_or_else(|| Stop::Unsupported("an upper bound that could not be read".into()))?),
                    None => None,
                };
                return Ok((lower, upper));
            }
            _ => {}
        }
    }
    match q.text().as_str() {
        "*" => Ok((0, None)),
        "+" => Ok((1, None)),
        _ => unsupported("a quantifier that could not be read"),
    }
}

impl Env<'_> {
    fn non_negative_spec(&self, spec: &Plain) -> R<usize> {
        let v = if let Some(i) = child(spec, "unsigned integer") {
            Val::Int(unsigned(&i.text()).ok_or_else(|| Stop::Unsupported("an integer out of range".into()))? as i128)
        } else {
            self.eval(spec, &Row::new())?
        };
        match v {
            Val::Int(i) if i >= 0 => Ok(i as usize),
            Val::Int(_) => Err(Stop::Exception("22G0F".to_string())),
            _ => unsupported("a count that is not an integer"),
        }
    }
}

// ---------------------------------------------------------------------------------------------
// expressions (clauses 19, 20)

/// GQL comparison (19.3): `None` is unknown (a null operand); `Err` where the values are not
/// comparable or the evaluator does not reach.
fn compare(a: &Val, b: &Val) -> R<Option<std::cmp::Ordering>> {
    use std::cmp::Ordering::*;
    Ok(Some(match (a, b) {
        (Val::Null, _) | (_, Val::Null) => return Ok(None),
        (Val::Opaque(what), _) | (_, Val::Opaque(what)) => {
            return unsupported(format!("{what} compared"));
        }
        (Val::Bool(x), Val::Bool(y)) => x.cmp(y),
        (Val::Int(x), Val::Int(y)) => x.cmp(y),
        (Val::Float(x), Val::Float(y)) => x.partial_cmp(y).ok_or_else(|| Stop::Unsupported("NaN compared".into()))?,
        (Val::Int(x), Val::Float(y)) => (*x as f64).partial_cmp(y).ok_or_else(|| Stop::Unsupported("NaN compared".into()))?,
        (Val::Float(x), Val::Int(y)) => x.partial_cmp(&(*y as f64)).ok_or_else(|| Stop::Unsupported("NaN compared".into()))?,
        (Val::Str(x), Val::Str(y)) => x.cmp(y),
        (Val::Node(x), Val::Node(y)) => x.cmp(y),
        (Val::Edge(x), Val::Edge(y)) => x.cmp(y),
        (Val::Path(x), Val::Path(y)) => x.cmp(y),
        (Val::List(x), Val::List(y)) => {
            // Element by element; a null element makes the comparison unknown unless an
            // earlier element decides it.
            for (p, q) in x.iter().zip(y) {
                match compare(p, q)? {
                    Some(Equal) => {}
                    other => return Ok(other),
                }
            }
            x.len().cmp(&y.len())
        }
        (Val::Record(x), Val::Record(y)) => {
            if x.keys().ne(y.keys()) {
                return unsupported("records with different fields compared");
            }
            for (p, q) in x.values().zip(y.values()) {
                match compare(p, q)? {
                    Some(Equal) => {}
                    other => return Ok(other),
                }
            }
            Equal
        }
        _ => return unsupported(format!("values of different classes compared: {} and {}", class_of(a), class_of(b))),
    }))
}

/// A total order for ORDER BY (14.9): the comparison, or an error where not comparable.
fn order_values(a: &Val, b: &Val) -> Result<std::cmp::Ordering, Stop> {
    match compare(a, b)? {
        Some(o) => Ok(o),
        None => Ok(std::cmp::Ordering::Equal),
    }
}

fn class_of(v: &Val) -> &'static str {
    match v {
        Val::Opaque(_) => "an implementation-defined value",
        Val::Null => "null",
        Val::Bool(_) => "boolean",
        Val::Int(_) => "integer",
        Val::Float(_) => "float",
        Val::Str(_) => "string",
        Val::Node(_) => "node",
        Val::Edge(_) => "edge",
        Val::Path(_) => "path",
        Val::List(_) => "list",
        Val::Record(_) => "record",
    }
}

impl Env<'_> {
    /// A search condition's truth value: `Some(true)`, `Some(false)` or `None` for unknown.
    fn truth(&self, cond: &Plain, row: &Row) -> R<Option<bool>> {
        match self.eval(cond, row)? {
            Val::Bool(b) => Ok(Some(b)),
            Val::Null => Ok(None),
            other => unsupported(format!("a condition that is not boolean: {}", class_of(&other))),
        }
    }

    /// An expression's value under `row`.
    fn eval(&self, p: &Plain, row: &Row) -> R<Val> {
        let name = match p {
            Plain::Def { name, .. } => name.as_str(),
            Plain::Kw(_) | Plain::Term(_) | Plain::Leaf { .. } => {
                return unsupported(format!("a bare token as an expression: {}", p.text()));
            }
        };
        let kids = logical(p);
        match name {
            // ---- boolean (19.1, 20.x)
            "boolean value expression" => {
                if kids.len() == 1 {
                    return self.eval(kids[0], row);
                }
                let a = self.truth(kids[0], row)?;
                let b = self.truth(kids[2], row)?;
                let op = kids[1].text();
                Ok(three(match op.as_str() {
                    "OR" => match (a, b) {
                        (Some(true), _) | (_, Some(true)) => Some(true),
                        (Some(false), Some(false)) => Some(false),
                        _ => None,
                    },
                    "XOR" => match (a, b) {
                        (Some(x), Some(y)) => Some(x != y),
                        _ => None,
                    },
                    _ => return unsupported(format!("boolean operator {op}")),
                }))
            }
            "boolean term" => {
                if kids.len() == 1 {
                    return self.eval(kids[0], row);
                }
                let a = self.truth(kids[0], row)?;
                let b = self.truth(kids[2], row)?;
                Ok(three(match (a, b) {
                    (Some(false), _) | (_, Some(false)) => Some(false),
                    (Some(true), Some(true)) => Some(true),
                    _ => None,
                }))
            }
            "boolean factor" => {
                let Some(test) = kids.last() else { return unsupported("an empty boolean factor") };
                if !has_kw(p, "NOT") {
                    // A value of any class derives through the boolean nonterminals.
                    return self.eval(test, row);
                }
                let v = self.truth(test, row)?;
                Ok(three(v.map(|b| !b)))
            }
            "boolean test" => {
                let Some(primary) = kids.first() else { return unsupported("an empty boolean test") };
                let v = self.eval(primary, row)?;
                if !has_kw(p, "IS") {
                    return Ok(v);
                }
                let truth = match &v {
                    Val::Bool(b) => Some(*b),
                    Val::Null => None,
                    other => return unsupported(format!("IS TRUE on a {}", class_of(other))),
                };
                let negated = has_kw(p, "NOT");
                let wanted = match child(p, "truth value").map(|t| t.text()).as_deref() {
                    Some("TRUE") => Some(true),
                    Some("FALSE") => Some(false),
                    Some("UNKNOWN") => None,
                    _ => return unsupported("a truth value that could not be read"),
                };
                Ok(Val::Bool((truth == wanted) != negated))
            }
            "boolean primary" | "boolean predicand" | "search condition" | "predicate"
            | "value expression" | "common value expression" | "aggregating value expression"
            | "comparison predicand" | "value expression primary"
            | "non-parenthesized value expression primary"
            | "non-parenthesized value expression primary special case" | "numeric primary"
            | "character string primary" | "string value expression"
            | "character string value expression" | "list primary" | "list value expression"
            | "path value primary" | "path value expression" | "record expression"
            | "node reference value expression" | "edge reference value expression"
            | "numeric value function" | "string value function" | "list value function"
            | "unsigned value specification" | "unsigned literal" | "general literal"
            | "value specification" | "result" | "result expression" | "sort key"
            | "let value expression body" | "non-negative integer specification"
            | "general value specification" | "dynamic parameter specification"
            | "case expression" | "case specification"
            | "numeric value expression dividend" | "numeric value expression divisor"
            | "numeric value expression base" | "numeric value expression exponent"
            | "general logarithm base" | "general logarithm argument"
            | "list element" | "field" | "when operand" | "case operand"
            | "element variable reference" | "property source" | "node reference" | "edge reference"
            | "path value expression 1" | "list value expression 1" | "cast operand"
            | "cardinality expression argument" | "dependent value expression" | "independent value expression"
            | "trim operands" | "trim source" | "trim character string" | "length expression"
            | "reference value expression"
            | "for item source" | "character string value expression 1" | "character string function 1" => {
                let defs: Vec<&Plain> = kids.iter().copied().filter(|c| def_name(c).is_some() && !punctuation(c)).collect();
                if defs.len() == 1 && kids.len() == 1 {
                    return self.eval(defs[0], row);
                }
                if name == "general value specification" && has_kw(p, "SESSION_USER") {
                    return Ok(Val::Opaque("string".to_string()));
                }
                if name == "field" {
                    return unsupported("a bare field");
                }
                if defs.len() == 1 {
                    return self.eval(defs[0], row);
                }
                unsupported(format!("a {name} with {} parts", kids.len()))
            }
            "parenthesized value expression" | "parenthesized boolean value expression" => {
                let Some(inner) = kids.iter().find(|c| def_name(c).is_some() && !punctuation(c)) else {
                    return unsupported("empty parentheses");
                };
                self.eval(inner, row)
            }
            // ---- predicates (19)
            "comparison predicate" => {
                let (Some(left), Some(part2)) = (kids.first(), kids.get(1)) else {
                    return unsupported("a comparison without two sides");
                };
                let a = self.eval(left, row)?;
                self.comparison_part2(part2, a, row)
            }
            "null predicate" => {
                let (Some(primary), Some(part2)) = (kids.first(), kids.get(1)) else {
                    return unsupported("a null predicate without parts");
                };
                let v = self.eval(primary, row)?;
                // An implementation-defined value is never null.
                Ok(Val::Bool(v.is_null() != has_kw(part2, "NOT")))
            }
            "labeled predicate" => {
                let (Some(reference), Some(part2)) = (kids.first(), kids.get(1)) else {
                    return unsupported("a labeled predicate without parts");
                };
                let v = self.eval(reference, row)?;
                self.labeled_part2(part2, v)
            }
            "directed predicate" => {
                let (Some(reference), Some(part2)) = (kids.first(), kids.get(1)) else {
                    return unsupported("a directed predicate without parts");
                };
                let v = self.eval(reference, row)?;
                self.directed_part2(part2, v)
            }
            "source/destination predicate" => {
                let (Some(node_ref), Some(part2)) = (kids.first(), kids.get(1)) else {
                    return unsupported("a source/destination predicate without parts");
                };
                let n = self.eval(node_ref, row)?;
                self.source_destination_part2(part2, n, row)
            }
            "all_different predicate" | "same predicate" => {
                let mut refs = Vec::new();
                find_all(p, "element variable reference", &mut refs);
                let mut ids: Vec<Val> = Vec::new();
                for r in refs {
                    ids.push(self.eval(r, row)?);
                }
                if ids.iter().any(Val::is_null) {
                    return Ok(Val::Null);
                }
                let keys: Vec<String> = ids.iter().map(Val::key).collect();
                let distinct = keys.iter().collect::<BTreeSet<_>>().len();
                Ok(Val::Bool(if name == "same predicate" { distinct == 1 } else { distinct == keys.len() }))
            }
            "property_exists predicate" => {
                let reference = kids.iter().find(|c| def_name(c) == Some("element variable reference"));
                let pname = kids.iter().find(|c| def_name(c) == Some("property name"));
                let (Some(reference), Some(pname)) = (reference, pname) else {
                    return unsupported("PROPERTY_EXISTS without parts");
                };
                let v = self.eval(reference, row)?;
                let key = identifier(pname);
                Ok(match v {
                    Val::Null => Val::Null,
                    Val::Node(n) => Val::Bool(self.node(n).properties.contains_key(&key)),
                    Val::Edge(e) => Val::Bool(self.edge(e).properties.contains_key(&key)),
                    other => return unsupported(format!("PROPERTY_EXISTS on a {}", class_of(&other))),
                })
            }
            "exists predicate" => self.exists(p, row),
            "normalized predicate" => {
                let (Some(s), Some(part2)) = (kids.first(), kids.get(1)) else {
                    return unsupported("a normalized predicate without parts");
                };
                match self.eval(s, row)? {
                    Val::Null => Ok(Val::Null),
                    Val::Str(t) => {
                        // ASCII is normalized under every normal form.
                        if !t.is_ascii() {
                            return unsupported("IS NORMALIZED on a non-ASCII string");
                        }
                        Ok(Val::Bool(!has_kw(part2, "NOT")))
                    }
                    other => unsupported(format!("IS NORMALIZED on a {}", class_of(&other))),
                }
            }
            // ---- numeric (20.x)
            "numeric value expression" | "term" => {
                if kids.len() == 1 {
                    return self.eval(kids[0], row);
                }
                let a = self.eval(kids[0], row)?;
                let b = self.eval(kids[2], row)?;
                arithmetic(&kids[1].text(), a, b)
            }
            "factor" => {
                let negative = child(p, "sign").is_some_and(|s| s.text() == "-");
                let Some(primary) = kids.last() else { return unsupported("an empty factor") };
                let v = self.eval(primary, row)?;
                Ok(if negative {
                    match v {
                        Val::Int(i) => Val::Int(-i),
                        Val::Float(f) => Val::Float(-f),
                        Val::Null => Val::Null,
                        other => return unsupported(format!("a sign on a {}", class_of(&other))),
                    }
                } else {
                    v
                })
            }
            "absolute value expression" | "floor function" | "ceiling function" | "square root"
            | "natural logarithm" | "common logarithm" | "exponential function" | "trigonometric function" => {
                let mut args = Vec::new();
                find_all(p, "numeric value expression", &mut args);
                let Some(arg) = args.first() else { return unsupported("a function without its argument") };
                let v = self.eval(arg, row)?;
                numeric_function(name, &p.text(), v)
            }
            "modulus expression" | "power function" | "general logarithm function" => {
                let mut args = Vec::new();
                find_all(p, "numeric value expression", &mut args);
                let (Some(a), Some(b)) = (args.first(), args.get(1)) else {
                    return unsupported("a two argument function without its arguments");
                };
                let a = self.eval(a, row)?;
                let b = self.eval(b, row)?;
                binary_function(name, a, b)
            }
            "char length expression" => {
                let mut args = Vec::new();
                find_all(p, "character string value expression", &mut args);
                let Some(arg) = args.first() else { return unsupported("CHAR_LENGTH without an argument") };
                Ok(match self.eval(arg, row)? {
                    Val::Null => Val::Null,
                    Val::Str(s) => Val::Int(s.chars().count() as i128),
                    other => return unsupported(format!("CHAR_LENGTH of a {}", class_of(&other))),
                })
            }
            "path length expression" => {
                let mut args = Vec::new();
                find_all(p, "path value expression", &mut args);
                let Some(arg) = args.first() else { return unsupported("PATH_LENGTH without an argument") };
                Ok(match self.eval(arg, row)? {
                    Val::Null => Val::Null,
                    Val::Path(ids) => Val::Int((ids.len() / 2) as i128),
                    other => return unsupported(format!("PATH_LENGTH of a {}", class_of(&other))),
                })
            }
            "cardinality expression" => {
                let Some(arg) = kids.iter().find(|c| matches!(def_name(c), Some("cardinality expression argument") | Some("list value expression"))) else {
                    return unsupported("CARDINALITY without an argument");
                };
                Ok(match self.eval(arg, row)? {
                    Val::Null => Val::Null,
                    Val::List(l) => Val::Int(l.len() as i128),
                    Val::Path(ids) => Val::Int(ids.len() as i128),
                    Val::Record(r) => Val::Int(r.len() as i128),
                    other => return unsupported(format!("CARDINALITY of a {}", class_of(&other))),
                })
            }
            // ---- strings
            "character string concatenation" | "list concatenation" | "path value concatenation" => {
                let (Some(a), Some(b)) = (kids.first(), kids.last()) else {
                    return unsupported("a concatenation without two sides");
                };
                let a = self.eval(a, row)?;
                let b = self.eval(b, row)?;
                match (a, b) {
                    (Val::Null, _) | (_, Val::Null) => Ok(Val::Null),
                    (Val::Str(x), Val::Str(y)) => Ok(Val::Str(x + &y)),
                    (Val::List(mut x), Val::List(y)) => {
                        x.extend(y);
                        Ok(Val::List(x))
                    }
                    (Val::Path(x), Val::Path(y)) => {
                        // 20.x: joined where the last node of x is the first of y.
                        if x.last() != y.first() {
                            return Err(Stop::Exception("22G0Z".to_string()));
                        }
                        let mut out = x;
                        out.extend(y.into_iter().skip(1));
                        Ok(Val::Path(out))
                    }
                    (a, b) => unsupported(format!("|| of a {} and a {}", class_of(&a), class_of(&b))),
                }
            }
            "fold" => {
                let Some(arg) = kids.iter().find(|c| def_name(c) == Some("character string value expression")) else {
                    return unsupported("UPPER/LOWER without an argument");
                };
                let upper = has_kw(p, "UPPER");
                Ok(match self.eval(arg, row)? {
                    Val::Null => Val::Null,
                    Val::Str(s) => Val::Str(if upper { s.to_uppercase() } else { s.to_lowercase() }),
                    Val::Opaque(w) => Val::Opaque(w),
                    other => return unsupported(format!("UPPER/LOWER of a {}", class_of(&other))),
                })
            }
            "substring function" => {
                let (Some(s), Some(n)) = (child(p, "character string value expression"), child(p, "string length")) else {
                    return unsupported("LEFT/RIGHT without its arguments");
                };
                let s = self.eval(s, row)?;
                let n = self.eval(n, row)?;
                match (s, n) {
                    (Val::Null, _) | (_, Val::Null) => Ok(Val::Null),
                    (Val::Str(s), Val::Int(n)) => {
                        if n < 0 {
                            return Err(Stop::Exception("22011".to_string()));
                        }
                        let chars: Vec<char> = s.chars().collect();
                        let n = (n as usize).min(chars.len());
                        Ok(Val::Str(if has_kw(p, "LEFT") { chars[..n].iter().collect() } else { chars[chars.len() - n..].iter().collect() }))
                    }
                    (Val::Opaque(w), _) => Ok(Val::Opaque(w)),
                    (s, n) => unsupported(format!("LEFT/RIGHT of a {} and a {}", class_of(&s), class_of(&n))),
                }
            }
            "normalize function" => {
                let Some(arg) = child(p, "character string value expression") else {
                    return unsupported("NORMALIZE without an argument");
                };
                match self.eval(arg, row)? {
                    Val::Null => Ok(Val::Null),
                    Val::Str(s) if s.is_ascii() => Ok(Val::Str(s)),
                    Val::Str(_) => unsupported("NORMALIZE of a non-ASCII string"),
                    Val::Opaque(w) => Ok(Val::Opaque(w)),
                    other => unsupported(format!("NORMALIZE of a {}", class_of(&other))),
                }
            }
            "character string function" | "trim function" => {
                let Some(inner) = kids.iter().find(|c| def_name(c).is_some()) else {
                    return unsupported("an empty string function");
                };
                self.eval(inner, row)
            }
            "single-character trim function" => {
                let Some(operands) = child(p, "trim operands") else {
                    return unsupported("TRIM without operands");
                };
                let Some(source) = child(operands, "trim source") else {
                    return unsupported("TRIM without a source");
                };
                let spec = child(operands, "trim specification").map(|s| s.text().to_ascii_uppercase()).unwrap_or_else(|| "BOTH".to_string());
                let chars = match child(operands, "trim character string") {
                    Some(c) => Some(self.eval(c, row)?),
                    None => None,
                };
                let source = self.eval(source, row)?;
                trim(source, chars, &spec, true)
            }
            "multi-character trim function" => {
                let Some(source) = child(p, "trim source") else {
                    return unsupported("BTRIM without a source");
                };
                let spec = if has_kw(p, "LTRIM") { "LEADING" } else if has_kw(p, "RTRIM") { "TRAILING" } else { "BOTH" };
                let chars = match child(p, "trim character string") {
                    Some(c) => Some(self.eval(c, row)?),
                    None => None,
                };
                let source = self.eval(source, row)?;
                trim(source, chars, spec, false)
            }
            "string length" => {
                let Some(inner) = kids.iter().find(|c| def_name(c).is_some()) else {
                    return unsupported("an empty string length");
                };
                self.eval(inner, row)
            }
            "value type predicate" => {
                let (Some(primary), Some(part2)) = (kids.first(), kids.get(1)) else {
                    return unsupported("a type predicate without parts");
                };
                let v = self.eval(primary, row)?;
                let Some(t) = child(part2, "value type") else {
                    return unsupported("a type predicate without a type");
                };
                let negated = has_kw(part2, "NOT");
                Ok(Val::Bool(is_typed(&v, &t.text())? != negated))
            }
            // ---- CASE (20.x)
            "searched case" => {
                let mut whens = Vec::new();
                find_all(p, "searched when clause", &mut whens);
                for w in whens {
                    let (Some(cond), Some(result)) = (child(w, "search condition"), child(w, "result")) else { continue };
                    if self.truth(cond, row)? == Some(true) {
                        return self.result(result, row);
                    }
                }
                match child(p, "else clause").and_then(|e| child(e, "result")) {
                    Some(r) => self.result(r, row),
                    None => Ok(Val::Null),
                }
            }
            "simple case" => {
                let Some(operand) = child(p, "case operand") else { return unsupported("a CASE without an operand") };
                let v = self.eval(operand, row)?;
                let mut whens = Vec::new();
                find_all(p, "simple when clause", &mut whens);
                for w in whens {
                    let mut operands = Vec::new();
                    find_all(w, "when operand", &mut operands);
                    for o in operands {
                        if self.when_operand(o, &v, row)? == Some(true) {
                            let Some(result) = child(w, "result") else { continue };
                            return self.result(result, row);
                        }
                    }
                }
                match child(p, "else clause").and_then(|e| child(e, "result")) {
                    Some(r) => self.result(r, row),
                    None => Ok(Val::Null),
                }
            }
            "case abbreviation" => {
                let mut args = Vec::new();
                find_all(p, "value expression", &mut args);
                if has_kw(p, "NULLIF") {
                    let (Some(a), Some(b)) = (args.first(), args.get(1)) else { return unsupported("NULLIF without two arguments") };
                    let a = self.eval(a, row)?;
                    let b = self.eval(b, row)?;
                    return Ok(if compare(&a, &b)? == Some(std::cmp::Ordering::Equal) { Val::Null } else { a });
                }
                for a in args {
                    let v = self.eval(a, row)?;
                    if !v.is_null() {
                        return Ok(v);
                    }
                }
                Ok(Val::Null)
            }
            // ---- primaries
            "binding variable reference" => {
                let name = identifier(p);
                match row.get(&name) {
                    Some(v) => Ok(v.clone()),
                    None => unsupported(format!("variable {name} is not bound")),
                }
            }
            "property reference" => {
                let (Some(source), Some(pname)) = (kids.first(), kids.get(2)) else {
                    return unsupported("a property reference without parts");
                };
                let v = self.eval(source, row)?;
                let key = identifier(pname);
                Ok(match v {
                    Val::Null => Val::Null,
                    Val::Node(n) => self.node(n).properties.get(&key).map(Val::from_ir).unwrap_or(Val::Null),
                    Val::Edge(e) => self.edge(e).properties.get(&key).map(Val::from_ir).unwrap_or(Val::Null),
                    Val::Record(r) => r.get(&key).cloned().unwrap_or(Val::Null),
                    other => return unsupported(format!("a property of a {}", class_of(&other))),
                })
            }
            "general parameter reference" => {
                let Some(pname) = child(p, "parameter name") else { return unsupported("a parameter without a name") };
                let key = super::parameter_key(&pname.text());
                match self.params.get(&key) {
                    Some(v) => Ok(v.clone()),
                    None => unsupported(format!("parameter ${key} has no value")),
                }
            }
            "null literal" => Ok(Val::Null),
            "boolean literal" | "character string literal" | "unsigned numeric literal"
            | "exact numeric literal" | "approximate numeric literal" | "unsigned integer"
            | "unsigned decimal in common notation" => match literal(p) {
                Ok(v) => Ok(Val::from_ir(&v)),
                Err(why) => unsupported(format!("a literal that is {why}")),
            },
            "byte string literal" => Ok(Val::Opaque("bytes".to_string())),
            "duration literal" | "SQL-interval literal" => Ok(Val::Opaque("duration".to_string())),
            "date literal" => Ok(Val::Opaque("date".to_string())),
            "time literal" => Ok(Val::Opaque(if p.text().contains('+') || p.text().contains('Z') || p.text().contains("-") { "zoned time" } else { "local time" }.to_string())),
            "datetime literal" | "SQL-datetime literal" => Ok(Val::Opaque("local datetime".to_string())),
            "temporal literal" => {
                let Some(inner) = kids.iter().find(|c| def_name(c).is_some()) else {
                    return unsupported("an empty temporal literal");
                };
                self.eval(inner, row)
            }
            "byte string value expression" | "byte string primary" | "byte string concatenation" => {
                let mut vals = Vec::new();
                for c in kids.iter().filter(|c| def_name(c).is_some() && !punctuation(c)) {
                    vals.push(self.eval(c, row)?);
                }
                if vals.iter().any(Val::is_null) {
                    return Ok(Val::Null);
                }
                if vals.len() == 1 {
                    return Ok(vals.pop().expect("one"));
                }
                Ok(Val::Opaque("bytes".to_string()))
            }
            "datetime value function" | "duration value function" | "date function" | "time function"
            | "datetime function" | "localtime function" | "localdatetime function" | "duration function"
            | "duration absolute value function" => {
                // CURRENT_DATE and friends: the clock's; DATE('...') and friends: their
                // argument's. An empty record or null argument is the one exception the
                // rules fix (22G05 invalid datetime, null in, null out).
                let mut params = Vec::new();
                for n in ["date function parameters", "time function parameters", "datetime function parameters", "duration function parameters"] {
                    find_all(p, n, &mut params);
                }
                if let Some(arg) = params.first() {
                    let t = arg.text();
                    if t == "{}" {
                        return Err(Stop::Exception("22G05".to_string()));
                    }
                    if let Some(inner) = logical(arg).into_iter().find(|c| def_name(c).is_some()) {
                        let v = self.eval(inner, row)?;
                        return match v {
                            Val::Null => Ok(Val::Null),
                            Val::Str(s) if name == "duration function" && !s.starts_with('P') && !s.starts_with("-P") => Err(Stop::Exception("22G05".to_string())),
                            Val::Record(r) if r.is_empty() => Err(Stop::Exception("22G05".to_string())),
                            Val::Record(_) | Val::Str(_) | Val::Opaque(_) => Ok(Val::Opaque(temporal_kind(name, &p.text()))),
                            other => unsupported(format!("a {name} of a {}", class_of(&other))),
                        };
                    }
                    return unsupported(format!("a {name} whose argument could not be read"));
                }
                if has_kw(p, "DURATION") && kids.len() > 1 {
                    // DURATION ( x ): the absolute value.
                    let Some(arg) = kids.iter().find(|c| def_name(c).is_some() && !punctuation(c)) else {
                        return unsupported("DURATION() without an argument");
                    };
                    return match self.eval(arg, row)? {
                        Val::Null => Ok(Val::Null),
                        _ => Ok(Val::Opaque("duration".to_string())),
                    };
                }
                Ok(Val::Opaque(temporal_kind(name, &p.text())))
            }
            "datetime value expression" | "duration value expression" | "duration term" | "duration term 2" | "duration factor" | "duration primary" | "datetime primary" => {
                // Temporal arithmetic: null in, null out; else a temporal value we do not
                // represent. A factor of exact or approximate class is read for exceptions.
                let mut vals = Vec::new();
                for c in kids.iter().filter(|c| def_name(c).is_some() && !punctuation(c) && def_name(c) != Some("sign")) {
                    vals.push(self.eval(c, row)?);
                }
                if vals.len() == 1 {
                    return Ok(vals.pop().expect("one"));
                }
                if vals.iter().any(Val::is_null) {
                    return Ok(Val::Null);
                }
                // A datetime plus a duration keeps the datetime's kind; durations stay
                // durations; a factor times a duration is a duration.
                let kind = vals.iter().find_map(|v| match v {
                    Val::Opaque(k) if k != "duration" => Some(k.clone()),
                    _ => None,
                });
                Ok(Val::Opaque(kind.unwrap_or_else(|| "duration".to_string())))
            }
            "datetime subtraction" => {
                let mut args = Vec::new();
                find_all(p, "datetime value expression", &mut args);
                let mut vals = Vec::new();
                for a in args {
                    vals.push(self.eval(a, row)?);
                }
                if vals.iter().any(Val::is_null) {
                    return Ok(Val::Null);
                }
                Ok(Val::Opaque("duration".to_string()))
            }
            "list value constructor" | "list value constructor by enumeration" => {
                let mut items = Vec::new();
                find_all(p, "list element", &mut items);
                let mut out = Vec::new();
                for i in items {
                    out.push(self.eval(i, row)?);
                }
                Ok(Val::List(out))
            }
            "record constructor" | "fields specification" => {
                let mut fields = Vec::new();
                find_all(p, "field", &mut fields);
                let mut out = BTreeMap::new();
                for f in fields {
                    let fk = logical(f);
                    let (Some(fname), Some(expr)) = (fk.first(), fk.get(2)) else { continue };
                    out.insert(identifier(fname), self.eval(expr, row)?);
                }
                Ok(Val::Record(out))
            }
            "path value constructor" | "path value constructor by enumeration" => {
                let mut refs = Vec::new();
                find_all(p, "node reference value expression", &mut refs);
                let mut erefs = Vec::new();
                find_all(p, "edge reference value expression", &mut erefs);
                let mut ids = Vec::new();
                let mut nodes = Vec::new();
                for r in &refs {
                    nodes.push(self.eval(r, row)?);
                }
                let mut edges = Vec::new();
                for r in &erefs {
                    edges.push(self.eval(r, row)?);
                }
                if nodes.iter().chain(&edges).any(Val::is_null) {
                    return Ok(Val::Null);
                }
                // 20.x: PATH[n0, e1, n1, ...] must identify a path: each edge connects its
                // neighbours, else 22G0Z.
                for (i, n) in nodes.iter().enumerate() {
                    let Val::Node(nid) = n else { return unsupported("PATH[] with something not a node") };
                    ids.push(*nid);
                    if let Some(e) = edges.get(i) {
                        let Val::Edge(eid) = e else { return unsupported("PATH[] with something not an edge") };
                        let Some(Val::Node(next)) = nodes.get(i + 1) else { return Err(Stop::Exception("22G0Z".to_string())) };
                        let edge = self.edge(*eid);
                        let connects = (edge.source == *nid && edge.target == *next) || (!edge.directed && edge.source == *next && edge.target == *nid) || (edge.directed && edge.source == *next && edge.target == *nid);
                        if !connects {
                            return Err(Stop::Exception("22G0Z".to_string()));
                        }
                        ids.push(*eid);
                    }
                }
                Ok(Val::Path(ids))
            }
            "elements function" => {
                let mut args = Vec::new();
                find_all(p, "path value expression", &mut args);
                let Some(arg) = args.first() else { return unsupported("ELEMENTS without an argument") };
                Ok(match self.eval(arg, row)? {
                    Val::Null => Val::Null,
                    Val::Path(ids) => Val::List(
                        ids.iter().enumerate().map(|(i, id)| if i % 2 == 0 { Val::Node(*id) } else { Val::Edge(*id) }).collect(),
                    ),
                    other => return unsupported(format!("ELEMENTS of a {}", class_of(&other))),
                })
            }
            "cast specification" => {
                let Some(operand) = child(p, "cast operand") else { return unsupported("CAST without an operand") };
                let Some(target) = child(p, "cast target") else { return unsupported("CAST without a target") };
                let v = self.eval(operand, row)?;
                cast(v, &target.text())
            }
            "element_id function" => unsupported("ELEMENT_ID's spelling is implementation-dependent"),
            "let value expression" => {
                let mut defs = Vec::new();
                find_all(p, "let variable definition", &mut defs);
                let mut r = row.clone();
                for d in defs {
                    let (name, expr, declared_type) = self.let_definition(d)?;
                    let v = self.eval(expr, &r)?;
                    if let Some(t) = &declared_type {
                        check_declared_type(&v, t)?;
                    }
                    r.insert(name, v);
                }
                let Some(body) = kids.iter().rev().find(|c| def_name(c) == Some("value expression")) else {
                    return unsupported("LET ... IN without a body");
                };
                self.eval(body, &r)
            }
            "value query expression" => {
                let Some(nested) = child(p, "nested query specification") else { return unsupported("VALUE without a query") };
                let Some(body) = child(nested, "query specification").and_then(|s| child(s, "procedure body")) else {
                    return unsupported("VALUE with an empty query");
                };
                let table = self.procedure_body(body, &Table { rows: vec![row.clone()], ordered: false })?;
                match table {
                    Some(t) if t.rows.len() == 1 && t.rows[0].len() == 1 => Ok(t.rows[0].values().next().cloned().unwrap_or(Val::Null)),
                    Some(t) if t.rows.is_empty() => Ok(Val::Null),
                    _ => Err(Stop::Exception("21000".to_string())),
                }
            }
            "aggregate function" => {
                let members = self.group.borrow().clone();
                match members {
                    Some(m) => self.aggregate(p, &m),
                    None => unsupported("an aggregate outside a grouped RETURN"),
                }
            }
            other => unsupported(format!("a {other}")),
        }
    }

    fn result(&self, r: &Plain, row: &Row) -> R<Val> {
        if child(r, "null literal").is_some() {
            return Ok(Val::Null);
        }
        let Some(e) = logical(r).into_iter().find(|c| def_name(c).is_some()) else {
            return Ok(Val::Null);
        };
        self.eval(e, row)
    }

    fn when_operand(&self, o: &Plain, operand: &Val, row: &Row) -> R<Option<bool>> {
        let Some(inner) = logical(o).into_iter().find(|c| def_name(c).is_some()) else {
            return unsupported("an empty when operand");
        };
        let v = match def_name(inner) {
            Some("comparison predicate part 2") => self.comparison_part2(inner, operand.clone(), row)?,
            Some("null predicate part 2") => Val::Bool(operand.is_null() != has_kw(inner, "NOT")),
            Some("labeled predicate part 2") => self.labeled_part2(inner, operand.clone())?,
            Some("directed predicate part 2") => self.directed_part2(inner, operand.clone())?,
            Some("source predicate part 2") | Some("destination predicate part 2") => {
                self.source_destination_part2(inner, operand.clone(), row)?
            }
            Some("value type predicate part 2") | Some("normalized predicate part 2") => {
                return unsupported("a type or normalized when operand");
            }
            _ => {
                let w = self.eval(inner, row)?;
                three(compare(operand, &w)?.map(|o| o == std::cmp::Ordering::Equal))
            }
        };
        match v {
            Val::Bool(b) => Ok(Some(b)),
            Val::Null => Ok(None),
            other => unsupported(format!("a when operand that is a {}", class_of(&other))),
        }
    }

    fn comparison_part2(&self, part2: &Plain, a: Val, row: &Row) -> R<Val> {
        let Some(op) = child(part2, "comp op").map(|o| o.text()) else {
            return unsupported("a comparison without an operator");
        };
        let Some(right) = child(part2, "comparison predicand") else {
            return unsupported("a comparison without a right side");
        };
        let b = self.eval(right, row)?;
        let Some(o) = compare(&a, &b)? else {
            return Ok(Val::Null);
        };
        use std::cmp::Ordering::*;
        Ok(Val::Bool(match op.as_str() {
            "=" => o == Equal,
            "<>" => o != Equal,
            "<" => o == Less,
            ">" => o == Greater,
            "<=" => o != Greater,
            ">=" => o != Less,
            _ => return unsupported(format!("comparison operator {op}")),
        }))
    }

    fn labeled_part2(&self, part2: &Plain, v: Val) -> R<Val> {
        let negated = child(part2, "is labeled or colon").is_some_and(|c| has_kw(c, "NOT"));
        let Some(e) = child(part2, "label expression").and_then(label_expr) else {
            return unsupported("a label expression that could not be read");
        };
        let labels = match v {
            Val::Null => return Ok(Val::Null),
            Val::Node(n) => &self.node(n).labels,
            Val::Edge(e) => &self.edge(e).labels,
            other => return unsupported(format!("a labeled predicate on a {}", class_of(&other))),
        };
        Ok(Val::Bool(e.holds(labels) != negated))
    }

    fn directed_part2(&self, part2: &Plain, v: Val) -> R<Val> {
        let negated = has_kw(part2, "NOT");
        Ok(match v {
            Val::Null => Val::Null,
            Val::Edge(e) => Val::Bool(self.edge(e).directed != negated),
            other => return unsupported(format!("IS DIRECTED on a {}", class_of(&other))),
        })
    }

    fn source_destination_part2(&self, part2: &Plain, n: Val, row: &Row) -> R<Val> {
        let negated = has_kw(part2, "NOT");
        let wants_source = has_kw(part2, "SOURCE");
        let Some(edge_ref) = child(part2, "edge reference") else {
            return unsupported("a source/destination predicate without an edge");
        };
        let e = self.eval(edge_ref, row)?;
        let (Val::Node(n), Val::Edge(e)) = (&n, &e) else {
            if n.is_null() || e.is_null() {
                return Ok(Val::Null);
            }
            return unsupported("a source/destination predicate on something not a node and an edge");
        };
        let edge = self.edge(*e);
        // 19.10: on an undirected edge both nodes are source and destination.
        let holds = if !edge.directed {
            edge.source == *n || edge.target == *n
        } else if wants_source {
            edge.source == *n
        } else {
            edge.target == *n
        };
        Ok(Val::Bool(holds != negated))
    }

    /// 19.4: EXISTS over a graph pattern, a match block or a nested query, under the row.
    fn exists(&self, p: &Plain, row: &Row) -> R<Val> {
        if let Some(gp) = child(p, "graph pattern") {
            // 19.4 SR 2: EXISTS { GP } is EXISTS { MATCH GP RETURN TRUE AS x }.
            let found = self.matches(gp, row)?;
            return Ok(Val::Bool(!found.is_empty()));
        }
        if let Some(block) = child(p, "match statement block") {
            let mut table = Table { rows: vec![row.clone()], ordered: false };
            let mut statements = Vec::new();
            find_all(block, "match statement", &mut statements);
            for m in statements {
                table = self.match_statement(m, table)?;
            }
            return Ok(Val::Bool(!table.rows.is_empty()));
        }
        if let Some(nested) = child(p, "nested query specification") {
            let Some(body) = child(nested, "query specification").and_then(|s| child(s, "procedure body")) else {
                return unsupported("EXISTS with an empty query");
            };
            let table = self.procedure_body(body, &Table { rows: vec![row.clone()], ordered: false })?;
            return Ok(Val::Bool(table.is_some_and(|t| !t.rows.is_empty())));
        }
        unsupported("an EXISTS that could not be read")
    }

    fn node(&self, id: usize) -> &super::Node {
        self.graph.nodes.iter().find(|n| n.id == id).expect("a node of the graph")
    }

    fn edge(&self, id: usize) -> &super::Edge {
        self.graph.edges.iter().find(|e| e.id == id).expect("an edge of the graph")
    }

    /// A return item over a group: aggregates folded over the members, everything else
    /// evaluated on the group's key row.
    fn eval_grouped(&self, expr: &Plain, key_row: &Row, members: &[Row]) -> R<Val> {
        if let Some(agg) = exactly(expr, "aggregate function") {
            return self.aggregate(agg, members);
        }
        // An aggregate inside a larger expression: folded over the group where it stands.
        let previous = self.group.replace(Some(members.to_vec()));
        let v = self.eval(expr, key_row);
        *self.group.borrow_mut() = previous;
        v
    }

    fn aggregate(&self, agg: &Plain, members: &[Row]) -> R<Val> {
        if has_kw(agg, "COUNT") && child(agg, "asterisk").is_some() || agg.text() == "COUNT(*)" {
            return Ok(Val::Int(members.len() as i128));
        }
        let Some(general) = child(agg, "general set function") else {
            return unsupported("a binary set function (PERCENTILE)");
        };
        let Some(kind) = child(general, "general set function type").map(|t| t.text()) else {
            return unsupported("a set function without a type");
        };
        let distinct = child(general, "set quantifier").is_some_and(|q| has_kw(q, "DISTINCT"));
        let Some(arg) = child(general, "value expression") else {
            return unsupported("a set function without an argument");
        };
        let mut values = Vec::new();
        for m in members {
            let v = self.eval(arg, m)?;
            if !v.is_null() {
                values.push(v);
            }
        }
        if distinct {
            let mut seen = BTreeSet::new();
            values.retain(|v| seen.insert(v.key()));
        }
        match kind.as_str() {
            "COUNT" => Ok(Val::Int(values.len() as i128)),
            "COLLECT_LIST" => Ok(Val::List(values)),
            "MAX" | "MIN" => {
                let mut best: Option<Val> = None;
                for v in values {
                    best = Some(match best {
                        None => v,
                        Some(b) => {
                            let o = compare(&v, &b)?.unwrap_or(std::cmp::Ordering::Equal);
                            if (kind == "MAX") == (o == std::cmp::Ordering::Greater) && o != std::cmp::Ordering::Equal { v } else { b }
                        }
                    });
                }
                Ok(best.unwrap_or(Val::Null))
            }
            "SUM" | "AVG" => {
                if values.is_empty() {
                    return Ok(Val::Null);
                }
                let mut acc = Val::Int(0);
                for v in &values {
                    acc = arithmetic("+", acc, v.clone())?;
                }
                if kind == "SUM" {
                    return Ok(acc);
                }
                let n = values.len() as i128;
                match acc {
                    // 20.x leaves the declared type of AVG over exact numerics to the
                    // implementation (turbolay answers a float).
                    Val::Int(_) => unsupported("AVG of exact numerics: the result type is implementation-defined"),
                    Val::Float(f) => Ok(Val::Float(f / n as f64)),
                    _ => unsupported("AVG of something not numeric"),
                }
            }
            other => unsupported(format!("the aggregate {other}")),
        }
    }
}

/// The text with everything inside brackets, braces and parentheses removed.
fn strip_nested(t: &str) -> String {
    let mut depth = 0usize;
    let mut out = String::new();
    for c in t.chars() {
        match c {
            '{' | '(' | '[' | '<' => depth += 1,
            '}' | ')' | ']' | '>' => depth = depth.saturating_sub(1),
            _ if depth == 0 => out.push(c),
            _ => {}
        }
    }
    out
}

/// The class of a temporal function's value, from its name and spelling.
fn temporal_kind(name: &str, text: &str) -> String {
    let t = text.to_ascii_uppercase();
    match name {
        "date function" => "date",
        "time function" => "zoned time",
        "localtime function" => "local time",
        "datetime function" => "zoned datetime",
        "localdatetime function" => "local datetime",
        "duration function" | "duration absolute value function" | "duration value function" => "duration",
        _ => {
            if t.starts_with("CURRENT_DATE") || t.starts_with("DATE") {
                "date"
            } else if t.starts_with("CURRENT_TIMESTAMP") || t.starts_with("ZONED_DATETIME") {
                "zoned datetime"
            } else if t.starts_with("LOCAL_DATETIME") {
                "local datetime"
            } else if t.starts_with("CURRENT_TIME") || t.starts_with("ZONED_TIME") {
                "zoned time"
            } else if t.starts_with("LOCAL_TIME") {
                "local time"
            } else {
                "duration"
            }
        }
    }
    .to_string()
}

/// 20.x TRIM: `chars` is one character for TRIM (22027 otherwise), any string for BTRIM.
fn trim(source: Val, chars: Option<Val>, spec: &str, single: bool) -> R<Val> {
    let source = match source {
        Val::Null => return Ok(Val::Null),
        Val::Str(s) => s,
        Val::Opaque(w) => return Ok(Val::Opaque(w)),
        other => return unsupported(format!("TRIM of a {}", class_of(&other))),
    };
    let set: Vec<char> = match chars {
        None => vec![' '],
        Some(Val::Null) => return Ok(Val::Null),
        Some(Val::Str(c)) => {
            if single && c.chars().count() != 1 {
                return Err(Stop::Exception("22027".to_string()));
            }
            c.chars().collect()
        }
        Some(Val::Opaque(w)) => return Ok(Val::Opaque(w)),
        Some(other) => return unsupported(format!("TRIM with a {} trim string", class_of(&other))),
    };
    let s = match spec {
        "LEADING" => source.trim_start_matches(|c| set.contains(&c)).to_string(),
        "TRAILING" => source.trim_end_matches(|c| set.contains(&c)).to_string(),
        _ => source.trim_matches(|c| set.contains(&c)).to_string(),
    };
    Ok(Val::Str(s))
}

/// 19.6 IS TYPED: whether the value is of the named type, for the classes the harness has.
fn is_typed(v: &Val, declared: &str) -> R<bool> {
    let t = declared.to_ascii_uppercase().replace(' ', "");
    if t.starts_with("NOTHING") {
        return Ok(false);
    }
    if t == "NULL" || t == "NULLTYPE" {
        return Ok(v.is_null());
    }
    let not_null = t.ends_with("NOTNULL");
    if v.is_null() {
        return Ok(!not_null);
    }
    if t.starts_with("ANY") && !t.starts_with("ANYNODE") && !t.starts_with("ANYEDGE") && !t.starts_with("ANYRELATIONSHIP") && !t.starts_with("ANYVALUE") {
        return Ok(true);
    }
    let base = t.trim_start_matches("ANY").trim_start_matches("PROPERTY");
    let family = |prefixes: &[&str]| prefixes.iter().any(|p| base.starts_with(p));
    Ok(match v {
        Val::Int(_) => family(&["INT", "SIGNED", "UINT", "USMALLINT", "UBIGINT", "SMALLINT", "BIGINT", "VALUE"]),
        Val::Float(_) => family(&["FLOAT", "DOUBLE", "REAL", "VALUE"]),
        Val::Str(_) => family(&["STRING", "VARCHAR", "CHAR", "VALUE"]),
        Val::Bool(_) => family(&["BOOL", "VALUE"]),
        Val::Node(_) => family(&["NODE", "VERTEX"]),
        Val::Edge(_) => family(&["EDGE", "RELATIONSHIP"]),
        Val::Path(_) => family(&["PATH"]),
        Val::List(_) => family(&["LIST", "ARRAY"]),
        Val::Record(_) => family(&["RECORD", "{"]),
        Val::Opaque(_) => return unsupported("IS TYPED on an implementation-defined value"),
        Val::Null => true,
    })
}

/// 10.x: the initializer's value is assigned to the declared type (22.10, store assignment).
/// Null fits every nullable type; a literal class fits its own family; anything else is
/// left to the implementation (a cast, a type the harness has no values of).
fn check_declared_type(v: &Val, declared: &str) -> R<()> {
    let t = declared.to_ascii_uppercase();
    // NOT NULL of the type itself, not of a field type inside its braces or parentheses.
    let outer = strip_nested(&t).replace(' ', "");
    let not_null = outer.ends_with("NOTNULL");
    if v.is_null() {
        if not_null {
            return Err(Stop::Exception("22004".to_string()));
        }
        return Ok(());
    }
    let base = t.trim_start_matches("TYPED").trim_start_matches("::").trim();
    let family = |prefixes: &[&str]| prefixes.iter().any(|p| base.starts_with(p));
    let fits = match v {
        Val::Int(_) => family(&["INT", "SIGNED", "UINT", "USMALLINT", "UBIGINT", "SMALLINT", "BIGINT", "FLOAT", "DOUBLE", "REAL", "DECIMAL", "DEC", "ANY"]),
        Val::Float(_) => family(&["FLOAT", "DOUBLE", "REAL", "ANY"]),
        Val::Str(_) => family(&["STRING", "VARCHAR", "CHAR", "ANY"]),
        Val::Bool(_) => family(&["BOOL", "ANY"]),
        Val::Node(_) => family(&["NODE", "VERTEX", "ANY", "OPEN"]),
        Val::Edge(_) => family(&["EDGE", "RELATIONSHIP", "ANY", "OPEN"]),
        Val::Path(_) => family(&["PATH", "ANY"]),
        Val::List(_) => family(&["LIST", "ARRAY", "ANY"]),
        Val::Record(_) => family(&["RECORD", "ANY", "{"]),
            Val::Opaque(hint) => match hint.as_str() {
            "string" => family(&["STRING", "VARCHAR", "CHAR", "ANY"]),
            "date" => family(&["DATE", "ANY"]),
            "zoned time" => family(&["ZONEDTIME", "TIMEWITHTIMEZONE", "ANY"]),
            "local time" => family(&["LOCALTIME", "TIMEWITHOUTTIMEZONE", "TIME", "ANY"]),
            "zoned datetime" => family(&["ZONEDDATETIME", "TIMESTAMPWITHTIMEZONE", "ANY"]),
            "local datetime" => family(&["LOCALDATETIME", "TIMESTAMPWITHOUTTIMEZONE", "TIMESTAMP", "ANY"]),
            "duration" => family(&["DURATION", "ANY"]),
            "bytes" => family(&["BYTES", "BINARY", "VARBINARY", "ANY"]),
            _ => return unsupported(format!("{hint} assigned to a declared type")),
        },
        Val::Null => true,
    };
    if fits {
        Ok(())
    } else {
        unsupported(format!("a {} assigned to the declared type {declared}", class_of(v)))
    }
}

fn three(v: Option<bool>) -> Val {
    match v {
        Some(b) => Val::Bool(b),
        None => Val::Null,
    }
}

/// 20.x arithmetic: exact with exact stays exact, anything with approximate is approximate,
/// null propagates; division of exact numerics and overflow are left to the implementation.
fn arithmetic(op: &str, a: Val, b: Val) -> R<Val> {
    match (a, b) {
        (Val::Null, _) | (_, Val::Null) => Ok(Val::Null),
        (Val::Opaque(what), _) | (_, Val::Opaque(what)) => Ok(Val::Opaque(what)),
        (Val::Int(x), Val::Int(y)) => Ok(Val::Int(match op {
            "+" => x.checked_add(y).ok_or_else(|| Stop::Exception("22003".to_string()))?,
            "-" => x.checked_sub(y).ok_or_else(|| Stop::Exception("22003".to_string()))?,
            "*" => x.checked_mul(y).ok_or_else(|| Stop::Exception("22003".to_string()))?,
            "/" => {
                if y == 0 {
                    return Err(Stop::Exception("22012".to_string()));
                }
                if x % y != 0 {
                    return unsupported("division of exact numerics with a remainder: the scale is implementation-defined");
                }
                x / y
            }
            _ => return unsupported(format!("operator {op}")),
        })),
        (a, b) => {
            let (x, y) = match (a, b) {
                (Val::Int(x), Val::Float(y)) => (x as f64, y),
                (Val::Float(x), Val::Int(y)) => (x, y as f64),
                (Val::Float(x), Val::Float(y)) => (x, y),
                (a, b) => return unsupported(format!("{op} of a {} and a {}", class_of(&a), class_of(&b))),
            };
            let r = match op {
                "+" => x + y,
                "-" => x - y,
                "*" => x * y,
                "/" => {
                    if y == 0.0 {
                        return Err(Stop::Exception("22012".to_string()));
                    }
                    x / y
                }
                _ => return unsupported(format!("operator {op}")),
            };
            if !r.is_finite() {
                return Err(Stop::Exception("22003".to_string()));
            }
            Ok(Val::Float(r))
        }
    }
}

fn numeric_function(name: &str, text: &str, v: Val) -> R<Val> {
    let x = match v {
        Val::Null => return Ok(Val::Null),
        Val::Int(i) => {
            if name == "absolute value expression" {
                return Ok(Val::Int(i.abs()));
            }
            if matches!(name, "floor function" | "ceiling function") {
                return Ok(Val::Int(i));
            }
            i as f64
        }
        Val::Float(f) => f,
        other => return unsupported(format!("a numeric function of a {}", class_of(&other))),
    };
    let upper = text.to_ascii_uppercase();
    let r = match name {
        "absolute value expression" => x.abs(),
        "floor function" => x.floor(),
        "ceiling function" => x.ceil(),
        "square root" => {
            if x < 0.0 {
                return Err(Stop::Exception("22013".to_string()));
            }
            x.sqrt()
        }
        "natural logarithm" | "common logarithm" => {
            if x <= 0.0 {
                return Err(Stop::Exception("2201E".to_string()));
            }
            if name == "natural logarithm" { x.ln() } else { x.log10() }
        }
        "exponential function" => x.exp(),
        "trigonometric function" => {
            let f = upper.split('(').next().unwrap_or("").trim();
            match f {
                "SIN" => x.sin(),
                "COS" => x.cos(),
                "TAN" => x.tan(),
                "COT" => 1.0 / x.tan(),
                "SINH" => x.sinh(),
                "COSH" => x.cosh(),
                "TANH" => x.tanh(),
                "ASIN" => x.asin(),
                "ACOS" => x.acos(),
                "ATAN" => x.atan(),
                "DEGREES" => x.to_degrees(),
                "RADIANS" => x.to_radians(),
                _ => return unsupported(format!("the function {f}")),
            }
        }
        _ => return unsupported(format!("the function {name}")),
    };
    if !r.is_finite() {
        return Err(Stop::Exception("22003".to_string()));
    }
    Ok(Val::Float(r))
}

fn binary_function(name: &str, a: Val, b: Val) -> R<Val> {
    match (name, a, b) {
        (_, Val::Null, _) | (_, _, Val::Null) => Ok(Val::Null),
        ("modulus expression", Val::Int(x), Val::Int(y)) => {
            if y == 0 {
                return Err(Stop::Exception("22012".to_string()));
            }
            Ok(Val::Int(x % y))
        }
        ("power function", a, b) => {
            let (x, y) = (as_f64(&a)?, as_f64(&b)?);
            let r = x.powf(y);
            if !r.is_finite() {
                return Err(Stop::Exception("22003".to_string()));
            }
            Ok(Val::Float(r))
        }
        ("general logarithm function", a, b) => {
            let (base, x) = (as_f64(&a)?, as_f64(&b)?);
            if base <= 0.0 || base == 1.0 || x <= 0.0 {
                return Err(Stop::Exception("2201E".to_string()));
            }
            Ok(Val::Float(x.ln() / base.ln()))
        }
        (n, a, b) => unsupported(format!("{n} of a {} and a {}", class_of(&a), class_of(&b))),
    }
}

fn as_f64(v: &Val) -> R<f64> {
    match v {
        Val::Int(i) => Ok(*i as f64),
        Val::Float(f) => Ok(*f),
        other => unsupported(format!("a numeric function of a {}", class_of(other))),
    }
}

/// CAST for the literal classes: to the same class, exact to approximate, numbers and
/// booleans to strings. The rest is left to the implementation or not reached.
fn cast(v: Val, target: &str) -> R<Val> {
    let t = target.to_ascii_uppercase();
    let t = t.trim();
    let is_string = t.starts_with("STRING") || t.starts_with("VARCHAR") || t.starts_with("CHAR");
    let is_int = t.starts_with("INT") || t.starts_with("SIGNED") || t.starts_with("UINT") || t.starts_with("SMALLINT") || t.starts_with("BIGINT");
    let is_float = t.starts_with("FLOAT") || t.starts_with("DOUBLE") || t.starts_with("REAL");
    let is_bool = t.starts_with("BOOL");
    if t.starts_with("ANY") {
        return Ok(v);
    }
    match (v, is_string, is_int, is_float, is_bool) {
        (Val::Null, ..) => Ok(Val::Null),
        (Val::Opaque(w), ..) => Ok(Val::Opaque(w)),
        (Val::Str(s), true, ..) => Ok(Val::Str(s)),
        (Val::Int(i), true, ..) => Ok(Val::Str(i.to_string())),
        (Val::Bool(b), true, ..) => Ok(Val::Str(if b { "TRUE".into() } else { "FALSE".into() })),
        (Val::Int(i), _, true, ..) => Ok(Val::Int(i)),
        (Val::Int(i), _, _, true, _) => Ok(Val::Float(i as f64)),
        (Val::Float(f), _, _, true, _) => Ok(Val::Float(f)),
        (Val::Bool(b), _, _, _, true) => Ok(Val::Bool(b)),
        (Val::Str(s), _, true, ..) => s.trim().parse::<i128>().map(Val::Int).map_err(|_| Stop::Exception("22018".to_string())),
        (Val::Str(s), _, _, _, true) => match s.trim().to_ascii_uppercase().as_str() {
            "TRUE" => Ok(Val::Bool(true)),
            "FALSE" => Ok(Val::Bool(false)),
            _ => Err(Stop::Exception("22018".to_string())),
        },
        (v, ..) => unsupported(format!("CAST of a {} AS {target}", class_of(&v))),
    }
}
