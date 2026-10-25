//! The witness oracle: a graph and a known outcome for a query, read off its tree and its
//! generation record (`research/oracle-witness-2026-10-23.md`).
//!
//! For a query in the pattern core the construction `W` freezes every `MATCH` into data: a
//! node per node pattern with a label set its label expression accepts and the properties its
//! predicates need, an edge per edge pattern with a direction that satisfies the edge kind, a
//! quantified group at its lower bound, a union by its first operand. Theorem 1 of the note
//! says the binding built this way is a match by ISO/IEC 39075 22.3, so the query's binding
//! table on the graph holds the record of it; or the pattern has no match on any graph, and
//! the construction says why. Everything outside the core still gets the graph and a weaker
//! expectation (the status), tagged as such.
//!
//! Rules cited are ISO/IEC 39075:2024 + Cor 1:2026. The 16.7 syntax rule transformations
//! (implicit node patterns, abbreviated edges as full ones, an element where clause as a
//! parenthesized one) are applied while walking, not by rewriting the tree.

pub mod eval;

use crate::verify::Plain;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

// ---------------------------------------------------------------------------------------------
// the ir

/// A property value of the test literal classes.
#[derive(Serialize, Clone, Debug, PartialEq)]
#[serde(untagged)]
pub enum Value {
    Null,
    Bool(bool),
    Int(i128),
    Float(f64),
    Str(String),
}

#[derive(Serialize, Clone, Debug, Default)]
pub struct Node {
    pub id: usize,
    pub labels: BTreeSet<String>,
    pub properties: BTreeMap<String, Value>,
}

#[derive(Serialize, Clone, Debug)]
pub struct Edge {
    pub id: usize,
    pub source: usize,
    pub target: usize,
    pub labels: BTreeSet<String>,
    pub directed: bool,
    pub properties: BTreeMap<String, Value>,
}

/// The graph a query runs against, in our own terms; ids are also the `_id` property of
/// every element, so a returned element is compared by it.
#[derive(Serialize, Clone, Debug, Default)]
pub struct Graph {
    pub nodes: Vec<Node>,
    pub edges: Vec<Edge>,
}

/// The property that identifies an element across engines. Generated queries never name it:
/// the leaf provider spells property names from a different alphabet.
pub const ID_PROPERTY: &str = "_id";

/// What a variable holds in the witness record (22.8).
#[derive(Serialize, Clone, Debug, PartialEq)]
#[serde(tag = "kind", content = "value")]
pub enum Bound {
    Node(usize),
    Edge(usize),
    /// The elements of a path, nodes and edges alternating.
    Path(Vec<usize>),
    /// A group variable: one entry per iteration.
    List(Vec<Bound>),
    Null,
    /// A literal an observation query returns.
    Int(i128),
}

/// The match mode a `<graph pattern>` without one gets (ID086).
pub use crate::MatchModeDefault;

/// Which tier of the oracle backs the expectation of a row.
#[derive(Serialize, Clone, Copy, Debug, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum Tier {
    /// Theorem 2: the evaluator computed the whole result (`bag`, or the exception).
    Bag,
    /// Theorem 1: the witness record is in the result, or the pattern never matches.
    Witness,
    /// Out of the core: the query completes with status 00000, no claim on rows.
    Status,
}

/// The expected outcome of the query on the graph.
#[derive(Serialize, Clone, Debug)]
pub struct Expect {
    pub tier: Tier,
    /// `ok` (a status of class 00), or `exception`.
    pub outcome: &'static str,
    /// The exception class when the outcome is one.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub status: Option<String>,
    /// The whole result, in the bag tier: every row, ordered when `ordered`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub bag: Option<Vec<eval::Row>>,
    pub ordered: bool,
    /// Why the evaluator stopped, when the record is not of the bag tier.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub evaluator: Option<String>,
    /// The witness record after the last MATCH: variable to what it holds.
    pub binding: BTreeMap<String, Bound>,
    /// `Some(0)` when the pattern is unsatisfiable on every graph, `Some(n)` when the bag
    /// is known exactly (theorem 2, later), `None` when only `row` is claimed.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rows: Option<usize>,
    /// A row the result must contain: the witness record projected by RETURN.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub row: Option<BTreeMap<String, Bound>>,
    /// Whether the query returns a result table at all (`FINISH` does not).
    pub result: bool,
}

/// One oracle record per sentence.
#[derive(Serialize, Clone, Debug)]
pub struct Oracle {
    pub sentence: String,
    pub graph: Graph,
    pub setup: Setup,
    pub expect: Expect,
    /// For a query whose only observable is completion (`FINISH`): the same patterns with
    /// their variables returned, and what that must return. Hypothesis H-observe: the
    /// engine evaluates the MATCH the same way whichever result statement follows.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub observe: Option<Observe>,
    /// The parameters the query takes, each given a value of a class its site admits (from
    /// the generation record's `params`): sent with the query by the probes.
    #[serde(skip_serializing_if = "BTreeMap::is_empty")]
    pub parameters: BTreeMap<String, Value>,
    /// Why the row is not of the witness tier, or why the pattern cannot match.
    pub why: Vec<String>,
}

#[derive(Serialize, Clone, Debug)]
pub struct Observe {
    pub query: String,
    /// `Some(0)` when no graph matches; else `row` must be among the rows.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rows: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub row: Option<BTreeMap<String, Bound>>,
    /// In the bag tier: the whole result of the observation query.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub bag: Option<Vec<eval::Row>>,
}

/// The setup statements per engine; a missing entry is unloadable there, with the reason.
#[derive(Serialize, Clone, Debug, Default)]
pub struct Setup {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub gql: Option<Vec<String>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cypher: Option<Vec<String>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub turbolay: Option<serde_json::Value>,
    pub unloadable: BTreeMap<&'static str, String>,
}

// ---------------------------------------------------------------------------------------------
// label expressions and their models (22.5)

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum LabelExpr {
    Name(String),
    Wildcard,
    Not(Box<LabelExpr>),
    And(Box<LabelExpr>, Box<LabelExpr>),
    Or(Box<LabelExpr>, Box<LabelExpr>),
}

impl LabelExpr {
    /// 22.5 SR 2: whether `set` satisfies the expression.
    pub(crate) fn holds(&self, set: &BTreeSet<String>) -> bool {
        match self {
            LabelExpr::Name(n) => set.contains(n),
            LabelExpr::Wildcard => !set.is_empty(),
            LabelExpr::Not(e) => !e.holds(set),
            LabelExpr::And(a, b) => a.holds(set) && b.holds(set),
            LabelExpr::Or(a, b) => a.holds(set) || b.holds(set),
        }
    }

    fn names(&self, out: &mut BTreeSet<String>) {
        match self {
            LabelExpr::Name(n) => {
                out.insert(n.clone());
            }
            LabelExpr::Wildcard => {}
            LabelExpr::Not(e) => e.names(out),
            LabelExpr::And(a, b) | LabelExpr::Or(a, b) => {
                a.names(out);
                b.names(out);
            }
        }
    }
}

/// The smallest non-empty label set satisfying every expression, if one exists. Enumerates
/// subsets of the names mentioned plus one fresh name (so `!a` is met by the fresh one), by
/// size; every label set is non-empty (22.5 NOTE 399), so the fresh name stands in when
/// nothing is required.
pub(crate) fn label_model(exprs: &[LabelExpr], fresh: &str) -> Option<BTreeSet<String>> {
    let mut names = BTreeSet::new();
    for e in exprs {
        e.names(&mut names);
    }
    let mut names: Vec<String> = names.into_iter().collect();
    names.push(fresh.to_string());
    let n = names.len();
    let mut best: Option<BTreeSet<String>> = None;
    for mask in 1u64..(1u64 << n) {
        let set: BTreeSet<String> = (0..n)
            .filter(|i| mask & (1 << i) != 0)
            .map(|i| names[i].clone())
            .collect();
        if exprs.iter().all(|e| e.holds(&set))
            && best.as_ref().is_none_or(|b| set.len() < b.len())
        {
            best = Some(set);
        }
    }
    best
}

/// A label expression from its tree (16.8).
pub(crate) fn label_expr(p: &Plain) -> Option<LabelExpr> {
    let kids = logical(p);
    match def_name(p)? {
        "label expression" | "label term" | "label factor" | "label primary" => {
            label_expr(kids.first()?)
        }
        "label disjunction" => Some(LabelExpr::Or(
            Box::new(label_expr(kids.first()?)?),
            Box::new(label_expr(kids.get(2)?)?),
        )),
        "label conjunction" => Some(LabelExpr::And(
            Box::new(label_expr(kids.first()?)?),
            Box::new(label_expr(kids.get(2)?)?),
        )),
        "label negation" => Some(LabelExpr::Not(Box::new(label_expr(kids.get(1)?)?))),
        "parenthesized label expression" => label_expr(kids.get(1)?),
        "wildcard label" => Some(LabelExpr::Wildcard),
        "label name" => Some(LabelExpr::Name(identifier(p))),
        _ => None,
    }
}

// ---------------------------------------------------------------------------------------------
// tree helpers

pub(crate) fn def_name(p: &Plain) -> Option<&str> {
    match p {
        Plain::Def { name, .. } => Some(name),
        _ => None,
    }
}

/// The children of `p` with the synthetic grouping nodes of desugaring looked through: what
/// the standard's production lists.
pub(crate) fn logical(p: &Plain) -> Vec<&Plain> {
    let mut out = Vec::new();
    fn go<'a>(p: &'a Plain, out: &mut Vec<&'a Plain>) {
        if let Plain::Def { children, .. } = p {
            for c in children {
                match c {
                    Plain::Def {
                        synthetic: true, ..
                    } => go(c, out),
                    _ => out.push(c),
                }
            }
        }
    }
    go(p, &mut out);
    out
}

/// The first logical child that is a definition named `name`.
pub(crate) fn child<'a>(p: &'a Plain, name: &str) -> Option<&'a Plain> {
    logical(p).into_iter().find(|c| def_name(c) == Some(name))
}

/// Whether a keyword `kw` is a logical child.
pub(crate) fn has_kw(p: &Plain, kw: &str) -> bool {
    logical(p)
        .into_iter()
        .any(|c| matches!(c, Plain::Kw(k) if k == kw))
}

/// Every descendant definition named `name`, outermost first, not descending into one found.
pub(crate) fn find_all<'a>(p: &'a Plain, name: &str, out: &mut Vec<&'a Plain>) {
    if def_name(p) == Some(name) {
        out.push(p);
        return;
    }
    if let Plain::Def { children, .. } = p {
        children.iter().for_each(|c| find_all(c, name, out));
    }
}

/// The one descendant named `name` whose text is all of `p`'s text: `p` is exactly that
/// construct, reached through single-child productions.
pub(crate) fn exactly<'a>(p: &'a Plain, name: &str) -> Option<&'a Plain> {
    let text = p.text();
    let mut found = Vec::new();
    find_all(p, name, &mut found);
    found.into_iter().find(|f| f.text() == text)
}

/// The spelling of an identifier: a delimited one without its quotes and with a doubled
/// delimiter inside read as one (21.3: ```` is the name made of one backtick), else as is.
pub(crate) fn identifier(p: &Plain) -> String {
    let t = p.text();
    for q in ['`', '"'] {
        if t.len() >= 2 && t.starts_with(q) && t.ends_with(q) {
            return t[1..t.len() - 1].replace(&format!("{q}{q}"), &q.to_string());
        }
    }
    t
}

/// The variable an `<element variable declaration>` declares, and whether it is TEMP.
pub(crate) fn declared(p: &Plain) -> Option<(String, bool)> {
    let d = child(p, "element variable declaration")?;
    let temp = has_kw(d, "TEMP");
    let v = child(d, "element variable")?;
    Some((identifier(v), temp))
}

/// An `<unsigned integer>` in any radix, underscores dropped.
pub(crate) fn unsigned(text: &str) -> Option<u64> {
    let t: String = text.chars().filter(|c| *c != '_').collect();
    let lower = t.to_ascii_lowercase();
    if let Some(h) = lower.strip_prefix("0x") {
        u64::from_str_radix(h, 16).ok()
    } else if let Some(o) = lower.strip_prefix("0o") {
        u64::from_str_radix(o, 8).ok()
    } else if let Some(b) = lower.strip_prefix("0b") {
        u64::from_str_radix(b, 2).ok()
    } else {
        lower.parse().ok()
    }
}

/// A literal of the test classes from a `<value expression>` that is exactly one, else the
/// reason it is not.
pub(crate) fn literal(p: &Plain) -> Result<Value, String> {
    if exactly(p, "null literal").is_some() {
        return Ok(Value::Null);
    }
    if let Some(b) = exactly(p, "boolean literal") {
        return Ok(match b.text().to_ascii_uppercase().as_str() {
            "TRUE" => Value::Bool(true),
            "FALSE" => Value::Bool(false),
            _ => Value::Null,
        });
    }
    if let Some(s) = exactly(p, "character string literal") {
        let t = s.text();
        let q = t.chars().next().unwrap_or('\'');
        let body = &t[1..t.len() - 1];
        if body.contains('\\') {
            return Err("a string literal with an escape".to_string());
        }
        return Ok(Value::Str(body.replace(&format!("{q}{q}"), &q.to_string())));
    }
    if let Some(i) = exactly(p, "unsigned integer") {
        return unsigned(&i.text())
            .map(|v| Value::Int(v as i128))
            .ok_or_else(|| "an integer out of range".to_string());
    }
    if let Some(d) = exactly(p, "unsigned decimal in common notation") {
        return d
            .text()
            .replace('_', "")
            .parse()
            .map(Value::Float)
            .map_err(|_| "a decimal out of range".to_string());
    }
    if p.text().is_empty() {
        return Err("an empty value".to_string());
    }
    Err(format!("a value that is not a test literal: {}", p.text()))
}

// ---------------------------------------------------------------------------------------------
// the witness construction

/// One elementary, bracket or subpath binding of a path binding (22.2 GR 13).
#[derive(Clone, Debug)]
enum Bind {
    Node(usize),
    Edge(usize),
    /// A bracket symbol binding, by its depth, opening or closing a parenthesized pattern.
    Open,
    Close,
}

/// One item of a path term at one depth, before 16.7 SR 14's implicit nodes.
enum Item<'a> {
    /// A node pattern, or an implicit empty one.
    Node(Option<&'a Plain>),
    /// An edge pattern of this kind, with its full form's filler and, from a simplified
    /// pattern, the label expression it stands for.
    Edge {
        kind: EdgeKind,
        filler: Option<&'a Plain>,
        label: Option<LabelExpr>,
    },
    /// A quantified, questioned or parenthesized path primary.
    Group(&'a Plain),
    /// A group a simplified path pattern expression rewrites to (16.12 SR 6).
    Simple(SItem<'a>),
    /// A placeholder for the node an edge needs after it.
    Implicit,
}

impl Item<'_> {
    fn is_edge(&self) -> bool {
        matches!(self, Item::Edge { .. })
    }
    fn is_node(&self) -> bool {
        matches!(self, Item::Node(_))
    }
}

enum SItem<'a> {
    /// `( PREFIX contents SUFFIX )` with the delimiters' default edge kind.
    Paren(&'a Plain, EdgeKind),
    /// `( PREFIX tertiary SUFFIX ) GPQ` at its lower bound.
    Quant(&'a Plain, EdgeKind, u64),
    /// `( PREFIX tertiary SUFFIX ) ?`: zero iterations.
    Opt,
}

/// The requirements collected on one element before its labels are modelled.
#[derive(Clone, Debug, Default)]
struct Element {
    labels: Vec<LabelExpr>,
    /// `Some(v)`: the property has value `v`; `None`: the property is absent.
    properties: BTreeMap<String, Option<Value>>,
    /// Edges only.
    source: usize,
    target: usize,
    directed: bool,
    /// A node merged into another: where it went.
    merged_into: Option<usize>,
}

/// What a variable is bound to while a pattern is walked.
#[derive(Clone, Debug)]
enum Slot {
    Node(usize),
    Edge(usize),
    Path(Vec<usize>),
    List(Vec<Bound>),
    Null,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Mode {
    Walk,
    Trail,
    Simple,
    Acyclic,
}

pub struct Builder {
    nodes: Vec<Element>,
    edges: Vec<Element>,
    vars: BTreeMap<String, Slot>,
    /// Unconditional singleton variables bound so far, to be joined on by a later pattern.
    unsat: Option<String>,
    why: Vec<String>,
    mode_default: MatchModeDefault,
    different_edges: bool,
    fresh_labels: usize,
}

impl Builder {
    pub fn new(mode_default: MatchModeDefault) -> Self {
        Builder {
            nodes: Vec::new(),
            edges: Vec::new(),
            vars: BTreeMap::new(),
            unsat: None,
            why: Vec::new(),
            mode_default,
            different_edges: false,
            fresh_labels: 0,
        }
    }

    fn fail(&mut self, why: String) {
        if self.unsat.is_none() {
            self.unsat = Some(why);
        }
    }

    fn out_of_core(&mut self, why: impl Into<String>) {
        let why = why.into();
        if !self.why.contains(&why) {
            self.why.push(why);
        }
    }

    fn canon(&self, mut n: usize) -> usize {
        while let Some(m) = self.nodes[n].merged_into {
            n = m;
        }
        n
    }

    fn new_node(&mut self) -> usize {
        self.nodes.push(Element::default());
        self.nodes.len() - 1
    }

    fn new_edge(&mut self, source: usize, target: usize, directed: bool) -> usize {
        self.edges.push(Element {
            source,
            target,
            directed,
            ..Element::default()
        });
        self.edges.len() - 1
    }

    /// Two node bindings that must be one node (22.2 GR 16 b, 16.4 GR 7): `b` goes into `a`.
    fn merge(&mut self, a: usize, b: usize) -> usize {
        let (a, b) = (self.canon(a), self.canon(b));
        if a == b {
            return a;
        }
        let moved = std::mem::take(&mut self.nodes[b]);
        self.nodes[b].merged_into = Some(a);
        self.nodes[a].labels.extend(moved.labels);
        for (k, v) in moved.properties {
            self.require_property(true, a, k, v);
        }
        for slot in self.vars.values_mut() {
            if let Slot::Node(n) = slot {
                if *n == b {
                    *n = a;
                }
            }
        }
        a
    }

    fn require_property(&mut self, node: bool, id: usize, key: String, value: Option<Value>) {
        let id = if node { self.canon(id) } else { id };
        let element = if node {
            &mut self.nodes[id]
        } else {
            &mut self.edges[id]
        };
        match element.properties.get(&key) {
            Some(have) if *have != value => {
                let why = format!("two requirements on property {key} disagree");
                self.fail(why);
            }
            _ => {
                element.properties.insert(key, value);
            }
        }
    }

    fn require_label(&mut self, node: bool, id: usize, e: LabelExpr) {
        let id = if node { self.canon(id) } else { id };
        let element = if node {
            &mut self.nodes[id]
        } else {
            &mut self.edges[id]
        };
        element.labels.push(e);
    }

    /// The filler of an element pattern applied to element `id`: its variable, its label
    /// expression, its property specification or where clause (16.7 SR 12).
    fn filler(&mut self, p: &Plain, node: bool, id: usize) {
        let Some(filler) = child(p, "element pattern filler") else {
            return;
        };
        if let Some((v, temp)) = declared(filler) {
            self.bind_var(&v, temp, node, id);
        }
        if let Some(ile) = child(filler, "is label expression") {
            match ile
                .text()
                .is_empty()
                .then_some(None)
                .unwrap_or_else(|| child(ile, "label expression").and_then(label_expr))
            {
                Some(e) => self.require_label(node, id, e),
                None => self.out_of_core("a label expression that could not be read"),
            }
        }
        if let Some(pred) = child(filler, "element pattern predicate") {
            if let Some(spec) = child(pred, "element property specification") {
                let mut pairs = Vec::new();
                find_all(spec, "property key value pair", &mut pairs);
                for pair in pairs {
                    let kids = logical(pair);
                    let (Some(name), Some(expr)) = (kids.first(), kids.get(2)) else {
                        continue;
                    };
                    let key = identifier(name);
                    match literal(expr) {
                        // `x.k = NULL` is never true (19.3): no graph matches.
                        Ok(Value::Null) => self.fail(format!("{{ {key} : NULL }} never holds")),
                        Ok(v) => self.require_property(node, id, key, Some(v)),
                        Err(why) => self.out_of_core(format!("a property value is {why}")),
                    }
                }
            }
            if let Some(w) = child(pred, "element pattern where clause") {
                if let Some(cond) = child(w, "search condition") {
                    self.where_clause(cond);
                }
            }
        }
    }

    /// A variable declared by an element pattern: a second declaration of a singleton binds
    /// the same element (16.4 GR 7), which for nodes is a merge and for edges depends on the
    /// match mode (16.4 NOTE 227).
    fn bind_var(&mut self, v: &str, temp: bool, node: bool, id: usize) {
        if temp {
            // Dropped by REDUCE before the record is built (22.2 GR 14 d, e).
            return;
        }
        match self.vars.get(v).cloned() {
            None => {
                self.vars.insert(
                    v.to_string(),
                    if node { Slot::Node(id) } else { Slot::Edge(id) },
                );
            }
            Some(Slot::Node(n)) if node => {
                self.merge(n, id);
            }
            Some(Slot::Edge(e)) if !node => {
                if e != id {
                    match (self.different_edges, self.mode_default) {
                        (true, _) => self.fail(format!(
                            "edge variable {v} declared twice under DIFFERENT EDGES"
                        )),
                        (false, MatchModeDefault::RepeatableElements) => self.out_of_core(
                            format!("edge variable {v} declared twice: one edge bound twice"),
                        ),
                        (false, _) => self.out_of_core(format!(
                            "edge variable {v} declared twice: the answer depends on ID086"
                        )),
                    }
                }
            }
            Some(_) => self.out_of_core(format!("variable {v} bound as two kinds")),
        }
    }

    /// `W` of a `<graph pattern>`: match mode, every path pattern, the where clause.
    pub fn graph_pattern(&mut self, p: &Plain, incoming_different_edges: Option<bool>) {
        self.different_edges = match child(p, "match mode") {
            Some(m) if child(m, "different edges match mode").is_some() => true,
            Some(_) => false,
            None => incoming_different_edges.unwrap_or(match self.mode_default {
                MatchModeDefault::DifferentEdges => true,
                MatchModeDefault::RepeatableElements => false,
                MatchModeDefault::Portable => false,
            }),
        };
        if child(p, "match mode").is_none() && self.mode_default == MatchModeDefault::Portable {
            // Nothing in the witness depends on the mode unless an edge variable repeats,
            // where `bind_var` says so.
        }
        let keep = child(p, "keep clause").and_then(|k| child(k, "path pattern prefix"));
        if let Some(list) = child(p, "path pattern list") {
            let mut patterns = Vec::new();
            find_all(list, "path pattern", &mut patterns);
            for pp in patterns {
                self.path_pattern(pp, keep);
            }
        }
        if let Some(w) = child(p, "graph pattern where clause") {
            if let Some(cond) = child(w, "search condition") {
                self.where_clause(cond);
            }
        }
    }

    fn path_pattern(&mut self, p: &Plain, keep: Option<&Plain>) {
        let prefix = child(p, "path pattern prefix").or(keep);
        let mut mode = Mode::Walk;
        if let Some(prefix) = prefix {
            if child(prefix, "path search prefix").is_some() {
                self.out_of_core(
                    "a selective path pattern: the witness is a match, the selection needs the evaluator",
                );
            }
            let mut modes = Vec::new();
            find_all(prefix, "path mode", &mut modes);
            if let Some(m) = modes.first() {
                mode = path_mode(m);
            }
        }
        let Some(expr) = child(p, "path pattern expression") else {
            return;
        };
        let binding = self.path_pattern_expression(expr);
        self.check_mode(&binding, mode);
        if let Some(decl) = child(p, "path variable declaration") {
            if let Some(v) = child(decl, "path variable") {
                let path = self.compressed(&binding);
                self.vars.insert(identifier(v), Slot::Path(path));
            }
        }
    }

    /// The extracted path (22.2 GR 13 d): node and edge ids, consecutive node bindings
    /// collapsed.
    fn compressed(&self, binding: &[Bind]) -> Vec<usize> {
        let mut out: Vec<usize> = Vec::new();
        let mut last_node = false;
        for b in binding {
            match b {
                Bind::Node(n) => {
                    let n = self.canon(*n);
                    if !last_node {
                        out.push(n);
                    }
                    last_node = true;
                }
                Bind::Edge(e) => {
                    out.push(*e);
                    last_node = false;
                }
                _ => {}
            }
        }
        out
    }

    /// 22.2 GR 16 d: a restrictive mode over the binding of one parenthesized pattern.
    fn check_mode(&mut self, binding: &[Bind], mode: Mode) {
        if mode == Mode::Walk {
            return;
        }
        let path = self.compressed(binding);
        let nodes: Vec<usize> = path.iter().step_by(2).copied().collect();
        let edges: Vec<usize> = path.iter().skip(1).step_by(2).copied().collect();
        let repeats = |xs: &[usize]| xs.iter().collect::<BTreeSet<_>>().len() < xs.len();
        let violated = match mode {
            Mode::Walk => false,
            Mode::Trail => repeats(&edges),
            Mode::Acyclic => repeats(&nodes),
            Mode::Simple => {
                let inner = if nodes.len() > 2 {
                    &nodes[1..nodes.len() - 1]
                } else {
                    &nodes[..]
                };
                repeats(inner)
                    || nodes.len() > 2
                        && inner.contains(&nodes[0])
                        && nodes[0] != nodes[nodes.len() - 1]
                    || nodes.len() > 2 && inner.contains(&nodes[nodes.len() - 1])
            }
        };
        if violated {
            self.fail(format!(
                "a variable bound twice under {mode:?}: no path can match (16.4 NOTE 224)"
            ));
        }
    }

    fn path_pattern_expression(&mut self, p: &Plain) -> Vec<Bind> {
        let kids = logical(p);
        let Some(first) = kids.first() else {
            return Vec::new();
        };
        match def_name(first) {
            Some("path term") => self.path_term(first),
            Some("path pattern union") | Some("path multiset alternation") => {
                // 22.3 GR 3 h: the union of the operands' matches; the witness is the first
                // operand's. Variables the other operands declare are conditional singletons
                // and bind null (16.7 SR 22 d iv).
                let terms: Vec<&Plain> = logical(first)
                    .into_iter()
                    .filter(|c| def_name(c) == Some("path term"))
                    .collect();
                let binding = terms
                    .first()
                    .map(|t| self.path_term(t))
                    .unwrap_or_default();
                for t in terms.iter().skip(1) {
                    let mut decls = Vec::new();
                    find_all(t, "element variable declaration", &mut decls);
                    for d in decls {
                        if let Some(v) = child(d, "element variable") {
                            self.vars.entry(identifier(v)).or_insert(Slot::Null);
                        }
                    }
                }
                binding
            }
            _ => Vec::new(),
        }
    }

    /// The items of a path term at this depth, in order (16.7 SR 14 is applied over them).
    fn items<'a>(&mut self, p: &'a Plain, out: &mut Vec<Item<'a>>) {
        match def_name(p) {
            Some("path term") | Some("path concatenation") | Some("path factor")
            | Some("path primary") => {
                for c in logical(p) {
                    self.items(c, out);
                }
            }
            Some("element pattern") => {
                if child(p, "edge pattern").is_some() {
                    let ep = child(p, "edge pattern").expect("an edge pattern");
                    let (kind, filler) = edge_kind(ep);
                    out.push(Item::Edge {
                        kind,
                        filler,
                        label: None,
                    });
                } else {
                    out.push(Item::Node(Some(p)));
                }
            }
            Some("quantified path primary")
            | Some("questioned path primary")
            | Some("parenthesized path pattern expression") => out.push(Item::Group(p)),
            Some("simplified path pattern expression") => {
                let kind = simplified_kind(p);
                // The contents sit under the defaulting variant that names the delimiters.
                let mut found = Vec::new();
                find_all(p, "simplified contents", &mut found);
                if let Some(contents) = found.first().copied() {
                    // 16.12 SR 5: the expression is parenthesized once, then rewritten.
                    out.push(Item::Simple(SItem::Paren(contents, kind)));
                }
            }
            _ => {}
        }
    }

    /// The items a `<simplified contents>` stands for after 16.12 SR 6, every edge with the
    /// delimiters' default kind unless overridden.
    fn simplified_items<'a>(&mut self, p: &'a Plain, kind: EdgeKind, out: &mut Vec<Item<'a>>) {
        match def_name(p) {
            Some("simplified contents") | Some("simplified term") | Some("simplified factor low")
            | Some("simplified factor high") | Some("simplified tertiary")
            | Some("simplified secondary") => {
                let kids = logical(p);
                // A union or alternation: the first operand is the witness (6 b i, ii); a
                // simplified pattern declares no variables, so nothing binds null.
                if let Some(first) = kids.first() {
                    match def_name(first) {
                        Some("simplified path union") | Some("simplified multiset alternation") => {
                            if let Some(t) = logical(first).into_iter().find(|c| def_name(c) == Some("simplified term")) {
                                self.simplified_items(t, kind, out);
                            }
                        }
                        Some("simplified concatenation") => {
                            // 6 b iii: `PREFIX ST SUFFIX PREFIX SFL SUFFIX`.
                            for c in logical(first) {
                                if def_name(c).is_some() {
                                    self.simplified_items(c, kind, out);
                                }
                            }
                        }
                        Some("simplified conjunction") | Some("simplified negation") => {
                            // 6 b iv, viii: one edge pattern whose label expression it is.
                            match simplified_label(first) {
                                Some(e) => out.push(Item::Edge { kind, filler: None, label: Some(e) }),
                                None => self.out_of_core("a simplified conjunction that is not a label expression"),
                            }
                        }
                        Some("simplified quantified") => {
                            let tertiary = child(first, "simplified tertiary");
                            let lower = child(first, "graph pattern quantifier").and_then(quantifier_lower);
                            match (tertiary, lower) {
                                (Some(t), Some(l)) => out.push(Item::Simple(SItem::Quant(t, kind, l))),
                                _ => self.out_of_core("a simplified quantifier that could not be read"),
                            }
                        }
                        Some("simplified questioned") => out.push(Item::Simple(SItem::Opt)),
                        Some("simplified direction override") => {
                            // 6 b vii: the override's kind, its secondary as the label expression.
                            let mut overridden = kind;
                            let mut secondary = None;
                            for o in logical(first) {
                                overridden = match def_name(o) {
                                    Some("simplified override left") => EdgeKind::Left,
                                    Some("simplified override undirected") => EdgeKind::Undirected,
                                    Some("simplified override right") => EdgeKind::Right,
                                    Some("simplified override left or undirected") => EdgeKind::LeftOrUndirected,
                                    Some("simplified override undirected or right") => EdgeKind::UndirectedOrRight,
                                    Some("simplified override left or right") => EdgeKind::LeftOrRight,
                                    Some("simplified override any direction") => EdgeKind::Any,
                                    _ => continue,
                                };
                                secondary = child(o, "simplified secondary");
                            }
                            match secondary.and_then(simplified_label) {
                                Some(e) => out.push(Item::Edge { kind: overridden, filler: None, label: Some(e) }),
                                None => self.out_of_core("a direction override whose contents are not a label expression"),
                            }
                        }
                        Some("simplified primary") => {
                            // 6 b ix: a label name is an edge pattern; parentheses nest.
                            if let Some(n) = child(first, "label name") {
                                out.push(Item::Edge { kind, filler: None, label: Some(LabelExpr::Name(identifier(n))) });
                            } else if let Some(inner) = child(first, "simplified contents") {
                                out.push(Item::Simple(SItem::Paren(inner, kind)));
                            }
                        }
                        Some(_) => self.simplified_items(first, kind, out),
                        None => {}
                    }
                }
            }
            Some(_) => {
                for c in logical(p) {
                    if def_name(c).is_some() {
                        self.simplified_items(c, kind, out);
                    }
                }
            }
            None => {}
        }
    }

    fn path_term(&mut self, p: &Plain) -> Vec<Bind> {
        let mut items = Vec::new();
        self.items(p, &mut items);
        self.term_items(items)
    }

    /// The binding of a sequence of items at one depth: 16.7 SR 14 b, c, d put an empty node
    /// pattern before and after every edge pattern that has none; adjacent node bindings are
    /// one node (22.2 GR 16 b).
    fn term_items(&mut self, items: Vec<Item<'_>>) -> Vec<Bind> {
        let mut binding: Vec<Bind> = Vec::new();
        let mut sequence: Vec<Item<'_>> = Vec::new();
        for item in items {
            let edge = item.is_edge();
            if edge && !sequence.last().is_some_and(Item::is_node) {
                sequence.push(Item::Node(None));
            }
            sequence.push(item);
            if edge {
                // Removed again below when the next item is a node pattern.
                sequence.push(Item::Implicit);
            }
        }
        // An implicit node right before an explicit node pattern is that node pattern.
        let mut cleaned: Vec<Item<'_>> = Vec::new();
        let mut iter = sequence.into_iter().peekable();
        while let Some(item) = iter.next() {
            if matches!(item, Item::Implicit) {
                if iter.peek().is_some_and(Item::is_node) {
                    continue;
                }
                cleaned.push(Item::Node(None));
            } else {
                cleaned.push(item);
            }
        }
        let mut pending_edge: Option<(usize, EdgeKind)> = None;
        for item in cleaned {
            match item {
                Item::Implicit => unreachable!("replaced above"),
                Item::Node(pattern) => {
                    let id = self.node_here(&mut binding, pattern);
                    self.close_edge(&mut pending_edge, &binding, id);
                }
                Item::Edge { kind, filler, label } => {
                    let Bind::Node(left) = last_element(&binding).expect("a node before an edge")
                    else {
                        unreachable!("alternation after SR 14")
                    };
                    let left = self.canon(left);
                    let id = self.new_edge(left, left, kind != EdgeKind::Undirected);
                    if let Some(filler) = filler {
                        self.filler(filler, false, id);
                    }
                    if let Some(e) = label {
                        self.require_label(false, id, e);
                    }
                    binding.push(Bind::Edge(id));
                    pending_edge = Some((id, kind));
                }
                Item::Group(p) => {
                    let group = self.group(p);
                    self.append_group(&mut binding, group);
                }
                Item::Simple(s) => {
                    let group = self.simple_group(s);
                    self.append_group(&mut binding, group);
                }
            }
        }
        binding
    }

    /// A group's binding after `binding`: a node before and the group's first node are not
    /// separable, so one node (22.2 GR 16 b).
    fn append_group(&mut self, binding: &mut Vec<Bind>, group: Vec<Bind>) {
        if let (Some(Bind::Node(prev)), Some(Bind::Node(first))) =
            (last_element(binding), first_element(&group))
        {
            self.merge(prev, first);
        }
        binding.extend(group);
    }

    /// The binding of a simplified group: a parenthesized expression (bracket bindings around
    /// its contents), a quantified one at its lower bound, a questioned one empty.
    fn simple_group(&mut self, s: SItem<'_>) -> Vec<Bind> {
        match s {
            SItem::Paren(contents, kind) => {
                let mut items = Vec::new();
                self.simplified_items(contents, kind, &mut items);
                let mut binding = vec![Bind::Open];
                binding.extend(self.term_items(items));
                binding.push(Bind::Close);
                binding
            }
            SItem::Quant(tertiary, kind, lower) => {
                if lower > 64 {
                    self.out_of_core(format!("a quantifier lower bound of {lower}"));
                    return Vec::new();
                }
                let mut binding: Vec<Bind> = Vec::new();
                for _ in 0..lower {
                    let mut items = Vec::new();
                    self.simplified_items(tertiary, kind, &mut items);
                    let mut iteration = vec![Bind::Open];
                    iteration.extend(self.term_items(items));
                    iteration.push(Bind::Close);
                    self.append_group(&mut binding, iteration);
                }
                binding
            }
            SItem::Opt => Vec::new(),
        }
    }

    /// A node pattern bound at the end of `binding`: the node before it, if any and not
    /// separable, is the same node (22.2 GR 16 b).
    fn node_here(&mut self, binding: &mut Vec<Bind>, pattern: Option<&Plain>) -> usize {
        let id = match last_element(binding) {
            Some(Bind::Node(prev)) => self.canon(prev),
            _ => self.new_node(),
        };
        if let Some(pattern) = pattern {
            let np = child(pattern, "node pattern").expect("a node pattern");
            self.filler(np, true, id);
        }
        binding.push(Bind::Node(id));
        self.canon(id)
    }

    /// The edge before `right` gets its right node and the direction its kind needs (22.3
    /// GR 3 f iii 2 D): one proposition of L, U, R made true.
    fn close_edge(&mut self, pending: &mut Option<(usize, EdgeKind)>, _: &[Bind], right: usize) {
        let Some((id, kind)) = pending.take() else {
            return;
        };
        let right = self.canon(right);
        let left = self.canon(self.edges[id].source);
        let (source, target, directed) = match kind {
            EdgeKind::Left | EdgeKind::LeftOrUndirected => (right, left, true),
            EdgeKind::Undirected => (left, right, false),
            EdgeKind::Right
            | EdgeKind::UndirectedOrRight
            | EdgeKind::LeftOrRight
            | EdgeKind::Any => (left, right, true),
        };
        let e = &mut self.edges[id];
        e.source = source;
        e.target = target;
        e.directed = directed;
    }

    /// A quantified, questioned or parenthesized item: its binding, possibly empty.
    fn group(&mut self, p: &Plain) -> Vec<Bind> {
        match def_name(p) {
            Some("parenthesized path pattern expression") => self.parenthesized(p),
            Some("questioned path primary") => {
                // 22.3 GR 3 d: zero iterations is a match; its variables bind null.
                self.declare_null(p);
                Vec::new()
            }
            Some("quantified path primary") => {
                let Some(q) = child(p, "graph pattern quantifier") else {
                    return Vec::new();
                };
                let lower = quantifier_lower(q);
                let Some(lower) = lower else {
                    self.out_of_core("a quantifier whose lower bound could not be read");
                    return Vec::new();
                };
                if lower > 64 {
                    self.out_of_core(format!("a quantifier lower bound of {lower}"));
                    return Vec::new();
                }
                let Some(primary) = child(p, "path primary") else {
                    return Vec::new();
                };
                // Every variable under the quantifier is a group variable: a list with one
                // entry per iteration (16.7 SR 22 e).
                let mut decls = Vec::new();
                find_all(primary, "element variable declaration", &mut decls);
                let names: BTreeSet<String> = decls
                    .iter()
                    .filter_map(|d| child(d, "element variable").map(identifier))
                    .collect();
                let outer: BTreeMap<String, Slot> = names
                    .iter()
                    .filter_map(|n| self.vars.remove(n).map(|s| (n.clone(), s)))
                    .collect();
                let mut lists: BTreeMap<String, Vec<Bound>> =
                    names.iter().map(|n| (n.clone(), Vec::new())).collect();
                let mut binding: Vec<Bind> = Vec::new();
                for _ in 0..lower {
                    for n in &names {
                        self.vars.remove(n);
                    }
                    let mut iteration = self.primary(primary);
                    if let (Some(Bind::Node(prev)), Some(Bind::Node(first))) =
                        (last_element(&binding), first_element(&iteration))
                    {
                        self.merge(prev, first);
                    }
                    binding.append(&mut iteration);
                    for n in &names {
                        let v = self.vars.remove(n).map_or(Bound::Null, |s| self.bound(&s));
                        lists.get_mut(n).expect("listed").push(v);
                    }
                }
                for (n, list) in lists {
                    self.vars.insert(n, Slot::List(list));
                }
                for (n, s) in outer {
                    // A group variable declared again outside: the name is one variable of
                    // two degrees, which 16.7 SR 22 forbids; keep the outer binding.
                    self.vars.insert(n, s);
                }
                binding
            }
            _ => Vec::new(),
        }
    }

    fn primary(&mut self, p: &Plain) -> Vec<Bind> {
        // 16.7 SR 14 a: a quantified edge pattern is a parenthesized one; a simplified
        // expression is parenthesized by 16.12 SR 5.
        for c in logical(p) {
            match def_name(c) {
                Some("parenthesized path pattern expression") => return self.parenthesized(c),
                Some("element pattern") | Some("simplified path pattern expression") => {
                    return self.path_term(c);
                }
                _ => {}
            }
        }
        Vec::new()
    }

    fn parenthesized(&mut self, p: &Plain) -> Vec<Bind> {
        let mode = child(p, "path mode prefix")
            .and_then(|m| child(m, "path mode"))
            .map_or(Mode::Walk, path_mode);
        let mut binding = vec![Bind::Open];
        if let Some(expr) = child(p, "path pattern expression") {
            binding.extend(self.path_pattern_expression(expr));
        }
        if let Some(w) = child(p, "parenthesized path pattern where clause") {
            if let Some(cond) = child(w, "search condition") {
                self.where_clause(cond);
            }
        }
        binding.push(Bind::Close);
        self.check_mode(&binding, mode);
        if let Some(decl) = child(p, "subpath variable declaration") {
            if let Some(v) = child(decl, "subpath variable") {
                let path = self.compressed(&binding);
                self.vars.insert(identifier(v), Slot::Path(path));
            }
        }
        binding
    }

    fn declare_null(&mut self, p: &Plain) {
        let mut decls = Vec::new();
        find_all(p, "element variable declaration", &mut decls);
        for d in decls {
            if let Some(v) = child(d, "element variable") {
                self.vars.entry(identifier(v)).or_insert(Slot::Null);
            }
        }
    }

    /// A where clause of the core: a conjunction of predicates each made true on the
    /// witness. Anything else leaves the core.
    fn where_clause(&mut self, cond: &Plain) {
        let mut conjuncts = Vec::new();
        self.conjuncts(cond, &mut conjuncts);
        for c in conjuncts {
            self.predicate(c);
        }
    }

    fn conjuncts<'a>(&mut self, p: &'a Plain, out: &mut Vec<&'a Plain>) {
        match def_name(p) {
            Some("search condition") | Some("boolean primary") | Some("boolean predicand")
                | Some("parenthesized boolean value expression") => {
                for c in logical(p) {
                    if def_name(c).is_some() {
                        self.conjuncts(c, out);
                    }
                }
            }
            Some("boolean value expression") => {
                if has_kw(p, "OR") || has_kw(p, "XOR") {
                    self.out_of_core("a where clause with OR or XOR");
                    return;
                }
                for c in logical(p) {
                    self.conjuncts(c, out);
                }
            }
            Some("boolean term") => {
                for c in logical(p) {
                    if def_name(c).is_some() {
                        self.conjuncts(c, out);
                    }
                }
            }
            Some("boolean factor") => {
                if has_kw(p, "NOT") {
                    self.out_of_core("a where clause with NOT");
                    return;
                }
                for c in logical(p) {
                    self.conjuncts(c, out);
                }
            }
            Some("boolean test") => {
                if has_kw(p, "IS") {
                    self.out_of_core("a where clause with IS TRUE/FALSE/UNKNOWN");
                    return;
                }
                for c in logical(p) {
                    self.conjuncts(c, out);
                }
            }
            Some("predicate") => out.push(p),
            Some("non-parenthesized value expression primary") => {
                self.out_of_core(format!("a where clause that is a value: {}", p.text()));
            }
            Some(_) => {
                for c in logical(p) {
                    self.conjuncts(c, out);
                }
            }
            None => {}
        }
    }

    /// The element a reference names, by the variable's current binding.
    fn element_of(&self, p: &Plain) -> Option<(bool, usize)> {
        let name = exactly(p, "binding variable reference").map(identifier)?;
        match self.vars.get(&name)? {
            Slot::Node(n) => Some((true, self.canon(*n))),
            Slot::Edge(e) => Some((false, *e)),
            _ => None,
        }
    }

    fn predicate(&mut self, p: &Plain) {
        let Some(inner) = logical(p).into_iter().find(|c| def_name(c).is_some()) else {
            return;
        };
        let text = p.text();
        match def_name(inner) {
            Some("comparison predicate") => {
                let kids = logical(inner);
                let (Some(left), Some(part2)) = (kids.first(), kids.get(1)) else {
                    return;
                };
                let right = child(part2, "comparison predicand");
                let op = child(part2, "comp op").map(|o| o.text());
                let Some(right) = right else { return };
                if op.as_deref() != Some("=") {
                    self.out_of_core(format!("a comparison that is not =: {text}"));
                    return;
                }
                let (reference, value) = match (exactly(left, "property reference"), exactly(right, "property reference")) {
                    (Some(r), None) => (r, right),
                    (None, Some(r)) => (r, *left),
                    _ => {
                        self.out_of_core(format!("a comparison that is not property = literal: {text}"));
                        return;
                    }
                };
                let kids = logical(reference);
                let (Some(source), Some(name)) = (kids.first(), kids.get(2)) else {
                    return;
                };
                let Some((node, id)) = self.element_of(source) else {
                    self.out_of_core(format!("a property of something not an element variable: {text}"));
                    return;
                };
                match literal(value) {
                    Ok(Value::Null) => self.fail(format!("{text} never holds")),
                    Ok(v) => self.require_property(node, id, identifier(name), Some(v)),
                    Err(why) => self.out_of_core(format!("a compared value is {why}")),
                }
            }
            Some("null predicate") => {
                let kids = logical(inner);
                let (Some(primary), Some(part2)) = (kids.first(), kids.get(1)) else {
                    return;
                };
                let negated = has_kw(part2, "NOT");
                let Some(reference) = exactly(primary, "property reference") else {
                    self.out_of_core(format!("a null predicate not on a property: {text}"));
                    return;
                };
                let kids = logical(reference);
                let (Some(source), Some(name)) = (kids.first(), kids.get(2)) else {
                    return;
                };
                let Some((node, id)) = self.element_of(source) else {
                    self.out_of_core(format!("a property of something not an element variable: {text}"));
                    return;
                };
                let key = identifier(name);
                if negated {
                    let element = if node { &self.nodes[id] } else { &self.edges[id] };
                    if !matches!(element.properties.get(&key), Some(Some(_))) {
                        self.require_property(node, id, key, Some(Value::Int(1)));
                    }
                } else {
                    self.require_property(node, id, key, None);
                }
            }
            Some("labeled predicate") => {
                let kids = logical(inner);
                let (Some(reference), Some(part2)) = (kids.first(), kids.get(1)) else {
                    return;
                };
                let Some((node, id)) = self.element_of(reference) else {
                    self.out_of_core(format!("a labeled predicate not on an element variable: {text}"));
                    return;
                };
                let negated = child(part2, "is labeled or colon").is_some_and(|c| has_kw(c, "NOT"));
                match child(part2, "label expression").and_then(label_expr) {
                    Some(e) => {
                        let e = if negated { LabelExpr::Not(Box::new(e)) } else { e };
                        self.require_label(node, id, e);
                    }
                    None => self.out_of_core("a label expression that could not be read"),
                }
            }
            Some("directed predicate") => {
                let kids = logical(inner);
                let (Some(reference), Some(part2)) = (kids.first(), kids.get(1)) else {
                    return;
                };
                let Some((false, id)) = self.element_of(reference) else {
                    self.out_of_core(format!("IS DIRECTED not on an edge variable: {text}"));
                    return;
                };
                let negated = has_kw(part2, "NOT");
                if self.edges[id].directed == negated {
                    self.fail(format!("{text} contradicts the edge pattern's direction"));
                }
            }
            Some("source/destination predicate") => {
                let kids = logical(inner);
                let (Some(node_ref), Some(part2)) = (kids.first(), kids.get(1)) else {
                    return;
                };
                let Some((true, n)) = self.element_of(node_ref) else {
                    self.out_of_core(format!("a source/destination predicate not on a node variable: {text}"));
                    return;
                };
                let negated = has_kw(part2, "NOT");
                let wants_source = has_kw(part2, "SOURCE");
                let Some(edge_ref) = child(part2, "edge reference") else {
                    return;
                };
                let Some((false, e)) = self.element_of(edge_ref) else {
                    self.out_of_core(format!("a source/destination predicate not on an edge variable: {text}"));
                    return;
                };
                let edge = &self.edges[e];
                let holds = if wants_source {
                    self.canon(edge.source) == n
                } else {
                    self.canon(edge.target) == n
                };
                // 19.10: on an undirected edge both nodes are source and destination.
                let holds = holds
                    || !edge.directed
                        && (self.canon(edge.source) == n || self.canon(edge.target) == n);
                if holds == negated {
                    self.fail(format!("{text} contradicts the edge pattern"));
                }
            }
            Some("property_exists predicate") => {
                let kids = logical(inner);
                let reference = kids.iter().find(|c| def_name(c) == Some("element variable reference"));
                let name = kids.iter().find(|c| def_name(c) == Some("property name"));
                let (Some(reference), Some(name)) = (reference, name) else {
                    return;
                };
                let Some((node, id)) = self.element_of(reference) else {
                    self.out_of_core(format!("PROPERTY_EXISTS not on an element variable: {text}"));
                    return;
                };
                let key = identifier(name);
                let element = if node { &self.nodes[id] } else { &self.edges[id] };
                if !matches!(element.properties.get(&key), Some(Some(_))) {
                    self.require_property(node, id, key, Some(Value::Int(1)));
                }
            }
            Some(other) => self.out_of_core(format!("a {other} in a where clause")),
            None => {}
        }
    }

    fn bound(&self, s: &Slot) -> Bound {
        match s {
            Slot::Node(n) => Bound::Node(self.canon(*n)),
            Slot::Edge(e) => Bound::Edge(*e),
            Slot::Path(p) => Bound::Path(p.iter().map(|&x| x).collect()),
            Slot::List(l) => Bound::List(l.clone()),
            Slot::Null => Bound::Null,
        }
    }

    /// The graph and the record: labels modelled, merged nodes compacted, ids renumbered
    /// with nodes first.
    pub fn finish(mut self) -> (Graph, BTreeMap<String, Bound>, Option<String>, Vec<String>) {
        let mut graph = Graph::default();
        let mut node_ids: BTreeMap<usize, usize> = BTreeMap::new();
        let mut unsat = self.unsat.take();
        let live: Vec<usize> = (0..self.nodes.len())
            .filter(|&i| self.nodes[i].merged_into.is_none())
            .collect();
        for &i in &live {
            let id = graph.nodes.len() + graph.edges.len();
            node_ids.insert(i, id);
            let fresh = format!("L{}", self.fresh_labels);
            self.fresh_labels += 1;
            let labels = match label_model(&self.nodes[i].labels, &fresh) {
                Some(m) => m,
                None => {
                    unsat.get_or_insert_with(|| {
                        "a node's label expressions have no model (22.5)".to_string()
                    });
                    // Every label set is non-empty (22.5 NOTE 399): the graph stays legal.
                    BTreeSet::from([fresh.clone()])
                }
            };
            let mut properties: BTreeMap<String, Value> = self.nodes[i]
                .properties
                .iter()
                .filter_map(|(k, v)| v.clone().map(|v| (k.clone(), v)))
                .collect();
            properties.insert(ID_PROPERTY.to_string(), Value::Int(id as i128));
            graph.nodes.push(Node {
                id,
                labels,
                properties,
            });
        }
        let base = graph.nodes.len();
        for (k, e) in self.edges.iter().enumerate() {
            let id = base + k;
            let fresh = format!("L{}", self.fresh_labels);
            self.fresh_labels += 1;
            let labels = match label_model(&e.labels, &fresh) {
                Some(m) => m,
                None => {
                    unsat.get_or_insert_with(|| {
                        "an edge's label expressions have no model (22.5)".to_string()
                    });
                    BTreeSet::from([fresh.clone()])
                }
            };
            let mut properties: BTreeMap<String, Value> = e
                .properties
                .iter()
                .filter_map(|(k, v)| v.clone().map(|v| (k.clone(), v)))
                .collect();
            properties.insert(ID_PROPERTY.to_string(), Value::Int(id as i128));
            graph.edges.push(Edge {
                id,
                source: node_ids[&self.canon(e.source)],
                target: node_ids[&self.canon(e.target)],
                labels,
                directed: e.directed,
                properties,
            });
        }
        let renumber = |b: &Bound| -> Bound {
            fn go(b: &Bound, node_ids: &BTreeMap<usize, usize>, base: usize) -> Bound {
                match b {
                    Bound::Node(n) => Bound::Node(node_ids[n]),
                    Bound::Edge(e) => Bound::Edge(base + e),
                    Bound::Path(p) => Bound::Path(
                        p.iter()
                            .enumerate()
                            .map(|(i, x)| if i % 2 == 0 { node_ids[x] } else { base + x })
                            .collect(),
                    ),
                    Bound::List(l) => Bound::List(l.iter().map(|x| go(x, node_ids, base)).collect()),
                    Bound::Null => Bound::Null,
                    Bound::Int(i) => Bound::Int(*i),
                }
            }
            go(b, &node_ids, base)
        };
        let record: BTreeMap<String, Bound> = self
            .vars
            .iter()
            .map(|(k, s)| (k.clone(), renumber(&self.bound(s))))
            .collect();
        (graph, record, unsat, self.why)
    }
}

fn last_element(binding: &[Bind]) -> Option<Bind> {
    binding
        .iter()
        .rev()
        .find(|b| matches!(b, Bind::Node(_) | Bind::Edge(_)))
        .cloned()
}

fn first_element(binding: &[Bind]) -> Option<Bind> {
    binding
        .iter()
        .find(|b| matches!(b, Bind::Node(_) | Bind::Edge(_)))
        .cloned()
}

pub(crate) fn path_mode(p: &Plain) -> Mode {
    match p.text().to_ascii_uppercase().as_str() {
        "TRAIL" => Mode::Trail,
        "SIMPLE" => Mode::Simple,
        "ACYCLIC" => Mode::Acyclic,
        _ => Mode::Walk,
    }
}

/// The lower bound of a quantifier: `*` 0, `+` 1, `{n}` n, `{m,n}` m, `{,n}` 0.
pub(crate) fn quantifier_lower(q: &Plain) -> Option<u64> {
    for c in logical(q) {
        match def_name(c) {
            Some("asterisk") => return Some(0),
            Some("plus sign") => return Some(1),
            Some("fixed quantifier") => {
                return child(c, "unsigned integer").and_then(|u| unsigned(&u.text()));
            }
            Some("general quantifier") => {
                return match child(c, "lower bound") {
                    Some(l) => unsigned(&l.text()),
                    None => Some(0),
                };
            }
            _ => {}
        }
    }
    match q.text().as_str() {
        "*" => Some(0),
        "+" => Some(1),
        _ => None,
    }
}

/// 16.12 Table 3: the default edge kind of a simplified path pattern's delimiters.
pub(crate) fn simplified_kind(p: &Plain) -> EdgeKind {
    for c in logical(p) {
        return match def_name(c) {
            Some("simplified defaulting left") => EdgeKind::Left,
            Some("simplified defaulting undirected") => EdgeKind::Undirected,
            Some("simplified defaulting right") => EdgeKind::Right,
            Some("simplified defaulting left or undirected") => EdgeKind::LeftOrUndirected,
            Some("simplified defaulting undirected or right") => EdgeKind::UndirectedOrRight,
            Some("simplified defaulting left or right") => EdgeKind::LeftOrRight,
            Some("simplified defaulting any direction") => EdgeKind::Any,
            _ => continue,
        };
    }
    EdgeKind::Any
}

/// A simplified conjunction, negation, primary or union read as the label expression it
/// becomes (16.12 NOTE 255, 257): `None` where it holds something a label expression cannot
/// (a concatenation, a quantifier, an override).
pub(crate) fn simplified_label(p: &Plain) -> Option<LabelExpr> {
    let kids = logical(p);
    match def_name(p)? {
        "simplified contents" | "simplified term" | "simplified factor low"
        | "simplified factor high" | "simplified tertiary" | "simplified secondary" => {
            simplified_label(kids.first()?)
        }
        "simplified path union" | "simplified multiset alternation" => {
            let mut terms = kids.into_iter().filter(|c| def_name(c) == Some("simplified term"));
            let mut e = simplified_label(terms.next()?)?;
            for t in terms {
                e = LabelExpr::Or(Box::new(e), Box::new(simplified_label(t)?));
            }
            Some(e)
        }
        "simplified conjunction" => Some(LabelExpr::And(
            Box::new(simplified_label(kids.first()?)?),
            Box::new(simplified_label(kids.get(2)?)?),
        )),
        "simplified negation" => Some(LabelExpr::Not(Box::new(simplified_label(kids.get(1)?)?))),
        "simplified primary" => {
            if let Some(n) = child(p, "label name") {
                Some(LabelExpr::Name(identifier(n)))
            } else {
                simplified_label(child(p, "simplified contents")?)
            }
        }
        _ => None,
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum EdgeKind {
    Left,
    Undirected,
    Right,
    LeftOrUndirected,
    UndirectedOrRight,
    LeftOrRight,
    Any,
}

/// The kind of an edge pattern (16.7 SR 14 e maps abbreviated ones to full ones) and its
/// full form's node, if any, whose filler applies.
pub(crate) fn edge_kind(ep: &Plain) -> (EdgeKind, Option<&Plain>) {
    if let Some(full) = child(ep, "full edge pattern") {
        for c in logical(full) {
            let kind = match def_name(c) {
                Some("full edge pointing left") => EdgeKind::Left,
                Some("full edge undirected") => EdgeKind::Undirected,
                Some("full edge pointing right") => EdgeKind::Right,
                Some("full edge left or undirected") => EdgeKind::LeftOrUndirected,
                Some("full edge undirected or right") => EdgeKind::UndirectedOrRight,
                Some("full edge left or right") => EdgeKind::LeftOrRight,
                Some("full edge any direction") => EdgeKind::Any,
                _ => continue,
            };
            return (kind, Some(c));
        }
    }
    if let Some(abbr) = child(ep, "abbreviated edge pattern") {
        for c in logical(abbr) {
            let kind = match def_name(c) {
                Some("left arrow") => EdgeKind::Left,
                Some("tilde") => EdgeKind::Undirected,
                Some("right arrow") => EdgeKind::Right,
                Some("left arrow tilde") => EdgeKind::LeftOrUndirected,
                Some("tilde right arrow") => EdgeKind::UndirectedOrRight,
                Some("left minus right") => EdgeKind::LeftOrRight,
                Some("minus sign") => EdgeKind::Any,
                _ => continue,
            };
            return (kind, None);
        }
        return (
            match abbr.text().as_str() {
                "<-" => EdgeKind::Left,
                "~" => EdgeKind::Undirected,
                "->" => EdgeKind::Right,
                "<~" => EdgeKind::LeftOrUndirected,
                "~>" => EdgeKind::UndirectedOrRight,
                "<->" => EdgeKind::LeftOrRight,
                _ => EdgeKind::Any,
            },
            None,
        );
    }
    (EdgeKind::Any, None)
}

// ---------------------------------------------------------------------------------------------
// the query around the patterns

/// The oracle record of a sentence from its tree and its generation record (`vars`, as the
/// context command exports it: per variable the kinds and class its labels gave it; absent
/// for sets cached before the export): the statements of the top level block walked in
/// order, every `MATCH` frozen into one graph, every `FILTER` of core predicates made true
/// on it, every `RETURN` of variables renaming the record, then what the last statement
/// lets us claim. The kinds `vars` gives the pattern variables are checked against what the
/// witness bound: a disagreement is reported, so the generator's record and the oracle's
/// reading of the tree keep each other honest.
pub fn oracle(
    sentence: &str,
    tree: &Plain,
    vars: Option<&serde_json::Value>,
    params: Option<&serde_json::Value>,
    mode_default: MatchModeDefault,
) -> Oracle {
    let mut b = Builder::new(mode_default);
    let (parameters, parameter_problems) = parameter_values(tree, params);
    for why in parameter_problems {
        b.out_of_core(why);
    }
    let mut had_match = false;
    let mut shape = Shape::Other("no statement block".to_string());
    let mut blocks = Vec::new();
    find_all(tree, "statement block", &mut blocks);
    if let Some(block) = blocks.first() {
        let mut statements = Vec::new();
        find_all(block, "statement", &mut statements);
        let n = statements.len();
        for (i, s) in statements.iter().enumerate() {
            shape = match statement(s, &mut b, &mut had_match) {
                Err(why) => Shape::Other(why),
                Ok(Shape::Finish) if i + 1 < n => {
                    Shape::Other("FINISH before NEXT".to_string())
                }
                Ok(shape) => shape,
            };
            if matches!(shape, Shape::Other(_)) {
                break;
            }
        }
    }
    let (graph, binding, unsat, mut why) = b.finish();
    for disagreement in check_vars(vars, &binding) {
        why.push(disagreement);
    }
    let mut tier = Tier::Witness;
    if !had_match {
        tier = Tier::Status;
        why.push("no MATCH at the top level: the graph plays no part".to_string());
    }
    if !why.is_empty() {
        tier = Tier::Status;
    }
    let (result, row) = match &shape {
        Shape::Finish => (false, None),
        Shape::Return(cols) => (
            true,
            Some(
                cols.iter()
                    .filter_map(|c| binding.get(c).map(|v| (c.clone(), v.clone())))
                    .collect::<BTreeMap<String, Bound>>(),
            ),
        ),
        Shape::Other(reason) => {
            tier = Tier::Status;
            why.push(reason.clone());
            (true, None)
        }
    };
    let rows = match (&unsat, tier) {
        (Some(reason), _) if had_match => {
            why.insert(0, format!("no graph matches: {reason}"));
            Some(0)
        }
        _ => None,
    };
    let mut expect = Expect {
        tier,
        outcome: "ok",
        status: None,
        bag: None,
        ordered: false,
        evaluator: None,
        binding,
        rows,
        row: if tier == Tier::Witness && rows.is_none() { row } else { None },
        result,
    };
    // Theorem 2: the evaluator over the witness graph gives the whole result where it
    // reaches; the witness tier stands where it stops.
    let mut observed_bag: Option<Vec<eval::Row>> = None;
    match eval::evaluate(tree, &graph, &parameters, mode_default) {
        Ok(eval::Outcome::Table(table)) => {
            expect.tier = Tier::Bag;
            expect.rows = Some(table.rows.len());
            expect.ordered = table.ordered;
            expect.bag = Some(table.rows);
            expect.row = None;
            expect.result = true;
        }
        Ok(eval::Outcome::NoResult) => {
            expect.tier = Tier::Bag;
            expect.result = false;
            expect.row = None;
            if let Ok(eval::Outcome::Table(table)) = eval::evaluate_observing(tree, &graph, &parameters, mode_default) {
                expect.rows = Some(table.rows.len());
                observed_bag = Some(table.rows);
            }
        }
        Ok(eval::Outcome::Exception(status)) => {
            expect.tier = Tier::Bag;
            expect.outcome = "exception";
            expect.status = Some(status);
            expect.result = false;
            expect.row = None;
            expect.rows = None;
        }
        Err(reason) => {
            expect.evaluator = Some(reason);
        }
    }
    let tier = expect.tier;
    let setup = emit(&graph);
    let observe = match (&shape, tier, sentence.strip_suffix(" FINISH")) {
        (Shape::Finish, Tier::Witness | Tier::Bag, Some(head)) if had_match || tier == Tier::Bag => {
            let names: Vec<String> = expect.binding.keys().cloned().collect();
            let (query, row) = if names.is_empty() {
                (
                    format!("{head} RETURN 1 AS n"),
                    BTreeMap::from([("n".to_string(), Bound::Int(1))]),
                )
            } else {
                let items: Vec<String> = names.iter().map(|n| gql_name(n)).collect();
                (
                    format!("{head} RETURN {}", items.join(" , ")),
                    names
                        .iter()
                        .map(|n| (n.clone(), expect.binding[n].clone()))
                        .collect(),
                )
            };
            let bag = observed_bag.map(|rows| {
                if names.is_empty() {
                    rows.into_iter()
                        .map(|_| BTreeMap::from([("n".to_string(), eval::Val::Int(1))]))
                        .collect()
                } else {
                    rows
                }
            });
            Some(Observe {
                query,
                rows: if tier == Tier::Bag { bag.as_ref().map(Vec::len) } else { rows.filter(|r| *r == 0) },
                row: if tier == Tier::Witness && rows.is_none() { Some(row) } else { None },
                bag,
            })
        }
        _ => None,
    };
    Oracle {
        sentence: sentence.to_string(),
        graph,
        setup,
        expect,
        observe,
        parameters,
        why,
    }
}

/// A value per parameter of the tree: of the first class in `exact`, `str`, `bool` that its
/// site admits by the generation record (`params`: name and classes). A parameter the
/// record does not know, or whose site admits none of the three (a list, a record, an
/// element, a temporal value: the harness has no way to pass those yet), leaves the core.
fn parameter_values(
    tree: &Plain,
    params: Option<&serde_json::Value>,
) -> (BTreeMap<String, Value>, Vec<String>) {
    let mut refs = Vec::new();
    find_all(tree, "general parameter reference", &mut refs);
    let mut values = BTreeMap::new();
    let mut problems = Vec::new();
    let known: Vec<(String, Vec<String>)> = params
        .and_then(|p| p.as_array())
        .map(|a| {
            a.iter()
                .filter_map(|p| {
                    Some((
                        p["name"].as_str()?.to_string(),
                        p["classes"]
                            .as_array()?
                            .iter()
                            .filter_map(|c| c.as_str().map(str::to_string))
                            .collect(),
                    ))
                })
                .collect()
        })
        .unwrap_or_default();
    for r in refs {
        let spelling = r.text();
        let Some(name) = child(r, "parameter name") else { continue };
        let key = parameter_key(&name.text());
        if values.contains_key(&key) {
            continue;
        }
        let Some((_, classes)) = known.iter().find(|(n, _)| *n == spelling) else {
            problems.push(format!("a parameter without a recorded class: {spelling}"));
            continue;
        };
        let value = if classes.iter().any(|c| c == "exact") {
            Value::Int(1)
        } else if classes.iter().any(|c| c == "str") {
            Value::Str("a".to_string())
        } else if classes.iter().any(|c| c == "bool") {
            Value::Bool(true)
        } else {
            problems.push(format!(
                "a parameter of a class the harness cannot pass: {spelling} admits {}",
                if classes.is_empty() { "nothing".to_string() } else { classes.join(", ") }
            ));
            continue;
        };
        values.insert(key, value);
    }
    (values, problems)
}

/// The key a parameter is passed under: the name without `$`, a delimited name unquoted,
/// a separated one (`@x`) without its `@`.
pub(crate) fn parameter_key(name: &str) -> String {
    let t = name.strip_prefix('@').unwrap_or(name);
    identifier(&Plain::Term(t.to_string()))
}

enum Shape {
    Finish,
    /// The columns a RETURN of variables produced, in order.
    Return(Vec<String>),
    Other(String),
}

/// One `<statement>` of the block applied to the builder: its simple query statements
/// (`MATCH`, or `FILTER` of core predicates) in order, then its result statement.
fn statement(s: &Plain, b: &mut Builder, had_match: &mut bool) -> Result<Shape, String> {
    let text = s.text();
    for kw in ["UNION", "EXCEPT", "INTERSECT", "OTHERWISE"] {
        if text.contains(kw) {
            return Err("a composite query".to_string());
        }
    }
    let mut simples = Vec::new();
    find_all(s, "simple query statement", &mut simples);
    for q in &simples {
        let Some(primitive) = child(q, "primitive query statement") else {
            return Err(format!("a statement that is not MATCH: {}", q.text()));
        };
        if let Some(m) = child(primitive, "match statement") {
            let mut matches = Vec::new();
            top_level_matches(m, &mut matches, b);
            if matches.is_empty() {
                return Err("an OPTIONAL MATCH".to_string());
            }
            for m in matches {
                *had_match = true;
                let Some(table) = child(m, "graph pattern binding table") else { continue };
                if let Some(gp) = child(table, "graph pattern") {
                    b.graph_pattern(gp, None);
                }
                if child(table, "graph pattern yield clause").is_some() {
                    b.out_of_core("a graph pattern YIELD");
                }
            }
        } else if let Some(f) = child(primitive, "filter statement") {
            // 14.6: rows where the condition is true; the witness row is made one.
            match child(f, "search condition") {
                Some(cond) => b.where_clause(cond),
                None => return Err("a FILTER without a condition".to_string()),
            }
        } else {
            return Err(format!("a statement that is not MATCH: {}", primitive.text()));
        }
    }
    let mut primitives = Vec::new();
    find_all(s, "primitive result statement", &mut primitives);
    let Some(result) = primitives.first() else {
        return Err("no result statement".to_string());
    };
    if has_kw(result, "FINISH") || result.text() == "FINISH" {
        return Ok(Shape::Finish);
    }
    let Some(ret) = child(result, "return statement") else {
        return Err(format!("a result statement that is not RETURN: {}", result.text()));
    };
    // 14.9: ORDER BY keeps the row, OFFSET or SKIP may drop it, LIMIT 0 drops it; the
    // witness claims a row, so only what keeps it stays in the core.
    if let Some(page) = child(result, "order by and page statement") {
        if child(page, "offset clause").is_some() {
            return Err("an OFFSET or SKIP: the witness row may be dropped".to_string());
        }
        if let Some(limit) = child(page, "limit clause") {
            let mut ints = Vec::new();
            find_all(limit, "unsigned integer", &mut ints);
            let mut params = Vec::new();
            find_all(limit, "general parameter reference", &mut params);
            match ints.first().and_then(|i| unsigned(&i.text())) {
                Some(0) => return Err("LIMIT 0 drops every row".to_string()),
                Some(_) => {}
                // A parameter is given the value 1 (`parameter_values`), which keeps the row.
                None if !params.is_empty() => {}
                None => return Err("a LIMIT that is not a literal".to_string()),
            }
        }
    }
    let Some(body) = child(ret, "return statement body") else {
        return Err("RETURN without a body".to_string());
    };
    if has_kw(body, "NO") {
        return Err("RETURN NO BINDINGS".to_string());
    }
    let Some(list) = child(body, "return item list") else {
        return Err("RETURN *".to_string());
    };
    let mut items = Vec::new();
    find_all(list, "return item", &mut items);
    let mut cols: Vec<(String, String)> = Vec::new();
    for item in items {
        let kids = logical(item);
        let Some(expr) = kids.first() else { continue };
        let Some(var) = exactly(expr, "binding variable reference") else {
            return Err(format!("a return item that is not a variable: {}", item.text()));
        };
        let name = identifier(var);
        if !b.vars.contains_key(&name) {
            return Err(format!("a returned variable the patterns do not bind: {name}"));
        }
        let col = child(item, "return item alias")
            .and_then(|a| child(a, "identifier"))
            .map(identifier)
            .unwrap_or_else(|| name.clone());
        cols.push((col, name));
    }
    // The outgoing table has exactly these columns (14.11): the record is renamed to them.
    let renamed: BTreeMap<String, Slot> = cols
        .iter()
        .filter_map(|(col, name)| b.vars.get(name).cloned().map(|s| (col.clone(), s)))
        .collect();
    b.vars = renamed;
    Ok(Shape::Return(cols.into_iter().map(|(c, _)| c).collect()))
}

/// Where the generation record and the witness disagree on a pattern variable's kind: the
/// record says `decl` or `out` is a node, an edge or a path, and the witness bound it as
/// something else. An absent record checks nothing.
fn check_vars(vars: Option<&serde_json::Value>, binding: &BTreeMap<String, Bound>) -> Vec<String> {
    let mut out = Vec::new();
    let Some(vars) = vars.and_then(|v| v.as_array()) else {
        return out;
    };
    for var in vars {
        let Some(name) = var["name"].as_str() else { continue };
        let Some(bound) = binding.get(name) else { continue };
        let kinds: BTreeSet<&str> = ["decl", "out"]
            .iter()
            .filter_map(|k| var[k].as_array())
            .flatten()
            .filter_map(|v| v.as_str())
            .collect();
        let witness = match bound {
            Bound::Node(_) => "node",
            Bound::Edge(_) => "edge",
            Bound::Path(_) => "path",
            Bound::List(_) | Bound::Null | Bound::Int(_) => continue,
        };
        let known: Vec<&str> = kinds
            .iter()
            .copied()
            .filter(|k| matches!(*k, "node" | "edge" | "path"))
            .collect();
        if !known.is_empty() && !known.contains(&witness) {
            out.push(format!(
                "the generation record says {name} is {}, the witness bound a {witness}",
                known.join(" or ")
            ));
        }
    }
    out
}

/// The simple match statements of the top level linear query, in order. A match under an
/// `EXISTS`, a nested query, a `CALL`, an `OPTIONAL` or a `FOR` is noted and skipped.
fn top_level_matches<'a>(p: &'a Plain, out: &mut Vec<&'a Plain>, b: &mut Builder) {
    match def_name(p) {
        Some("simple match statement") => {
            out.push(p);
            return;
        }
        Some("optional match statement") => {
            b.out_of_core("an OPTIONAL MATCH");
            return;
        }
        Some("exists predicate") | Some("nested query specification")
        | Some("nested procedure specification") | Some("for statement")
        | Some("call query statement") => {
            return;
        }
        _ => {}
    }
    if let Plain::Def { children, .. } = p {
        for c in children {
            top_level_matches(c, out, b);
        }
    }
}

// ---------------------------------------------------------------------------------------------
// the setup statements per engine

fn gql_value(v: &Value) -> String {
    match v {
        Value::Null => "NULL".to_string(),
        Value::Bool(true) => "TRUE".to_string(),
        Value::Bool(false) => "FALSE".to_string(),
        Value::Int(i) => i.to_string(),
        Value::Float(f) => {
            let s = f.to_string();
            if s.contains('.') { s } else { format!("{s}.0") }
        }
        Value::Str(s) => format!("'{}'", s.replace('\'', "''")),
    }
}

pub(crate) fn gql_name(n: &str) -> String {
    if !n.is_empty()
        && n.chars().next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && n.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
    {
        n.to_string()
    } else {
        format!("`{}`", n.replace('`', "``"))
    }
}

fn properties_gql(props: &BTreeMap<String, Value>) -> String {
    let items: Vec<String> = props
        .iter()
        .map(|(k, v)| format!("{} : {}", gql_name(k), gql_value(v)))
        .collect();
    format!("{{ {} }}", items.join(" , "))
}

/// One `INSERT` for the whole graph: nodes first, then edges by node variable (16.5 SR 10
/// b lets a variable be declared again without a filler).
pub fn emit_gql(g: &Graph) -> Vec<String> {
    let mut parts = Vec::new();
    for n in &g.nodes {
        let labels: Vec<String> = n.labels.iter().map(|l| gql_name(l)).collect();
        let label = if labels.is_empty() { String::new() } else { format!(" :{}", labels.join("&")) };
        parts.push(format!("( n{}{label} {} )", n.id, properties_gql(&n.properties)));
    }
    for e in &g.edges {
        let labels: Vec<String> = e.labels.iter().map(|l| gql_name(l)).collect();
        let label = if labels.is_empty() { String::new() } else { format!(":{} ", labels.join("&")) };
        let filler = format!("{label}{}", properties_gql(&e.properties));
        let edge = if e.directed {
            format!("-[ {filler} ]->")
        } else {
            format!("~[ {filler} ]~")
        };
        parts.push(format!("( n{} ) {edge} ( n{} )", e.source, e.target));
    }
    if parts.is_empty() {
        return Vec::new();
    }
    vec![format!("INSERT {}", parts.join(" , "))]
}

fn cypher_value(v: &Value) -> String {
    match v {
        Value::Null => "null".to_string(),
        Value::Bool(b) => b.to_string(),
        Value::Int(i) => i.to_string(),
        Value::Float(f) => {
            let s = f.to_string();
            if s.contains('.') { s } else { format!("{s}.0") }
        }
        Value::Str(s) => format!("'{}'", s.replace('\\', "\\\\").replace('\'', "\\'")),
    }
}

fn properties_cypher(props: &BTreeMap<String, Value>) -> String {
    let items: Vec<String> = props
        .iter()
        .map(|(k, v)| format!("{}: {}", gql_name(k), cypher_value(v)))
        .collect();
    format!("{{{}}}", items.join(", "))
}

/// One `CREATE` for the whole graph, or why neo4j cannot hold it: one type per
/// relationship, every relationship directed.
pub fn emit_cypher(g: &Graph) -> Result<Vec<String>, String> {
    let mut parts = Vec::new();
    for n in &g.nodes {
        let labels: String = n.labels.iter().map(|l| format!(":{}", gql_name(l))).collect();
        parts.push(format!("(n{}{labels} {})", n.id, properties_cypher(&n.properties)));
    }
    for e in &g.edges {
        if e.labels.len() != 1 {
            return Err(format!("edge {} has {} labels; neo4j has one type per relationship", e.id, e.labels.len()));
        }
        if !e.directed {
            return Err(format!("edge {} is undirected; neo4j relationships are directed", e.id));
        }
        let label = gql_name(e.labels.iter().next().expect("one label"));
        parts.push(format!("(n{})-[:{label} {}]->(n{})", e.source, properties_cypher(&e.properties), e.target));
    }
    if parts.is_empty() {
        return Ok(Vec::new());
    }
    Ok(vec![format!("CREATE {}", parts.join(", "))])
}

/// Turbolay's in-memory records (`MemoryStorage::with_graph`): vertices and relationships
/// as json the probe turns into `VertexRecord` and `RelationshipRecord`.
pub fn emit_turbolay(g: &Graph) -> Result<serde_json::Value, String> {
    let mut vertices = Vec::new();
    for n in &g.nodes {
        vertices.push(serde_json::json!({
            "id": n.id,
            "labels": n.labels,
            "properties": n.properties,
        }));
    }
    let mut relationships = Vec::new();
    for e in &g.edges {
        if e.labels.len() != 1 {
            return Err(format!("edge {} has {} labels; turbolay has one type per relationship", e.id, e.labels.len()));
        }
        if !e.directed {
            return Err(format!("edge {} is undirected; turbolay relationships are directed", e.id));
        }
        relationships.push(serde_json::json!({
            "id": e.id,
            "source": e.source,
            "target": e.target,
            "relationship_type": e.labels.iter().next(),
            "properties": e.properties,
        }));
    }
    Ok(serde_json::json!({ "vertices": vertices, "relationships": relationships }))
}

pub fn emit(g: &Graph) -> Setup {
    let mut setup = Setup {
        gql: Some(emit_gql(g)),
        ..Setup::default()
    };
    match emit_cypher(g) {
        Ok(s) => setup.cypher = Some(s),
        Err(why) => {
            setup.unloadable.insert("cypher", why);
        }
    }
    match emit_turbolay(g) {
        Ok(s) => setup.turbolay = Some(s),
        Err(why) => {
            setup.unloadable.insert("turbolay", why);
        }
    }
    setup
}

#[cfg(test)]
mod tests {
    use super::*;

    fn name(n: &str) -> LabelExpr {
        LabelExpr::Name(n.to_string())
    }

    #[test]
    fn label_models() {
        let m = label_model(&[name("a")], "L0").unwrap();
        assert_eq!(m, ["a".to_string()].into_iter().collect());
        let m = label_model(&[LabelExpr::Not(Box::new(name("a")))], "L0").unwrap();
        assert_eq!(m, ["L0".to_string()].into_iter().collect());
        assert!(label_model(&[LabelExpr::Not(Box::new(LabelExpr::Wildcard))], "L0").is_none());
        assert!(label_model(&[name("a"), LabelExpr::Not(Box::new(name("a")))], "L0").is_none());
        let m = label_model(
            &[LabelExpr::Or(Box::new(name("a")), Box::new(name("b"))), LabelExpr::Not(Box::new(name("a")))],
            "L0",
        )
        .unwrap();
        assert_eq!(m, ["b".to_string()].into_iter().collect());
        assert_eq!(label_model(&[], "L0").unwrap().len(), 1);
    }

    #[test]
    fn delimited_identifiers() {
        let leaf = |s: &str| Plain::Term(s.to_string());
        assert_eq!(identifier(&leaf("````")), "`");
        assert_eq!(identifier(&leaf("\"\"\"\"")), "\"");
        assert_eq!(identifier(&leaf("`a``b`")), "a`b");
        assert_eq!(identifier(&leaf("ab")), "ab");
    }

    #[test]
    fn radix_integers() {
        assert_eq!(unsigned("0o22"), Some(18));
        assert_eq!(unsigned("0b1"), Some(1));
        assert_eq!(unsigned("0x1F"), Some(31));
        assert_eq!(unsigned("1_000"), Some(1000));
    }
}
