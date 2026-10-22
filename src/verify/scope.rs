//! Variable scoping of ISO/IEC 39075 (2024 + Cor 1), checked on a `Plain` tree straight from
//! the Syntax Rules.
//!
//! A scope is the declared type of the incoming working record and of the incoming working
//! table, cut down to field names, each with a kind (what bound it) and a degree of reference
//! (20.12 SR 11). Statements thread the scope left to right (9.2 SR 10-12, 13.1 SR 6-8, 14.3
//! SR 3-5); an expression sees the record amended with the table (16.13 SR 2, 16.17 SR 5, 14.8
//! SR 7, 15.1 SR 5); a subquery sees that record and a unit table (15.1 SR 7, 20.6 SR 11-12).
//!
//! Unmodelled, so not checked inside and binding nothing:
//! - catalog-modifying statements and session commands
//! - a <select statement> with a <select statement body>
//! - the result of a <named procedure call> without YIELD, which only a catalog knows
//! - value types: a name bound to an arbitrary expression has an unknown type, so kinds are
//!   only compared between names bound as nodes, edges, paths, graphs and tables
//!
//! Readings where the text leaves room:
//! - a group variable is a group list (4.15.3), so returning or passing it on is fine; outside
//!   an aggregate function it is no property source (20.1 SR 4-6) and no operand of the
//!   element predicates (19.8-19.13 SR 2, 20.10 SR 2)
//! - an aggregate function outside an <aggregating value expression> is horizontal (20.1 SR 7)
//! - 16.7 SR 11 holds for multiset alternation too, which SR 10 f makes a union
//! - a name declared both as a subpath variable and as another graph pattern variable breaks
//!   16.3 SR 4; a path variable declared twice breaks 4.11.4

use super::{Plain, Violation};
use std::collections::{BTreeMap, BTreeSet, HashMap};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Node,
    Edge,
    Path,
    /// A LET, FOR or VALUE variable or a column computed by an expression: any value type.
    Value,
    Graph,
    Table,
}

/// Degree of reference (20.12 SR 11); a group is effectively bounded (SR 12).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Degree {
    Single,
    Conditional,
    Group,
}

#[derive(Debug, Clone)]
struct Var {
    kind: Kind,
    degree: Degree,
    /// The rule a reference from here breaks: graph pattern variables in a WHERE clause.
    bad: Option<(&'static str, String)>,
}

impl Var {
    fn new(kind: Kind, degree: Degree) -> Var {
        Var {
            kind,
            degree,
            bad: None,
        }
    }

    fn value() -> Var {
        Var::new(Kind::Value, Degree::Single)
    }
}

type Fields = BTreeMap<String, Var>;

#[derive(Debug, Clone, Default)]
struct Scope {
    record: Fields,
    table: Fields,
}

impl Scope {
    /// The record amended with the table, what an expression or a procedure call sees.
    fn merged(&self) -> Fields {
        let mut all = self.record.clone();
        all.extend(self.table.clone());
        all
    }
}

/// What an expression sees.
#[derive(Clone)]
struct Env {
    vars: Fields,
    /// What the argument of an aggregate function sees, when that differs (14.11 SR 10 a ix).
    agg: Option<Fields>,
    /// The rule a name that is not in `vars` breaks.
    unbound: &'static str,
}

impl Env {
    fn new(vars: Fields) -> Env {
        Env {
            vars,
            agg: None,
            unbound: "20.12 SR 8",
        }
    }
}

/// Where in an expression the walk is.
#[derive(Debug, Clone, Copy, Default)]
struct At {
    /// Inside the argument of an aggregate function.
    agg: bool,
    /// Inside the <value expression> of an <aggregating value expression>, below no other.
    vertical: bool,
}

/// Every scoping violation in a tree rooted at <GQL-program> (or any statement-level node).
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

    fn inside(&self, node: &Plain, ancestor: &Plain) -> bool {
        let mut at = Some(node);
        while let Some(n) = at {
            if std::ptr::eq(n, ancestor) {
                return true;
            }
            at = self.parent.get(&(n as *const Plain)).copied();
        }
        false
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

    fn root(&mut self, node: &'t Plain) {
        match name(node) {
            Some("procedure body") => {
                self.body(node, Scope::default());
            }
            Some("statement") => {
                self.statement(node, Scope::default());
            }
            Some("composite query expression") => {
                self.composite(node, Scope::default());
            }
            Some("linear query statement" | "linear data-modifying statement") => {
                self.linear(node, Scope::default());
            }
            Some(n) if n.starts_with("session") => {}
            _ => kids(node).into_iter().for_each(|k| self.root(k)),
        }
    }

    // --- statements ---------------------------------------------------------------------

    /// 9.2: the columns of the declared type of a procedure body, if a binding table type.
    fn body(&mut self, pb: &'t Plain, scope: Scope) -> Option<Fields> {
        let mut record = scope.record;
        if let Some(block) = own(pb, "binding variable definition block") {
            for def in owns(block, "binding variable definition") {
                let Some(def) = kids(def).into_iter().next() else {
                    continue;
                };
                let (kind, rule) = match name(def) {
                    Some("graph variable definition") => (Kind::Graph, "10.1 SR 7"),
                    Some("binding table variable definition") => (Kind::Table, "10.2 SR 7"),
                    _ => (Kind::Value, "10.3 SR 7"),
                };
                let Some((bv, value)) = definition(def) else {
                    continue;
                };
                // SR 2: each definition sees the record so far and a unit table.
                self.expr(def, &Env::new(record.clone()), At::default());
                let n = bv.text();
                if record.contains_key(&n) {
                    self.report(def, rule, format!("{n} is already a field of the record"));
                }
                let var = match value {
                    Some(v) if kind == Kind::Value => bound(v, &record),
                    _ => Var::new(kind, Degree::Single),
                };
                record.insert(n, var);
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
            // SR 12 b: the table is the previous statement's result, or a unit table. No
            // statement changes the names of the record, so it is the block's.
            let mut table = result.unwrap_or_default();
            if let Some(yc) = own(next, "yield clause") {
                table = self.yield_clause(yc, Some(&table));
            }
            for n in table.keys() {
                if scope.record.contains_key(n) {
                    self.report(
                        next,
                        "9.2 SR 12",
                        format!("{n} is a field of the record and a column of the table"),
                    );
                }
            }
            result = match own(next, "statement") {
                Some(st) => self.statement(
                    st,
                    Scope {
                        record: scope.record.clone(),
                        table,
                    },
                ),
                None => None,
            };
        }
        result
    }

    /// 16.14: the columns a <yield clause> makes of `table`, or of a procedure result.
    fn yield_clause(&mut self, yc: &'t Plain, table: Option<&Fields>) -> Fields {
        let mut out = Fields::new();
        let mut items = Vec::new();
        find(yc, "yield item", &mut items);
        for item in items {
            let Some(field) = own(item, "yield item name") else {
                continue;
            };
            let from = ident(field);
            let to = match own(item, "yield item alias").and_then(|a| own(a, "binding variable")) {
                Some(bv) => bv.text(),
                None => {
                    if contains(field, "delimited identifier") {
                        self.report(
                            item,
                            "16.14 SR 4",
                            format!("{from} has no alias and is not a binding variable"),
                        );
                    }
                    from.clone()
                }
            };
            let var = match table {
                Some(table) => match table.get(&from) {
                    Some(var) => var.clone(),
                    None => {
                        self.report(
                            item,
                            "16.14 SR 7",
                            format!("{from} is not a column of the working table"),
                        );
                        Var::value()
                    }
                },
                None => Var::value(),
            };
            if out.insert(to.clone(), var).is_some() {
                self.report(item, "16.14 SR 6", format!("{to} is yielded twice"));
            }
        }
        out
    }

    fn statement(&mut self, st: &'t Plain, scope: Scope) -> Option<Fields> {
        let inner = kids(st).into_iter().next()?;
        match name(inner)? {
            "composite query statement" => {
                self.composite(own(inner, "composite query expression")?, scope)
            }
            "linear data-modifying statement" => self.linear(inner, scope),
            _ => None,
        }
    }

    /// 14.2: every operand gets the same scope (SR 8-10) and returns the same column names.
    fn composite(&mut self, cqe: &'t Plain, scope: Scope) -> Option<Fields> {
        let mut operands = Vec::new();
        conjuncts(cqe, &mut operands);
        if operands.len() > 1 && operands.iter().any(|op| finishes(op)) {
            self.report(cqe, "14.2 SR 5", "FINISH in a composite query".into());
        }
        let mut first: Option<Option<Fields>> = None;
        for &op in &operands {
            let result = self.linear(op, scope.clone());
            match (&first, &result) {
                (None, _) => first = Some(result),
                (Some(Some(a)), Some(b)) if a.keys().ne(b.keys()) => {
                    let a: Vec<_> = a.keys().collect();
                    let b: Vec<_> = b.keys().collect();
                    self.report(
                        op,
                        "14.2 SR 10",
                        format!("columns {a:?} and {b:?} are not name-equal"),
                    );
                }
                _ => {}
            }
        }
        first.flatten()
    }

    /// 14.3 SR 2-5 and 13.1 SR 4-8: the statements of a linear statement, left to right.
    fn linear(&mut self, node: &'t Plain, mut scope: Scope) -> Option<Fields> {
        let mut parts = Vec::new();
        steps(node, &mut parts);
        let mut result = None;
        for step in parts {
            result = None;
            match name(step) {
                // 16.2 SR 3-4: the graph expression sees the record and a unit table.
                Some("use graph clause") => {
                    self.expr(step, &Env::new(scope.record.clone()), At::default())
                }
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
            // 14.6 SR 6-9, 14.9 SR 4-5: the scope passes through.
            Some("filter statement" | "order by and page statement") => {
                self.expr(node, &Env::new(scope.merged()), At::default());
                scope
            }
            Some("call procedure statement") => self.call(node, scope),
            Some("insert statement") => self.insert(node, scope),
            Some("set statement" | "remove statement" | "delete statement") => {
                self.modify(node, &scope);
                scope
            }
            _ => scope,
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
                // SR 4: OPTIONAL CALL (every incoming name) { the operand RETURN its new names }.
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
                for (n, var) in body.table {
                    scope.table.insert(n, optional(var));
                }
                scope
            }
            _ => scope,
        }
    }

    fn simple_match(&mut self, sms: &'t Plain, scope: Scope) -> Scope {
        let Some(gpbt) = own(sms, "graph pattern binding table") else {
            return scope;
        };
        match own(gpbt, "graph pattern") {
            Some(gp) => self.pattern_match(gp, own(gpbt, "graph pattern yield clause"), scope),
            None => scope,
        }
    }

    /// 16.3, with 14.4 SR 5: the pattern's yielded names that are new become columns.
    fn pattern_match(&mut self, gp: &'t Plain, yc: Option<&'t Plain>, mut scope: Scope) -> Scope {
        let incoming = scope.merged();
        let (globals, subpaths) = self.graph_pattern(gp, &incoming);
        for n in &subpaths {
            if scope.record.contains_key(n) {
                self.report(
                    gp,
                    "16.3 SR 7",
                    format!("subpath variable {n} is a field of the record"),
                );
            }
            if scope.table.contains_key(n) {
                self.report(
                    gp,
                    "16.3 SR 9",
                    format!("subpath variable {n} is a column of the table"),
                );
            }
        }
        let yielded: Vec<String> = match yc {
            Some(yc) => {
                let mut refs = Vec::new();
                find(yc, "binding variable reference", &mut refs);
                // SR 12 a iii-iv: the overlap with the incoming names is always yielded.
                let mut names: Vec<String> = globals
                    .keys()
                    .filter(|n| incoming.contains_key(*n))
                    .cloned()
                    .collect();
                let mut explicit = BTreeSet::new();
                for r in refs {
                    let n = r.text();
                    if !explicit.insert(n.clone()) {
                        self.report(r, "16.3 SR 12", format!("{n} is yielded twice"));
                    } else if !globals.contains_key(&n) {
                        self.report(
                            r,
                            "16.3 SR 12",
                            format!("{n} is not a variable of the graph pattern"),
                        );
                    } else if !names.contains(&n) {
                        names.push(n);
                    }
                }
                names
            }
            None => globals.keys().cloned().collect(),
        };
        for n in yielded {
            let var = globals[&n].clone();
            match incoming.get(&n) {
                Some(old) => {
                    if (old.degree == Degree::Group) != (var.degree == Degree::Group) {
                        self.report(
                            gp,
                            "16.3 SR 16",
                            format!("{n} joins a group with a singleton"),
                        );
                    }
                    if !joinable(old.kind, var.kind) {
                        self.report(
                            gp,
                            "16.3 SR 20",
                            format!("{n} joins a {:?} with a {:?}", old.kind, var.kind),
                        );
                    }
                }
                None => {
                    scope.table.insert(n, var);
                }
            }
        }
        scope
    }

    /// 14.7 as Cor 1 rewrites it: each definition is CALL (the LET's incoming names) {
    /// VALUE x = e RETURN x }, so it sees none of the others.
    fn let_statement(&mut self, ls: &'t Plain, mut scope: Scope) -> Scope {
        let incoming = scope.merged();
        let defs = own(ls, "let variable definition list")
            .map(|l| owns(l, "let variable definition"))
            .unwrap_or_default();
        for def in defs {
            let Some((bv, value)) = definition(def) else {
                continue;
            };
            self.expr(def, &Env::new(incoming.clone()), At::default());
            let n = bv.text();
            if incoming.contains_key(&n) {
                self.report(
                    def,
                    "10.3 SR 7",
                    format!("{n} is already a field of the record"),
                );
            } else if scope.table.contains_key(&n) {
                self.report(def, "15.1 SR 9", format!("{n} is defined twice"));
            }
            let var = value.map_or_else(Var::value, |v| bound(v, &incoming));
            scope.table.insert(n, var);
        }
        scope
    }

    /// 14.8.
    fn for_statement(&mut self, fs: &'t Plain, mut scope: Scope) -> Scope {
        let incoming = scope.merged();
        let Some(item) = own(fs, "for item") else {
            return scope;
        };
        let source = own(item, "for item source");
        if let Some(source) = source {
            self.expr(source, &Env::new(incoming.clone()), At::default());
        }
        let mut new = Vec::new();
        if let Some(bv) = own(item, "for item alias").and_then(|a| own(a, "binding variable")) {
            // an element of a group list of nodes or edges is a node or an edge
            let element = source
                .and_then(bare)
                .and_then(|n| incoming.get(&n))
                .filter(|v| v.degree == Degree::Group)
                .map_or_else(Var::value, |v| Var::new(v.kind, Degree::Single));
            new.push((bv.text(), element));
        }
        if let Some(bv) =
            own(fs, "for ordinality or offset").and_then(|f| own(f, "binding variable"))
        {
            let n = bv.text();
            if new.iter().any(|(a, _)| *a == n) {
                self.report(
                    fs,
                    "14.8 SR 10",
                    format!("{n} names both the item and its position"),
                );
            } else {
                new.push((n, Var::value()));
            }
        }
        for (n, var) in new {
            // reading: SR 11 keeps the new names out of the record and the table both
            if incoming.contains_key(&n) {
                self.report(fs, "14.8 SR 11", format!("{n} is already bound"));
            }
            scope.table.insert(n, var);
        }
        scope
    }

    /// 15.1-15.3.
    fn call(&mut self, cps: &'t Plain, mut scope: Scope) -> Scope {
        let is_optional = kids(cps).iter().any(|k| keyword(k, "OPTIONAL"));
        let Some(pc) = own(cps, "procedure call").and_then(|p| kids(p).into_iter().next()) else {
            return scope;
        };
        // 15.1 SR 5-7: the procedure sees the record amended with the table.
        let incoming = scope.merged();
        let result = match name(pc) {
            Some("inline procedure call") => {
                let record = match own(pc, "variable scope clause") {
                    // 15.2 SR 5-7
                    Some(vsc) => {
                        let mut record = Fields::new();
                        let mut listed = BTreeSet::new();
                        let mut refs = Vec::new();
                        find(vsc, "binding variable reference", &mut refs);
                        for r in refs {
                            self.reference(r, &Env::new(incoming.clone()), At::default());
                            let n = r.text();
                            if !listed.insert(n.clone()) {
                                self.report(r, "15.2 SR 6", format!("{n} is listed twice"));
                            }
                            if let Some(var) = incoming.get(&n) {
                                record.insert(n, var.clone());
                            }
                        }
                        record
                    }
                    // 15.2 SR 3
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
                    self.expr(args, &Env::new(incoming.clone()), At::default());
                }
                own(pc, "yield clause").map(|yc| self.yield_clause(yc, None))
            }
            _ => None,
        };
        for (n, var) in result.unwrap_or_default() {
            // 15.1 SR 9 as Cor 1 corrects it
            if incoming.contains_key(&n) {
                self.report(
                    cps,
                    "15.1 SR 9",
                    format!("the call returns {n}, which is already bound"),
                );
                continue;
            }
            scope
                .table
                .insert(n, if is_optional { optional(var) } else { var });
        }
        scope
    }

    /// 13.2 SR 4, 7 and 16.5: an insert pattern adds its unbound element variables as columns.
    fn insert(&mut self, is: &'t Plain, mut scope: Scope) -> Scope {
        let incoming = scope.merged();
        let Some(igp) = own(is, "insert graph pattern") else {
            return scope;
        };
        // 16.5 SR 6
        let mut specs = Vec::new();
        find(igp, "element property specification", &mut specs);
        for s in specs {
            self.expr(s, &Env::new(incoming.clone()), At::default());
        }
        let mut patterns = Vec::new();
        find_any(
            igp,
            &["insert node pattern", "insert edge pattern"],
            &mut patterns,
        );
        let mut declared: Vec<(String, Kind)> = Vec::new();
        for ep in patterns {
            let Some(filler) = first(ep, "insert element pattern filler") else {
                continue;
            };
            let Some(n) = own(filler, "element variable declaration")
                .and_then(|d| first(d, "binding variable"))
                .map(Plain::text)
            else {
                continue;
            };
            let kind = match name(ep) {
                Some("insert edge pattern") => Kind::Edge,
                _ => Kind::Node,
            };
            let labelled = own(filler, "label and property set specification").is_some();
            if let Some(var) = incoming.get(&n) {
                // SR 8, 10 a: a bound insert element pattern
                if kind == Kind::Edge
                    || !matches!(var.kind, Kind::Node | Kind::Value)
                    || var.degree == Degree::Group
                {
                    self.report(ep, "16.5 SR 10", format!("{n} is bound and not a node"));
                } else if labelled {
                    self.report(
                        ep,
                        "16.5 SR 10",
                        format!("bound {n} has labels or properties"),
                    );
                }
            } else if let Some(&(_, was)) = declared.iter().find(|(d, _)| *d == n) {
                if kind == Kind::Edge || was == Kind::Edge {
                    self.report(
                        ep,
                        "16.5 SR 11",
                        format!("{n} is declared again next to an edge"),
                    );
                } else if labelled {
                    self.report(
                        ep,
                        "16.5 SR 10",
                        format!("{n} has labels or properties outside its defining pattern"),
                    );
                }
            } else {
                declared.push((n, kind));
            }
        }
        for (n, kind) in declared {
            scope.table.insert(n, Var::new(kind, Degree::Single));
        }
        scope
    }

    /// 13.3-13.5: the items reference bound graph elements.
    fn modify(&mut self, st: &'t Plain, scope: &Scope) {
        let incoming = scope.merged();
        self.expr(st, &Env::new(incoming.clone()), At::default());
        let (rule, targets): (&'static str, Vec<&Plain>) = match name(st) {
            Some("set statement") => (
                "13.3 SR 3",
                items(
                    st,
                    &[
                        "set property item",
                        "set all properties item",
                        "set label item",
                    ],
                ),
            ),
            Some("remove statement") => (
                "13.4 SR 3",
                items(st, &["remove property item", "remove label item"]),
            ),
            _ => ("13.5 SR 5", items(st, &["delete item"])),
        };
        for target in &targets {
            let source = own(target, "binding variable reference")
                .or_else(|| own(target, "value expression"));
            let Some(n) = source.and_then(bare) else {
                continue;
            };
            if let Some(var) = incoming.get(&n)
                && (!matches!(var.kind, Kind::Node | Kind::Edge | Kind::Value)
                    || var.degree == Degree::Group)
            {
                self.report(target, rule, format!("{n} is not a graph element"));
            }
        }
        if name(st) == Some("set statement") {
            // SR 4-5
            let mut properties = BTreeSet::new();
            let mut all = BTreeSet::new();
            let target = |item: &Plain| own(item, "binding variable reference").map(Plain::text);
            for item in &targets {
                let Some(n) = target(item) else { continue };
                match name(item) {
                    Some("set property item") => {
                        let key = own(item, "property name")
                            .map(Plain::text)
                            .unwrap_or_default();
                        if !properties.insert((n.clone(), key.clone())) {
                            self.report(item, "13.3 SR 4", format!("{n}.{key} is set twice"));
                        }
                    }
                    Some("set all properties item") => {
                        if !all.insert(n.clone()) {
                            self.report(
                                item,
                                "13.3 SR 5",
                                format!("all properties of {n} are set twice"),
                            );
                        }
                    }
                    _ => {}
                }
            }
            for (n, key) in &properties {
                if all.contains(n) {
                    self.report(
                        st,
                        "13.3 SR 5",
                        format!("{n}.{key} is set next to all properties of {n}"),
                    );
                }
            }
        }
    }

    /// 14.12 SR 27 a: without a body a SELECT is a RETURN of its items; with one it is
    /// unmodelled.
    fn select(&mut self, sel: &'t Plain, scope: &Scope) -> Option<Fields> {
        if own(sel, "select statement body").is_some() {
            return None;
        }
        if own(sel, "asterisk").is_some() {
            self.report(sel, "14.12 SR 7", "SELECT * without FROM".into());
            return Some(Fields::new());
        }
        let incoming = scope.merged();
        let mut cols = Fields::new();
        for item in own(sel, "select item list")
            .map(|l| owns(l, "select item"))
            .unwrap_or_default()
        {
            let Some(ave) = own(item, "aggregating value expression") else {
                continue;
            };
            self.expr(ave, &Env::new(incoming.clone()), At::default());
            let alias = own(item, "select item alias")
                .and_then(|a| own(a, "identifier"))
                .map(ident);
            let Some(n) = alias.or_else(|| bare(ave)) else {
                self.report(
                    item,
                    "14.12 SR 8",
                    "a select item that is not a binding variable reference needs an alias".into(),
                );
                continue;
            };
            if cols.insert(n.clone(), bound(ave, &incoming)).is_some() {
                self.report(item, "14.11 SR 11", format!("column {n} is returned twice"));
            }
        }
        Some(cols)
    }

    /// 14.10 and 14.11: the columns a primitive result statement declares; FINISH declares
    /// none.
    fn result(&mut self, prs: &'t Plain, scope: &Scope) -> Option<Fields> {
        let rs = own(prs, "return statement")?;
        let body = own(rs, "return statement body")?;
        let incoming = scope.merged();
        let distinct =
            own(body, "set quantifier").is_some_and(|q| q.text().eq_ignore_ascii_case("DISTINCT"));
        let gbc = own(body, "group by clause");
        let mut cols = Fields::new();
        let mut aggregating = false;
        let mut grouping: Vec<(&Plain, String)> = Vec::new();
        if own(body, "asterisk").is_some() {
            // SR 6
            if scope.table.is_empty() {
                self.report(
                    rs,
                    "14.11 SR 6",
                    "RETURN * against a unit working table".into(),
                );
            }
            if gbc.is_some() {
                self.report(rs, "14.11 SR 6", "RETURN * with GROUP BY".into());
            }
            cols = scope.table.clone();
        } else {
            let items = own(body, "return item list")
                .map(|l| owns(l, "return item"))
                .unwrap_or_default();
            let mut named = Vec::new();
            for item in items {
                let Some(ave) = own(item, "aggregating value expression") else {
                    continue;
                };
                let alias = own(item, "return item alias")
                    .and_then(|a| own(a, "identifier"))
                    .map(ident);
                let n = alias.or_else(|| bare(ave));
                if n.is_none() {
                    // SR 8 b
                    self.report(
                        item,
                        "14.11 SR 8",
                        format!(
                            "return item {} is not a binding variable reference and has no alias",
                            ave.text()
                        ),
                    );
                }
                let agg = directly(ave, "aggregate function");
                aggregating |= agg;
                named.push((item, ave, n, agg));
            }
            if let Some(gbc) = gbc {
                let mut refs = Vec::new();
                find(gbc, "binding variable reference", &mut refs);
                grouping = refs.into_iter().map(|r| (r, r.text())).collect();
            }
            // SR 10: with GROUP BY, an item is grouping (its alias is a grouping element) or
            // aggregating, and aggregating items see the grouping columns in the record and the
            // rest of the table only inside aggregate functions.
            let mut group = scope.record.clone();
            for (r, g) in &grouping {
                match named.iter().find(|(_, _, n, _)| n.as_ref() == Some(g)) {
                    Some((_, ave, _, _)) => {
                        group.insert(g.clone(), bound(ave, &incoming));
                    }
                    // reading: a grouping element that names no alias names an incoming field
                    // (16.15 SR 2 b ii 2)
                    None => match incoming.get(g) {
                        Some(var) => {
                            group.insert(g.clone(), var.clone());
                        }
                        None => self.report(
                            r,
                            "20.12 SR 8",
                            format!("{g} is not a field of the incoming working record"),
                        ),
                    },
                }
            }
            let mut rest = scope.table.clone();
            rest.retain(|n, _| !grouping.iter().any(|(_, g)| g == n));
            let mut inner = group.clone();
            inner.extend(rest);
            for (item, ave, n, agg) in &named {
                let grouped = n
                    .as_ref()
                    .is_some_and(|n| grouping.iter().any(|(_, g)| g == n));
                let env = if gbc.is_some() && !grouped && *agg {
                    Env {
                        vars: group.clone(),
                        agg: Some(inner.clone()),
                        unbound: "20.12 SR 8",
                    }
                } else {
                    if gbc.is_some() && !grouped {
                        self.report(
                            item,
                            "14.11 SR 10",
                            format!(
                                "{} is neither a grouping item nor aggregating",
                                n.as_deref().unwrap_or("item")
                            ),
                        );
                    }
                    Env::new(incoming.clone())
                };
                self.expr(ave, &env, At::default());
                if let Some(n) = n
                    && cols.insert(n.clone(), bound(ave, &incoming)).is_some()
                {
                    self.report(item, "14.11 SR 11", format!("column {n} is returned twice"));
                }
            }
        }
        // 14.10 SR 4 c
        if let Some(obc) =
            own(prs, "order by and page statement").and_then(|o| own(o, "order by clause"))
        {
            let mut refs = cols.clone();
            if gbc.is_some() {
                for (_, g) in &grouping {
                    if !refs.contains_key(g) {
                        refs.insert(
                            g.clone(),
                            incoming.get(g).cloned().unwrap_or_else(Var::value),
                        );
                    }
                }
            } else if !distinct && !aggregating {
                let mut all = incoming.clone();
                all.extend(refs);
                refs = all;
            }
            if gbc.is_none() && !aggregating && contains(obc, "aggregate function") {
                self.report(
                    obc,
                    "14.10 SR 4",
                    "an aggregate in ORDER BY without grouping or aggregation".into(),
                );
            }
            if contains(obc, "nested query specification") {
                self.report(
                    obc,
                    "14.10 SR 4",
                    "a sort key contains a nested query".into(),
                );
            }
            let env = Env {
                vars: refs,
                agg: Some(incoming),
                unbound: "14.10 SR 4",
            };
            self.expr(obc, &env, At::default());
        }
        Some(cols)
    }

    // --- graph patterns -----------------------------------------------------------------

    /// 16.3 SR 3-5, 16.4, 16.6, 16.7: check a graph pattern and its WHERE clauses against the
    /// incoming names; give its variables with their degree of exposure, and its subpath
    /// variables.
    fn graph_pattern(&mut self, gp: &'t Plain, incoming: &Fields) -> (Fields, BTreeSet<String>) {
        let mut pat = Pattern::default();
        let keep = own(gp, "keep clause").and_then(|k| own(k, "path pattern prefix"));
        let mut paths: Vec<String> = Vec::new();
        // (path pattern expression, exposure, selective) per path pattern
        let mut each: Vec<(&Plain, Exposed, bool)> = Vec::new();
        for pp in own(gp, "path pattern list")
            .map(|l| owns(l, "path pattern"))
            .unwrap_or_default()
        {
            // 16.4 SR 6-7 move a KEEP prefix and a path mode into each path pattern.
            let prefixes: Vec<&Plain> = own(pp, "path pattern prefix")
                .into_iter()
                .chain(keep)
                .collect();
            let restrictive = prefixes.iter().any(|p| restricts(p));
            let selective = prefixes.iter().any(|p| selects(p));
            if let Some(bv) =
                own(pp, "path variable declaration").and_then(|d| first(d, "binding variable"))
            {
                paths.push(bv.text());
            }
            let Some(ppe) = own(pp, "path pattern expression") else {
                continue;
            };
            let ctx = Ctx {
                selective: selective.then_some(ppe),
                ..Ctx::default()
            };
            let mut exposed = self.expose(ppe, restrictive, &ctx, &mut pat);
            // 16.7 SR 22 h
            for (_, d) in exposed.values_mut() {
                if *d == Exp::Unbounded {
                    *d = Exp::Bounded;
                }
            }
            each.push((ppe, exposed, selective));
        }
        // 16.4 SR 3-4
        let mut exposed = Exposed::new();
        for (_, e, _) in &each {
            for (n, &(sort, d)) in e {
                match exposed.get(n) {
                    None => {
                        exposed.insert(n.clone(), (sort, d));
                    }
                    Some(&(was, prev)) => {
                        if sort == Sort::Subpath || was == Sort::Subpath {
                            self.report(
                                gp,
                                "16.4 SR 4",
                                format!("two path patterns expose subpath variable {n}"),
                            );
                        } else if d != Exp::Single || prev != Exp::Single {
                            self.report(
                                gp,
                                "16.4 SR 3",
                                format!("{n} is exposed by two path patterns, not as an unconditional singleton in both"),
                            );
                        }
                    }
                }
            }
        }
        self.names(gp, &pat, &paths);
        self.selective_rules(&each);
        let mut globals = Fields::new();
        let mut subpaths = BTreeSet::new();
        for (n, &(sort, d)) in &exposed {
            match sort {
                Sort::Subpath => {
                    subpaths.insert(n.clone());
                }
                _ => {
                    let kind = if sort == Sort::Node {
                        Kind::Node
                    } else {
                        Kind::Edge
                    };
                    globals.insert(n.clone(), Var::new(kind, degree(d)));
                }
            }
        }
        for n in &paths {
            globals
                .entry(n.clone())
                .or_insert(Var::new(Kind::Path, Degree::Single));
        }
        // 16.3 SR 25: expressions see the incoming names, shadowed by the pattern's own.
        let mut base = incoming.clone();
        base.retain(|n, _| !globals.contains_key(n) && !subpaths.contains(n));
        if let Some(w) = own(gp, "graph pattern where clause") {
            pat.wheres.push(Where {
                cond: w,
                local: Local::Graph,
                ctx: Ctx::default(),
            });
        }
        let wheres = std::mem::take(&mut pat.wheres);
        for w in &wheres {
            let mut env = base.clone();
            for (n, var) in &globals {
                env.insert(n.clone(), self.verdict(n, var, w, &pat, &exposed));
            }
            self.expr(w.cond, &Env::new(env), At::default());
        }
        (globals, subpaths)
    }

    /// 16.3 SR 4, 16.4 SR 5, 4.11.4: what one name may identify in a graph pattern.
    fn names(&mut self, gp: &'t Plain, pat: &Pattern<'t>, paths: &[String]) {
        let mut sorts: BTreeMap<&str, BTreeSet<Sort>> = BTreeMap::new();
        for (n, sort, _) in &pat.elements {
            sorts.entry(n.as_str()).or_default().insert(*sort);
        }
        for (n, _) in &pat.subpaths {
            sorts.entry(n.as_str()).or_default().insert(Sort::Subpath);
        }
        for (n, s) in &sorts {
            if s.contains(&Sort::Node) && s.contains(&Sort::Edge) {
                self.report(
                    gp,
                    "16.4 SR 5",
                    format!("{n} names a node variable and an edge variable"),
                );
            }
            if s.contains(&Sort::Subpath) && s.len() > 1 {
                self.report(
                    gp,
                    "16.3 SR 4",
                    format!("{n} names a subpath variable and an element variable"),
                );
            }
        }
        let mut seen = BTreeSet::new();
        for n in paths {
            if !seen.insert(n) {
                self.report(gp, "4.11.4", format!("path variable {n} is declared twice"));
            }
            if sorts.contains_key(n.as_str()) {
                self.report(
                    gp,
                    "16.3 SR 4",
                    format!("{n} names a path variable and another graph pattern variable"),
                );
            }
        }
    }

    /// 16.6 SR 7. Reading: an element variable declared in a path pattern that is not
    /// selective is exterior, even if a selective one declares it too.
    fn selective_rules(&mut self, each: &[(&'t Plain, Exposed, bool)]) {
        let exterior: BTreeSet<&String> = each
            .iter()
            .filter(|(_, _, s)| !s)
            .flat_map(|(_, e, _)| e.keys())
            .collect();
        for (i, (ppe, e, s)) in each.iter().enumerate() {
            if !s {
                continue;
            }
            let single = |n: &Option<String>| {
                n.clone()
                    .filter(|n| e.get(n).is_some_and(|v| v.1 == Exp::Single))
            };
            let left = single(&boundary(ppe, false));
            let right = single(&boundary(ppe, true));
            for (n, (sort, _)) in e {
                if *sort == Sort::Subpath || left.as_ref() == Some(n) || right.as_ref() == Some(n) {
                    continue;
                }
                let elsewhere = each
                    .iter()
                    .enumerate()
                    .any(|(j, (_, f, s))| j != i && *s && f.contains_key(n));
                if exterior.contains(n) || elsewhere {
                    self.report(
                        ppe,
                        "16.6 SR 7",
                        format!("{n} is a strict interior variable of a selective path pattern and is declared outside it"),
                    );
                }
            }
        }
    }

    /// 16.7 SR 22: the variables `node` exposes and their degree of exposure; also collects
    /// declarations and WHERE clauses into `pat`.
    fn expose(
        &mut self,
        node: &'t Plain,
        restrictive: bool,
        ctx: &Ctx<'t>,
        pat: &mut Pattern<'t>,
    ) -> Exposed {
        let exposed = match name(node) {
            Some(op @ ("path multiset alternation" | "path pattern union")) => {
                let operands = owns(node, "path term");
                let mut each = Vec::new();
                for &operand in &operands {
                    let mut inner = ctx.clone();
                    inner.unions.push((operand, node));
                    each.push(self.expose(operand, restrictive, &inner, pat));
                }
                if op == "path multiset alternation" {
                    // SR 10 c
                    let mut seen = BTreeSet::new();
                    for e in &each {
                        for (n, (sort, _)) in e {
                            if *sort == Sort::Subpath && !seen.insert(n.clone()) {
                                self.report(
                                    node,
                                    "16.7 SR 10",
                                    format!("subpath variable {n} is declared by two operands"),
                                );
                            }
                        }
                    }
                }
                // SR 22 d
                let mut out = Exposed::new();
                let names: BTreeSet<&String> = each.iter().flat_map(|e| e.keys()).collect();
                for n in names {
                    let found: Vec<(Sort, Exp)> =
                        each.iter().filter_map(|e| e.get(n).copied()).collect();
                    let degrees: Vec<Exp> = found.iter().map(|f| f.1).collect();
                    let d =
                        if found.len() == each.len() && degrees.iter().all(|d| *d == Exp::Single) {
                            Exp::Single
                        } else if degrees.contains(&Exp::Unbounded) {
                            Exp::Unbounded
                        } else if degrees.contains(&Exp::Bounded) {
                            Exp::Bounded
                        } else {
                            Exp::Conditional
                        };
                    out.insert(n.clone(), (found[0].0, d));
                }
                out
            }
            Some("path concatenation") => {
                let mut left = match own(node, "path term") {
                    Some(t) => self.expose(t, restrictive, ctx, pat),
                    None => Exposed::new(),
                };
                let right = match own(node, "path factor") {
                    Some(f) => self.expose(f, restrictive, ctx, pat),
                    None => Exposed::new(),
                };
                // SR 22 c
                for (n, (sort, d)) in right {
                    match left.get(&n) {
                        None => {
                            left.insert(n, (sort, d));
                        }
                        Some(&(was, prev)) => {
                            if d != Exp::Single || prev != Exp::Single {
                                self.report(
                                    node,
                                    "16.7 SR 22",
                                    format!("{n} is exposed by both operands of a concatenation, not as an unconditional singleton in both"),
                                );
                            } else if sort == Sort::Subpath || was == Sort::Subpath {
                                self.report(
                                    node,
                                    "16.7 SR 22",
                                    format!("subpath variable {n} is joined in a concatenation"),
                                );
                            }
                        }
                    }
                }
                left
            }
            Some("quantified path primary") => {
                let bounded = own(node, "graph pattern quantifier").is_some_and(bounded);
                let inner = match own(node, "path primary") {
                    Some(p) => self.expose(p, restrictive, ctx, pat),
                    None => Exposed::new(),
                };
                // SR 22 e
                inner
                    .into_iter()
                    .map(|(n, (sort, d))| {
                        let d = if restrictive || (bounded && d != Exp::Unbounded) {
                            Exp::Bounded
                        } else {
                            Exp::Unbounded
                        };
                        (n, (sort, d))
                    })
                    .collect()
            }
            Some("questioned path primary") => {
                let inner = match own(node, "path primary") {
                    Some(p) => self.expose(p, restrictive, ctx, pat),
                    None => Exposed::new(),
                };
                // SR 22 f
                inner
                    .into_iter()
                    .map(|(n, (sort, d))| match d {
                        Exp::Single | Exp::Conditional => (n, (sort, Exp::Conditional)),
                        group => (n, (sort, group)),
                    })
                    .collect()
            }
            Some("parenthesized path pattern expression") => {
                let mode = own(node, "path mode prefix").is_some_and(restricts);
                let mut inner = ctx.clone();
                inner.pppes.push(node);
                let mut exposed = match own(node, "path pattern expression") {
                    Some(ppe) => self.expose(ppe, restrictive || mode, &inner, pat),
                    None => Exposed::new(),
                };
                if let Some(sv) = own(node, "subpath variable declaration")
                    .and_then(|d| own(d, "subpath variable"))
                {
                    // SR 22 b
                    let n = sv.text();
                    if exposed.contains_key(&n) {
                        self.report(
                            node,
                            "16.7 SR 22",
                            format!("subpath variable {n} is declared inside its own declaration"),
                        );
                    }
                    pat.subpaths.push((n.clone(), node));
                    exposed.insert(n, (Sort::Subpath, Exp::Single));
                }
                if let Some(w) = own(node, "parenthesized path pattern where clause") {
                    pat.wheres.push(Where {
                        cond: w,
                        local: Local::Paren(node),
                        ctx: inner,
                    });
                }
                exposed
            }
            Some("element pattern") => {
                let mut exposed = Exposed::new();
                let sort = if own(node, "node pattern").is_some() {
                    Sort::Node
                } else {
                    Sort::Edge
                };
                let filler = first(node, "element pattern filler");
                let var = filler
                    .and_then(|f| own(f, "element variable declaration"))
                    .and_then(|d| first(d, "binding variable"))
                    .map(Plain::text);
                if let Some(n) = &var {
                    pat.elements.push((n.clone(), sort, node));
                    exposed.insert(n.clone(), (sort, Exp::Single));
                }
                if let Some(predicate) = filler.and_then(|f| own(f, "element pattern predicate")) {
                    if own(predicate, "element pattern where clause").is_some() && var.is_none() {
                        self.report(
                            node,
                            "16.7 SR 21",
                            "an element pattern with WHERE declares no variable".into(),
                        );
                    }
                    // 16.3 SR 21, 16.7 SR 12: both become a WHERE around the element pattern.
                    pat.wheres.push(Where {
                        cond: predicate,
                        local: Local::Element(var),
                        ctx: ctx.clone(),
                    });
                }
                exposed
            }
            Some("path pattern expression" | "path term" | "path factor" | "path primary") => {
                match kids(node).into_iter().next() {
                    Some(k) => self.expose(k, restrictive, ctx, pat),
                    None => Exposed::new(),
                }
            }
            _ => Exposed::new(),
        };
        pat.exposed.insert(node, exposed.clone());
        exposed
    }

    /// 20.12 SR 10-12, 16.7 SR 11 and 24, 16.6 SR 8: what a reference to graph pattern
    /// variable `n` from WHERE clause `w` is.
    fn verdict(
        &self,
        n: &str,
        global: &Var,
        w: &Where<'t>,
        pat: &Pattern<'t>,
        exposed: &Exposed,
    ) -> Var {
        let mut var = global.clone();
        if global.kind == Kind::Path {
            if !matches!(w.local, Local::Graph) {
                var.bad = Some((
                    "16.7 SR 24",
                    format!("path variable {n} in a parenthesized path pattern WHERE clause"),
                ));
            }
            return var;
        }
        let by = |node: &Plain| {
            pat.exposed
                .get(&(node as *const Plain))
                .and_then(|e| e.get(n))
                .map(|v| v.1)
        };
        let mut bad = None;
        if let Some(spp) = w.ctx.selective
            && by(spp).is_none()
        {
            bad = Some((
                "16.6 SR 8",
                format!("a selective path pattern references {n}, declared outside it"),
            ));
        }
        for &(operand, union) in &w.ctx.unions {
            let outside = pat
                .elements
                .iter()
                .any(|(e, _, at)| e == n && !self.inside(at, union));
            if bad.is_none() && by(operand).is_none() && !outside {
                bad = Some((
                    "16.7 SR 11",
                    format!("{n} is declared in another operand of the union only"),
                ));
            }
        }
        let local = match &w.local {
            Local::Graph => exposed.get(n).map(|v| v.1),
            Local::Paren(p) => by(p),
            Local::Element(v) => (v.as_deref() == Some(n)).then_some(Exp::Single),
        };
        let d = match local {
            Some(d) => d,
            // SR 11 a ii 2: the innermost enclosing declaration, which must be a singleton
            None => {
                let skip = matches!(w.local, Local::Paren(_)) as usize;
                let d = w
                    .ctx
                    .pppes
                    .iter()
                    .rev()
                    .skip(skip)
                    .find_map(|p| by(p))
                    .or_else(|| exposed.get(n).map(|v| v.1))
                    .unwrap_or(Exp::Single);
                if bad.is_none() && matches!(d, Exp::Bounded | Exp::Unbounded) {
                    bad = Some((
                        "20.12 SR 11",
                        format!("non-local reference to {n} has group degree"),
                    ));
                }
                d
            }
        };
        if bad.is_none() && d == Exp::Unbounded {
            bad = Some((
                "20.12 SR 12",
                format!("{n} is an effectively unbounded group here"),
            ));
        }
        var.degree = degree(d);
        var.bad = bad;
        var
    }

    // --- expressions --------------------------------------------------------------------

    fn expr(&mut self, node: &'t Plain, env: &Env, at: At) {
        let Some(n) = name(node) else {
            return;
        };
        match n {
            "binding variable reference" => self.reference(node, env, at),
            "aggregating value expression" => {
                for k in kids(node) {
                    let vertical = At {
                        vertical: true,
                        ..at
                    };
                    match name(k) {
                        Some("value expression") => kids(k)
                            .into_iter()
                            .for_each(|c| self.expr(c, env, vertical)),
                        _ => self.expr(k, env, at),
                    }
                }
            }
            "value expression" => {
                let at = At {
                    vertical: false,
                    ..at
                };
                kids(node).into_iter().for_each(|k| self.expr(k, env, at));
            }
            "aggregate function" => {
                // 20.1 SR 7. Reading: an aggregate not in an <aggregating value expression>
                // (in a WHERE clause, say) is horizontal too.
                if !at.vertical {
                    let mut refs = Vec::new();
                    find(node, "binding variable reference", &mut refs);
                    let groups: BTreeSet<String> = refs
                        .iter()
                        .map(|r| r.text())
                        .filter(|r| lookup(env, true, r).is_some_and(|v| v.degree == Degree::Group))
                        .collect();
                    if groups.len() != 1 {
                        self.report(
                            node,
                            "20.1 SR 7",
                            format!(
                                "a horizontal aggregate references {} group variables, not one",
                                groups.len()
                            ),
                        );
                    }
                }
                let at = At {
                    agg: true,
                    vertical: false,
                };
                kids(node).into_iter().for_each(|k| self.expr(k, env, at));
            }
            "let value expression" => self.let_value(node, env, at),
            "exists predicate" => self.exists(node, env),
            // 20.6 SR 8 and 11.2 SR 2: the body's declared type is a binding table type, which
            // a body whose emitting result statement is FINISH does not have (14.10 SR 5).
            "value query expression" | "nested binding table query specification" => {
                if let Some(pb) = first(node, "procedure body")
                    && emits_finish(pb)
                {
                    let rule = if n == "value query expression" {
                        "20.6 SR 8"
                    } else {
                        "11.2 SR 2"
                    };
                    self.report(node, rule, "the body's result statement is FINISH".into());
                }
                kids(node).into_iter().for_each(|k| self.expr(k, env, at));
            }
            "procedure body" => {
                self.body(
                    node,
                    Scope {
                        record: env.vars.clone(),
                        table: Fields::new(),
                    },
                );
            }
            "property reference" => {
                if let Some(source) = own(node, "property source") {
                    self.singleton(source, env, at, "20.1 SR 4-6");
                }
                kids(node).into_iter().for_each(|k| self.expr(k, env, at));
            }
            "directed predicate"
            | "labeled predicate"
            | "source/destination predicate"
            | "all_different predicate"
            | "same predicate"
            | "property_exists predicate"
            | "element_id function" => {
                let rule = match n {
                    "directed predicate" => "19.8 SR 2",
                    "labeled predicate" => "19.9 SR 2",
                    "source/destination predicate" => "19.10 SR 2-3",
                    "all_different predicate" => "19.11 SR 2",
                    "same predicate" => "19.12 SR 2",
                    "property_exists predicate" => "19.13 SR 2",
                    _ => "20.10 SR 2",
                };
                let mut refs = Vec::new();
                find(node, "element variable reference", &mut refs);
                for r in refs {
                    self.singleton(r, env, at, rule);
                }
                kids(node).into_iter().for_each(|k| self.expr(k, env, at));
            }
            _ => kids(node).into_iter().for_each(|k| self.expr(k, env, at)),
        }
    }

    /// 20.12 SR 8: a reference names a field of the incoming working record.
    fn reference(&mut self, r: &'t Plain, env: &Env, at: At) {
        let n = r.text();
        match lookup(env, at.agg, &n) {
            None => {
                let rule = if at.agg && env.agg.is_some() {
                    "20.12 SR 8"
                } else {
                    env.unbound
                };
                let detail = match rule {
                    "14.10 SR 4" => {
                        format!("{n} is neither a return alias nor visible to ORDER BY here")
                    }
                    _ => format!("{n} is not a field of the incoming working record"),
                };
                self.report(r, rule, detail);
            }
            Some(Var {
                bad: Some((rule, detail)),
                ..
            }) => {
                let (rule, detail) = (*rule, detail.clone());
                self.report(r, rule, detail);
            }
            Some(_) => {}
        }
    }

    /// Outside an aggregate function, `node` (a bare reference) must not have group degree.
    fn singleton(&mut self, node: &'t Plain, env: &Env, at: At, rule: &'static str) {
        if at.agg {
            return;
        }
        if let Some(n) = bare(node)
            && lookup(env, false, &n).is_some_and(|v| v.degree == Degree::Group)
        {
            self.report(node, rule, format!("{n} has group degree of reference"));
        }
    }

    /// 20.5.
    fn let_value(&mut self, node: &'t Plain, env: &Env, at: At) {
        let defs = own(node, "let variable definition list")
            .map(|l| owns(l, "let variable definition"))
            .unwrap_or_default();
        let mut added = Fields::new();
        for def in defs {
            let Some((bv, value)) = definition(def) else {
                continue;
            };
            // reading: a definition sees the outer record only
            self.expr(def, env, at);
            let n = bv.text();
            if env.vars.contains_key(&n) {
                self.report(
                    def,
                    "20.5 SR 3",
                    format!("{n} is already a field of the record"),
                );
            } else if added.contains_key(&n) {
                self.report(def, "20.5 SR 4", format!("{n} is defined twice"));
            }
            added.insert(n, value.map_or_else(Var::value, |v| bound(v, &env.vars)));
        }
        let mut inner = env.clone();
        inner.vars.extend(added.clone());
        if let Some(agg) = &mut inner.agg {
            agg.extend(added);
        }
        if let Some(rhs) = own(node, "value expression") {
            self.expr(rhs, &inner, at);
        }
    }

    /// 19.4 SR 2-4: a correlated MATCH ... RETURN or nested query.
    fn exists(&mut self, node: &'t Plain, env: &Env) {
        let scope = Scope {
            record: env.vars.clone(),
            table: Fields::new(),
        };
        if let Some(gp) = own(node, "graph pattern") {
            self.pattern_match(gp, None, scope);
        } else if let Some(block) = own(node, "match statement block") {
            let mut scope = scope;
            for m in owns(block, "match statement") {
                scope = self.match_statement(m, scope);
            }
        } else if let Some(pb) = first(node, "procedure body") {
            // SR 5: the body's declared type is a binding table type (not FINISH's empty type).
            if emits_finish(pb) {
                self.report(
                    node,
                    "19.4 SR 5",
                    "the body's result statement is FINISH".into(),
                );
            }
            self.body(pb, scope);
        }
    }
}

// --- graph pattern bookkeeping ----------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Sort {
    Node,
    Edge,
    Subpath,
}

/// Degree of exposure (16.7 SR 22).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Exp {
    Single,
    Conditional,
    Bounded,
    Unbounded,
}

type Exposed = BTreeMap<String, (Sort, Exp)>;

fn degree(d: Exp) -> Degree {
    match d {
        Exp::Single => Degree::Single,
        Exp::Conditional => Degree::Conditional,
        Exp::Bounded | Exp::Unbounded => Degree::Group,
    }
}

#[derive(Debug, Clone, Default)]
struct Ctx<'t> {
    /// Enclosing parenthesized path pattern expressions, innermost last.
    pppes: Vec<&'t Plain>,
    /// Enclosing (operand, path pattern union or multiset alternation) pairs.
    unions: Vec<(&'t Plain, &'t Plain)>,
    /// The expression of the enclosing selective path pattern.
    selective: Option<&'t Plain>,
}

/// Where a WHERE clause sits (20.12 SR 10-11).
enum Local<'t> {
    Graph,
    Paren(&'t Plain),
    /// An element pattern with its variable, a parenthesized expression by 16.7 SR 12.
    Element(Option<String>),
}

struct Where<'t> {
    cond: &'t Plain,
    local: Local<'t>,
    ctx: Ctx<'t>,
}

#[derive(Default)]
struct Pattern<'t> {
    exposed: HashMap<*const Plain, Exposed>,
    elements: Vec<(String, Sort, &'t Plain)>,
    subpaths: Vec<(String, &'t Plain)>,
    wheres: Vec<Where<'t>>,
}

/// 16.6 SR 3: a path mode other than WALK.
fn restricts(prefix: &Plain) -> bool {
    let mut modes = Vec::new();
    find(prefix, "path mode", &mut modes);
    modes.iter().any(|m| !m.text().eq_ignore_ascii_case("WALK"))
}

fn keyword(node: &Plain, kw: &str) -> bool {
    matches!(node, Plain::Kw(t) if t.eq_ignore_ascii_case(kw))
}

/// 16.6 SR 4: a search prefix other than ALL.
fn selects(prefix: &Plain) -> bool {
    let mut searches = Vec::new();
    find(prefix, "path search prefix", &mut searches);
    searches.iter().any(|s| own(s, "all path search").is_none())
}

fn bounded(quantifier: &Plain) -> bool {
    match kids(quantifier).first().and_then(|k| name(k)) {
        Some("fixed quantifier") => true,
        Some("general quantifier") => contains(quantifier, "upper bound"),
        _ => false,
    }
}

/// 16.6 SR 5 b-c: the variable of the first (or last) node pattern of a path pattern
/// expression, unless that sits in a union, an alternation or a quantified or questioned
/// primary (which do not expose it as an unconditional singleton).
fn boundary(node: &Plain, last: bool) -> Option<String> {
    match name(node)? {
        "path concatenation" => boundary(
            own(node, if last { "path factor" } else { "path term" })?,
            last,
        ),
        "parenthesized path pattern expression" => {
            boundary(own(node, "path pattern expression")?, last)
        }
        "node pattern" => own(node, "element pattern filler")
            .and_then(|f| own(f, "element variable declaration"))
            .and_then(|d| first(d, "binding variable"))
            .map(Plain::text),
        "path pattern expression"
        | "path term"
        | "path factor"
        | "path primary"
        | "element pattern" => boundary(kids(node).into_iter().next()?, last),
        _ => None,
    }
}

// --- helpers ------------------------------------------------------------------------------

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

/// The child of `node` that is a `<want>`.
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

/// Contains without an intervening <procedure body> (5.3).
fn directly(node: &Plain, want: &str) -> bool {
    match node {
        Plain::Def { name, .. } if name == want => true,
        Plain::Def { name, .. } if name == "procedure body" => false,
        Plain::Def { children, .. } => children.iter().any(|c| directly(c, want)),
        _ => false,
    }
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

/// What a name bound to `value` is: a bare reference passes its kind and degree on.
fn bound(value: &Plain, env: &Fields) -> Var {
    match bare(value).and_then(|n| env.get(&n)) {
        Some(var) => Var::new(var.kind, var.degree),
        None => Var::value(),
    }
}

fn lookup<'e>(env: &'e Env, agg: bool, n: &str) -> Option<&'e Var> {
    match (&env.agg, agg) {
        (Some(inner), true) => inner.get(n),
        _ => env.vars.get(n),
    }
}

/// 14.4 SR 4, 15.1: a name an OPTIONAL MATCH or OPTIONAL CALL binds can be null.
fn optional(mut var: Var) -> Var {
    if var.degree == Degree::Single {
        var.degree = Degree::Conditional;
    }
    var
}

/// Equality of the joined names (16.3 SR 20) needs comparable kinds.
fn joinable(a: Kind, b: Kind) -> bool {
    a == b || a == Kind::Value || b == Kind::Value
}

/// The <binding variable> a variable definition defines, and its <value expression>.
fn definition(def: &Plain) -> Option<(&Plain, Option<&Plain>)> {
    if let Some(inner) = own(def, "value variable definition") {
        return definition(inner);
    }
    let bv = own(def, "binding variable")?;
    let value = own(def, "value expression").or_else(|| {
        own(def, "opt typed value initializer")
            .and_then(|o| own(o, "value initializer"))
            .and_then(|v| own(v, "value expression"))
    });
    Some((bv, value))
}

/// The name an <identifier> stands for: a delimited one without its quotes, doubled quotes
/// undoubled (21.3, representative form).
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

/// A linear statement whose declared type is FINISH's empty type (14.3 SR 6, 13.1 SR 9, 14.10
/// SR 5): its last element is FINISH, explicit or implicit (13.1 SR 2-3: a data-modifying
/// statement without a primitive result statement), or a nested query specification whose
/// body emits FINISH (20.6 SR 5 b ii). Reading: 14.2 SR 5 is applied to that too, since an
/// empty-typed operand cannot be column name-equal (SR 10).
fn finishes(lqs: &Plain) -> bool {
    let mut parts = Vec::new();
    steps(lqs, &mut parts);
    parts.last().is_some_and(|p| match name(p) {
        Some("primitive result statement") => kids(p).iter().any(|k| keyword(k, "FINISH")),
        // Either body's declared type is its own (9.1 SR 2-3).
        Some("nested query specification" | "nested data-modifying procedure specification") => {
            first(p, "procedure body").is_some_and(emits_finish)
        }
        // 13.1 SR 2-3.
        _ => name(lqs) == Some("linear data-modifying statement"),
    })
}

/// 9.2 SR 13 and 20.6 SR 4-5: a procedure body whose declared type is the empty type, its
/// last statement being a one-operand composite or a data-modifying statement that finishes,
/// or a catalog-modifying statement.
fn emits_finish(pb: &Plain) -> bool {
    let Some(sb) = own(pb, "statement block") else {
        return false;
    };
    let last = match owns(sb, "next statement").last() {
        Some(next) => own(next, "statement"),
        None => own(sb, "statement"),
    };
    let Some(inner) = last.and_then(|st| kids(st).into_iter().next()) else {
        return false;
    };
    match name(inner) {
        Some("composite query statement") => {
            let Some(cqe) = own(inner, "composite query expression") else {
                return false;
            };
            let mut operands = Vec::new();
            conjuncts(cqe, &mut operands);
            matches!(operands.as_slice(), [op] if finishes(op))
        }
        Some("linear data-modifying statement") => finishes(inner),
        // 12.1 SR 4: the empty type.
        Some("linear catalog-modifying statement") => true,
        _ => false,
    }
}

fn items<'t>(st: &'t Plain, want: &[&str]) -> Vec<&'t Plain> {
    let mut out = Vec::new();
    find_any(st, want, &mut out);
    out
}
