//! Independent checker for one generated tree. Part of the trusted base: it reads the ISO
//! EBNF through `bnf` and `tokens`, and never touches `cfg` or the generator.
//!
//! A tree passes when:
//! - every node's children, with synthetic grouping nodes flattened away, match the ISO EBNF
//!   of its definition (this is what makes the desugaring in `cfg` untrusted)
//! - every prose leaf satisfies the Syntax Rule that defines it
//! - the token-internal Syntax Rules hold (21.2 SR 57, 59-68, 21.3 SR 18)
//! - the rendered string is exactly the tree's tokens joined by one space, with tokens cut at
//!   lexical definitions, which `tokens::Grammar::check` proves are single tokens

mod conformance;
pub mod scope;

use crate::MatchModeDefault;
use crate::bnf::Ebnf;
use crate::features::Forbidden;
use crate::tokens::{EXCLUDED, Grammar};
use chrono::{NaiveDate, NaiveDateTime, NaiveTime};
use std::collections::HashSet;
use std::fmt;
use unicode_general_category::{GeneralCategory, get_general_category};

/// A tree as names and text, the only view of a tree the checker trusts.
#[derive(Debug, Clone)]
pub enum Plain {
    Def {
        name: String,
        /// A grouping node introduced by desugaring `[..]`, `{..|..}` or `...`.
        synthetic: bool,
        children: Vec<Plain>,
    },
    Kw(String),
    Term(String),
    /// A prose leaf ("!! See the Syntax Rules") of definition `def`.
    Leaf {
        def: String,
        text: String,
    },
}

impl Plain {
    /// The characters this subtree spells, with no separators added.
    pub fn text(&self) -> String {
        match self {
            Plain::Def { children, .. } => children.iter().map(Plain::text).collect(),
            Plain::Kw(t) | Plain::Term(t) | Plain::Leaf { text: t, .. } => t.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Violation {
    pub path: String,
    pub rule: &'static str,
    pub detail: String,
}

impl fmt::Display for Violation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {} at {}", self.rule, self.detail, self.path)
    }
}

pub struct Verifier<'b> {
    grammar: Grammar<'b>,
    lexical: HashSet<&'b str>,
    reserved: HashSet<String>,
    /// Check the Syntax Rules `refine` compiles into the grammar, with this ID086.
    syntax_rules: Option<MatchModeDefault>,
    /// Conformance rules in force: no tree may contain a match of any of their patterns.
    conformance: Vec<Forbidden>,
    /// Check the scoping of binding variables (`scope`).
    scope: bool,
}

impl<'b> Verifier<'b> {
    pub fn new(grammar: Grammar<'b>) -> Self {
        let lexical = grammar.lexical();
        let reserved = grammar.reserved_words();
        Verifier {
            grammar,
            lexical,
            reserved,
            syntax_rules: None,
            conformance: Vec::new(),
            scope: false,
        }
    }

    /// Also check that variables are referenced in scope and declared new.
    pub fn with_scope(mut self) -> Self {
        self.scope = true;
        self
    }

    /// Also check 16.4 SR 6, 16.4 SR 14 and 13.1 SR 5.
    pub fn with_syntax_rules(mut self, id086: MatchModeDefault) -> Self {
        self.syntax_rules = Some(id086);
        self
    }

    /// Also check these conformance rules, the ones a claim leaves in force.
    pub fn with_conformance(mut self, rules: Vec<Forbidden>) -> Self {
        self.conformance = rules;
        self
    }

    /// The conformance rules in force that `tree` breaks.
    pub fn broken_conformance(&self, tree: &Plain) -> Vec<&Forbidden> {
        let t = conformance::Tree::new(tree);
        self.conformance
            .iter()
            .filter(|f| f.patterns.iter().any(|p| t.occurs(p)))
            .collect()
    }

    pub fn grammar(&self) -> &Grammar<'b> {
        &self.grammar
    }

    /// Every violation in `tree`, and whether `rendered` is its token rendering.
    pub fn verify(&self, tree: &Plain, rendered: &str) -> Vec<Violation> {
        let mut out = Vec::new();
        self.walk(tree, &mut Vec::new(), &mut out);
        if let Some(id086) = self.syntax_rules {
            syntax_rules(tree, id086, &mut Vec::new(), &mut out);
        }
        if self.scope {
            out.extend(scope::check(tree));
        }
        for f in self.broken_conformance(tree) {
            out.push(Violation {
                path: String::new(),
                rule: "conformance rule",
                detail: f.label.clone(),
            });
        }
        let expected = self.render(tree);
        if expected != rendered {
            out.push(Violation {
                path: String::new(),
                rule: "21.3 SR 13, 14",
                detail: format!("rendered text differs from the tree's tokens: {expected:?}"),
            });
        }
        out
    }

    /// Tokens joined by one space, a token being a literal of a syntactic rule or the whole
    /// text of a subtree rooted at a lexical definition.
    pub fn render(&self, tree: &Plain) -> String {
        let mut tokens = Vec::new();
        self.tokens(tree, &mut tokens);
        tokens.retain(|t| !t.is_empty());
        tokens.join(" ")
    }

    fn tokens(&self, node: &Plain, out: &mut Vec<String>) {
        match node {
            Plain::Def {
                name,
                synthetic,
                children,
            } => {
                if !synthetic && self.lexical.contains(name.as_str()) {
                    out.push(node.text());
                } else {
                    children.iter().for_each(|c| self.tokens(c, out));
                }
            }
            leaf => out.push(leaf.text()),
        }
    }

    fn walk<'t>(&self, node: &'t Plain, path: &mut Vec<&'t str>, out: &mut Vec<Violation>) {
        match node {
            Plain::Def {
                name,
                synthetic: false,
                children,
            } => {
                path.push(name);
                self.check_def(name, node, children, path, out);
                children.iter().for_each(|c| self.walk(c, path, out));
                path.pop();
            }
            Plain::Def { children, .. } => children.iter().for_each(|c| self.walk(c, path, out)),
            Plain::Leaf { def, text } => {
                if let Err((rule, detail)) = leaf_rule(def, text) {
                    out.push(violation(path, rule, detail));
                }
            }
            Plain::Kw(_) | Plain::Term(_) => {}
        }
    }

    fn check_def(
        &self,
        name: &str,
        node: &Plain,
        children: &[Plain],
        path: &[&str],
        out: &mut Vec<Violation>,
    ) {
        let Some(rhs) = self.grammar.rhs(name) else {
            out.push(violation(
                path,
                "ISO BNF",
                format!("<{name}> is not an ISO definition"),
            ));
            return;
        };
        let mut items = Vec::new();
        flatten(children, &mut items);
        if !self.seq_matches(rhs, &items) {
            let got: Vec<String> = items.iter().map(|i| short(i)).collect();
            out.push(violation(
                path,
                "ISO BNF",
                format!("children [{}] do not match the definition", got.join(" ")),
            ));
        }
        if let Err((rule, detail)) = self.token_rule(name, node) {
            out.push(violation(path, rule, detail));
        }
    }

    fn seq_matches(&self, rhs: &Ebnf, items: &[&Plain]) -> bool {
        self.m(rhs, items, 0, &|j| j == items.len())
    }

    /// Continuation-passing backtracking match of `e` against `items[i..]`.
    fn m(&self, e: &Ebnf, items: &[&Plain], i: usize, k: &dyn Fn(usize) -> bool) -> bool {
        match e {
            Ebnf::Seq(parts) => self.seq(parts, items, i, k),
            Ebnf::Alt(alts) => alts.iter().any(|a| self.m(a, items, i, k)),
            Ebnf::Opt(inner) => self.m(inner, items, i, k) || k(i),
            Ebnf::Repeat(inner) => self.rep(inner, items, i, k),
            Ebnf::Ref(want) => {
                matches!(items.get(i), Some(Plain::Def { name, synthetic: false, .. }) if name == want)
                    && k(i + 1)
            }
            Ebnf::Kw(want) => matches!(items.get(i), Some(Plain::Kw(t)) if t == want) && k(i + 1),
            Ebnf::Term(want) => {
                matches!(items.get(i), Some(Plain::Term(t)) if t == want) && k(i + 1)
            }
            Ebnf::Opaque(want) => {
                matches!(items.get(i), Some(Plain::Leaf { def, .. }) if def == want) && k(i + 1)
            }
        }
    }

    fn seq(&self, parts: &[Ebnf], items: &[&Plain], i: usize, k: &dyn Fn(usize) -> bool) -> bool {
        match parts.split_first() {
            None => k(i),
            Some((head, tail)) => self.m(head, items, i, &|j| self.seq(tail, items, j, k)),
        }
    }

    /// One or more; a pass that consumes nothing cannot repeat.
    fn rep(&self, inner: &Ebnf, items: &[&Plain], i: usize, k: &dyn Fn(usize) -> bool) -> bool {
        self.m(inner, items, i, &|j| {
            k(j) || (j > i && self.rep(inner, items, j, k))
        })
    }

    /// The same match at character level, for text whose shape the Syntax Rules give as a BNF
    /// definition (the contents of a duration string, 21.2 SR 68).
    fn chars_match(&self, def: &str, text: &[char]) -> bool {
        match self.grammar.rhs(def) {
            Some(rhs) => self.mc(rhs, text, 0, &|j| j == text.len(), 64),
            None => false,
        }
    }

    fn mc(&self, e: &Ebnf, s: &[char], i: usize, k: &dyn Fn(usize) -> bool, fuel: u32) -> bool {
        if fuel == 0 {
            return false;
        }
        match e {
            Ebnf::Seq(parts) => self.mc_seq(parts, s, i, k, fuel),
            Ebnf::Alt(alts) => alts.iter().any(|a| self.mc(a, s, i, k, fuel)),
            Ebnf::Opt(inner) => self.mc(inner, s, i, k, fuel) || k(i),
            Ebnf::Repeat(inner) => self.mc_rep(inner, s, i, k, fuel),
            Ebnf::Ref(name) => match self.grammar.rhs(name) {
                Some(rhs) => self.mc(rhs, s, i, k, fuel - 1),
                None => false,
            },
            Ebnf::Kw(t) | Ebnf::Term(t) => {
                let want: Vec<char> = t.chars().collect();
                s[i..].starts_with(&want) && k(i + want.len())
            }
            Ebnf::Opaque(def) => {
                i < s.len() && leaf_rule(def, &s[i].to_string()).is_ok() && k(i + 1)
            }
        }
    }

    fn mc_seq(
        &self,
        parts: &[Ebnf],
        s: &[char],
        i: usize,
        k: &dyn Fn(usize) -> bool,
        fuel: u32,
    ) -> bool {
        match parts.split_first() {
            None => k(i),
            Some((head, tail)) => self.mc(head, s, i, &|j| self.mc_seq(tail, s, j, k, fuel), fuel),
        }
    }

    fn mc_rep(
        &self,
        inner: &Ebnf,
        s: &[char],
        i: usize,
        k: &dyn Fn(usize) -> bool,
        fuel: u32,
    ) -> bool {
        self.mc(
            inner,
            s,
            i,
            &|j| k(j) || (j > i && self.mc_rep(inner, s, j, k, fuel)),
            fuel,
        )
    }

    /// Syntax Rules on the inside of a token.
    fn token_rule(&self, name: &str, node: &Plain) -> Result<(), (&'static str, String)> {
        match name {
            "byte string literal" => {
                let mut separators = Vec::new();
                find(node, "separator", &mut separators);
                match separators.iter().find(|s| !s.text().contains('\n')) {
                    Some(s) => Err((
                        "21.2 SR 57",
                        format!("separator {:?} has no newline", s.text()),
                    )),
                    None => Ok(()),
                }
            }
            "regular identifier" => {
                let normal = node.text().to_uppercase();
                if self.reserved.contains(&normal) {
                    Err((
                        "21.3 SR 18",
                        format!("identifier {normal} is a reserved word"),
                    ))
                } else {
                    Ok(())
                }
            }
            "duration string" => {
                let content =
                    quoted(node).ok_or(("21.2 SR 68", "not a plain quoted string".into()))?;
                let chars: Vec<char> = content.chars().collect();
                if self.chars_match("iso8601 years and months", &chars)
                    || self.chars_match("iso8601 days and time", &chars)
                {
                    Ok(())
                } else {
                    Err((
                        "21.2 SR 68",
                        format!("{content:?} is not an iso8601 duration"),
                    ))
                }
            }
            "date string" => temporal(node, "21.2 SR 59", |c| {
                c.len() == 10 && NaiveDate::parse_from_str(c, "%Y-%m-%d").is_ok()
            }),
            "time string" => temporal(node, "21.2 SR 62", |c| {
                c.len() >= 8 && NaiveTime::parse_from_str(c, "%H:%M:%S%.f").is_ok()
            }),
            "datetime string" => temporal(node, "21.2 SR 64", |c| {
                c.len() >= 19 && NaiveDateTime::parse_from_str(c, "%Y-%m-%dT%H:%M:%S%.f").is_ok()
            }),
            "time zone string" => temporal(node, "21.2 SR 61", |c| {
                let b = c.as_bytes();
                c.len() == 6
                    && (b[0] == b'+' || b[0] == b'-')
                    && b[3] == b':'
                    && c[1..3].parse::<u8>().is_ok_and(|h| h < 24)
                    && c[4..6].parse::<u8>().is_ok_and(|m| m < 60)
            }),
            _ => Ok(()),
        }
    }
}

/// How much text a prose leaf can span, as `leaf_rule` reads its Syntax Rule.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Span {
    /// One character.
    One,
    /// Any length, and every prefix of a valid leaf is valid.
    Run,
    /// Any length.
    Any,
}

pub(crate) fn leaf_span(def: &str) -> Span {
    match def {
        "whitespace" | "truncating whitespace" | "bracketed comment contents" => Span::Run,
        "external object reference" | "SQL-datetime literal" | "SQL-interval literal" => Span::Any,
        _ => Span::One,
    }
}

/// Each prose leaf against the Syntax Rule that defines it. Where a rule depends on context
/// or on implementation choices, this checks a stricter form.
pub(crate) fn leaf_rule(def: &str, text: &str) -> Result<(), (&'static str, String)> {
    let mut chars = text.chars();
    let one = match (chars.next(), chars.next()) {
        (Some(c), None) => Some(c),
        _ => None,
    };
    let bad = |rule: &'static str| Err((rule, format!("{text:?} is not a valid <{def}>")));
    let ok = |cond: bool, rule: &'static str| if cond { Ok(()) } else { bad(rule) };
    if let Some((_, why)) = EXCLUDED.iter().find(|(name, _)| *name == def) {
        return Err(("excluded", format!("<{def}> has no portable form: {why}")));
    }
    match def {
        "identifier start" => ok(
            one.is_some_and(|c| c == '_' || unicode_ident::is_xid_start(c)),
            "21.3 SR 1",
        ),
        "identifier extend" => ok(one.is_some_and(unicode_ident::is_xid_continue), "21.3 SR 2"),
        "character representation" | "string literal character" => ok(
            one.is_some_and(|c| !matches!(c, '\'' | '"' | '`' | '\\') && !c.is_control()),
            "21.2 SR 31-33, 41",
        ),
        "whitespace" => ok(
            !text.is_empty() && text.chars().all(char::is_whitespace),
            "21.3 SR 6",
        ),
        // Our implementation-defined (IV023) subset is just <space>.
        "truncating whitespace" => ok(
            !text.is_empty() && text.chars().all(|c| c == ' '),
            "21.3 SR 7",
        ),
        // Our implementation-defined (IA023) end-of-line indicator.
        "newline" => ok(text == "\n", "21.3 SR 12"),
        "simple comment character" => ok(one.is_some_and(|c| c != '\n' && c != '\r'), "21.3 SR 9"),
        "bracketed comment contents" => ok(!text.contains("*/"), "21.3 SR 10"),
        "bidirectional control character" => ok(
            one.is_some_and(|c| matches!(c, '\u{202A}'..='\u{202E}' | '\u{2066}'..='\u{2069}')),
            "21.3 SR 8",
        ),
        "other digit" => ok(
            one.is_some_and(|c| {
                get_general_category(c) == GeneralCategory::DecimalNumber && !c.is_ascii_digit()
            }),
            "21.4 SR 2",
        ),
        "other language character" => {
            ok(one.is_some_and(|c| !gql_language_character(c)), "21.4 SR 1")
        }
        "external object reference" => ok(
            text.contains(':') && !text.contains("//") && !text.chars().any(char::is_whitespace),
            "17.8 SR 2, 3",
        ),
        "SQL-datetime literal" => ok(
            text.strip_prefix("DATE '")
                .and_then(|r| r.strip_suffix('\''))
                .is_some_and(|d| d.len() == 10 && NaiveDate::parse_from_str(d, "%Y-%m-%d").is_ok()),
            "21.2 SR 69",
        ),
        "SQL-interval literal" => ok(
            text.strip_prefix("INTERVAL '")
                .and_then(|r| r.split_once("' "))
                .is_some_and(|(n, unit)| {
                    !n.is_empty()
                        && n.chars().all(|c| c.is_ascii_digit())
                        && matches!(
                            unit,
                            "YEAR" | "MONTH" | "DAY" | "HOUR" | "MINUTE" | "SECOND"
                        )
                }),
            "21.2 SR 70",
        ),
        _ => Err(("no rule", format!("no checked rule for prose leaf <{def}>"))),
    }
}

/// 21.4: simple Latin letters, digits and the GQL special characters.
fn gql_language_character(c: char) -> bool {
    c.is_ascii_alphabetic()
        || get_general_category(c) == GeneralCategory::DecimalNumber
        || " &*:=,@$\"!`>{[(<-.+?'\\}])/_|%~".contains(c)
}

fn temporal(
    node: &Plain,
    rule: &'static str,
    valid: impl Fn(&str) -> bool,
) -> Result<(), (&'static str, String)> {
    match quoted(node) {
        Some(c) if valid(&c) => Ok(()),
        Some(c) => Err((rule, format!("{c:?} is not in the accepted iso 8601 form"))),
        None => Err((rule, "not a plain quoted string".into())),
    }
}

/// The contents of a `'...'` or `"..."` literal without escapes or doubled quotes.
fn quoted(node: &Plain) -> Option<String> {
    let text = node.text();
    let text = text.strip_prefix('@').unwrap_or(&text);
    let inner = text
        .strip_prefix('\'')
        .and_then(|t| t.strip_suffix('\''))
        .or_else(|| text.strip_prefix('"').and_then(|t| t.strip_suffix('"')))?;
    (!inner.contains(['\'', '"', '\\'])).then(|| inner.to_string())
}

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

fn find<'t>(node: &'t Plain, want: &str, out: &mut Vec<&'t Plain>) {
    if let Plain::Def { name, children, .. } = node {
        if name == want {
            out.push(node);
        }
        children.iter().for_each(|c| find(c, want, out));
    }
}

fn short(p: &Plain) -> String {
    match p {
        Plain::Def { name, .. } => format!("<{name}>"),
        Plain::Kw(t) => t.clone(),
        Plain::Term(t) => format!("{t:?}"),
        Plain::Leaf { def, .. } => format!("!!<{def}>"),
    }
}

fn violation(path: &[&str], rule: &'static str, detail: String) -> Violation {
    let tail = &path[path.len().saturating_sub(4)..];
    let path = tail
        .iter()
        .map(|p| format!("<{p}>"))
        .collect::<Vec<_>>()
        .join(" > ");
    Violation { path, rule, detail }
}

// --- Syntax Rules above the token layer, read directly from the text ---------------------
//
// Reading: 16.4 SR 6 and 14 are applied per depth of graph pattern matching (16.4 SR 2), so a
// rule looks no further out than the nearest enclosing <graph pattern>. 13.1 SR 5 is read
// along the statement sequence, see `modifies`.

fn syntax_rules<'t>(
    node: &'t Plain,
    id086: MatchModeDefault,
    ancestors: &mut Vec<&'t Plain>,
    out: &mut Vec<Violation>,
) {
    let Plain::Def {
        name,
        synthetic,
        children,
    } = node
    else {
        return;
    };
    if !synthetic {
        let path: Vec<&str> = ancestors.iter().filter_map(|a| def_name(a)).collect();
        match name.as_str() {
            "quantified path primary" | "simplified quantified" => {
                if unbounded(node) && !guarded(ancestors, id086) {
                    out.push(violation(
                        &path,
                        "16.4 SR 14",
                        "unbounded quantifier without a restrictive path mode, a selective path pattern or DIFFERENT EDGES".into(),
                    ));
                }
            }
            "graph pattern" => {
                let keep = flat(children)
                    .into_iter()
                    .any(|c| def_name(c) == Some("keep clause"));
                let searched = path_patterns(node).into_iter().any(|pp| {
                    own(pp, "path pattern prefix")
                        .is_some_and(|p| contains(p, "path search prefix"))
                });
                if keep && searched {
                    out.push(violation(
                        &path,
                        "16.4 SR 6",
                        "a path pattern has its own search prefix next to a KEEP clause".into(),
                    ));
                }
            }
            "linear data-modifying statement" if !modifies(node) => {
                out.push(violation(
                    &path,
                    "13.1 SR 5",
                    "no INSERT, SET, REMOVE, DELETE or data-modifying CALL".into(),
                ));
            }
            _ => {}
        }
        ancestors.push(node);
    }
    children
        .iter()
        .for_each(|c| syntax_rules(c, id086, ancestors, out));
    if !synthetic {
        ancestors.pop();
    }
}

fn def_name(node: &Plain) -> Option<&str> {
    match node {
        Plain::Def { name, .. } => Some(name),
        _ => None,
    }
}

/// Children with desugaring groups flattened away.
fn flat(children: &[Plain]) -> Vec<&Plain> {
    let mut out = Vec::new();
    flatten(children, &mut out);
    out
}

/// The child of `node` that is a `<want>`.
fn own<'t>(node: &'t Plain, want: &str) -> Option<&'t Plain> {
    let Plain::Def { children, .. } = node else {
        return None;
    };
    flat(children)
        .into_iter()
        .find(|c| def_name(c) == Some(want))
}

fn contains(node: &Plain, want: &str) -> bool {
    let mut found = Vec::new();
    find(node, want, &mut found);
    !found.is_empty()
}

/// `*`, `+`, or `{m,}` with no upper bound.
fn unbounded(qpp: &Plain) -> bool {
    let Some(q) = own(qpp, "graph pattern quantifier") else {
        return false;
    };
    let Plain::Def { children, .. } = q else {
        return false;
    };
    match flat(children).first().and_then(|c| def_name(c)) {
        Some("asterisk" | "plus sign") => true,
        Some("general quantifier") => {
            own(q, "general quantifier").is_some_and(|g| !contains(g, "upper bound"))
        }
        _ => false,
    }
}

/// A prefix that is restrictive (TRAIL, SIMPLE, ACYCLIC) or selective (a search prefix other
/// than ALL).
fn prefix_guards(prefix: &Plain) -> bool {
    let mut modes = Vec::new();
    find(prefix, "path mode", &mut modes);
    let restrictive = modes
        .iter()
        .any(|m| matches!(m.text().as_str(), "TRAIL" | "SIMPLE" | "ACYCLIC"));
    let mut searches = Vec::new();
    find(prefix, "path search prefix", &mut searches);
    let selective = searches.iter().any(|s| own(s, "all path search").is_none());
    restrictive || selective
}

/// 16.4 SR 14, from the quantified path primary's ancestors up to its graph pattern.
fn guarded(ancestors: &[&Plain], id086: MatchModeDefault) -> bool {
    for a in ancestors.iter().rev() {
        match def_name(a) {
            // SR 7 puts a path pattern's prefix in parentheses around its expression.
            Some("parenthesized path pattern expression") => {
                if own(a, "path mode prefix").is_some_and(prefix_guards) {
                    return true;
                }
            }
            Some("path pattern") => {
                if own(a, "path pattern prefix").is_some_and(prefix_guards) {
                    return true;
                }
            }
            Some("graph pattern") => {
                let keep = own(a, "keep clause").is_some_and(prefix_guards);
                let different = match own(a, "match mode") {
                    Some(mode) => contains(mode, "different edges match mode"),
                    None => id086 == MatchModeDefault::DifferentEdges,
                };
                return keep || different;
            }
            _ => {}
        }
    }
    false
}

/// The path patterns of a graph pattern's own path pattern list.
fn path_patterns(gp: &Plain) -> Vec<&Plain> {
    let Some(Plain::Def { children, .. }) = own(gp, "path pattern list") else {
        return Vec::new();
    };
    flat(children)
        .into_iter()
        .filter(|c| def_name(c) == Some("path pattern"))
        .collect()
}

/// 13.1 SR 5, read with 13.1's Function ("a linear composition of at least one <simple
/// data-modifying statement>"): an element of the statement's sequence is a simple
/// data-modifying statement, or a nested `{ ... }` data-modifying procedure whose own
/// statements satisfy this. So the search only follows statements, never subqueries.
fn modifies(statement: &Plain) -> bool {
    const FOLLOW: &[&str] = &[
        "simple linear data-accessing statement",
        "simple data-accessing statement",
        "ambient linear data-modifying statement",
        "ambient linear data-modifying statement body",
        "focused linear data-modifying statement",
        "focused linear data-modifying statement body",
        "focused nested data-modifying procedure specification",
        "nested data-modifying procedure specification",
        "data-modifying procedure specification",
        "procedure body",
        "statement block",
        "next statement",
        "statement",
        "linear data-modifying statement",
    ];
    let Plain::Def { children, .. } = statement else {
        return false;
    };
    flat(children)
        .into_iter()
        .any(|child| match def_name(child) {
            Some("simple data-modifying statement") => true,
            Some(name) if FOLLOW.contains(&name) => modifies(child),
            _ => false,
        })
}
