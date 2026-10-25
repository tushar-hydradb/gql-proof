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
pub mod graph_type;
pub mod scope;
pub mod types;

use crate::MatchModeDefault;
use crate::bnf::Ebnf;
use crate::features::Forbidden;
use crate::tokens::{EXCLUDED, Grammar};
use chrono::{NaiveDate, NaiveDateTime, NaiveTime};
use std::collections::HashSet;
use std::fmt;
use unicode_general_category::{GeneralCategory, get_general_category};

/// The rules the checker reports and no generator rule keeps: the gate alone keeps them out of
/// what is printed (a flagged tree is withheld), so a generated tree may break them. The
/// value-size limits under H2 (no automaton counts digits) and the graph type bodies of
/// 18.1-18.5 (every alias, label and name is spelled `a`, so a body's consistency is a matter of
/// which specifications sit together, not followed).
pub const GATE_ONLY: &[&str] = &[
    // The audit's `checked` rows (tools/inventory/audit.py requires each listed here).
    "14.12 SR 22",
    "16.4 SR 6 nested",
    "16.4 SR 14 nested",
    "7.1 SR 6",
    "9.2 SR 7",
    "20.8 SR 11 d",
    "13.3 SR 3",
    "14.2 SR 10",
    "14.11 SR 10",
    "16.6 SR 7",
    "16.5 SR 6",
    "16.8 SR 4",
    "18.9 SR 68",
    "21.2 SR 18",
    "21.2 SR 20",
    "21.3 SR 5",
    "18.1 SR 8",
    "18.1 SR 9",
    "18.1 SR 10",
    "18.1 SR 11",
    "18.1 SR 14",
    "18.1 SR 16",
    "18.2 SR 7",
    "18.3 SR 8",
    "18.3 SR 17",
    "18.3 SR 18",
    "18.5 SR 1",
];

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
    /// Check the static types of value expressions (`types`).
    types: bool,
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
            types: false,
        }
    }

    /// Also check that variables are referenced in scope and declared new.
    pub fn with_scope(mut self) -> Self {
        self.scope = true;
        self
    }

    /// Also check that value expressions are typed.
    pub fn with_types(mut self) -> Self {
        self.types = true;
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
        confusables(tree, &mut out);
        created_names(tree, &mut out);
        self.walk(tree, &mut Vec::new(), &mut out);
        if let Some(id086) = self.syntax_rules {
            syntax_rules(tree, id086, &mut Vec::new(), &mut out);
            out.extend(graph_type::check(tree));
        }
        if self.scope {
            out.extend(scope::check(tree));
        }
        if self.types {
            out.extend(types::check(tree));
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
            // 21.3 SR 18: a non-delimited identifier, a parameter name's extended one too.
            "regular identifier" | "extended identifier" => {
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
            one.is_some_and(|c| {
                !matches!(c, '\'' | '"' | '`' | '\\')
                    && !c.is_control()
                    && get_general_category(c) != GeneralCategory::Unassigned
            }),
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
                if unbounded(node) && guarded(ancestors, id086) && !guarded_everywhere(ancestors, id086) {
                    out.push(violation(
                        &path,
                        "16.4 SR 14 nested",
                        "an unbounded quantifier in a nested graph pattern not guarded for an enclosing one".into(),
                    ));
                }
                if unbounded(node) && !guarded(ancestors, id086) {
                    out.push(violation(
                        &path,
                        "16.4 SR 14",
                        "unbounded quantifier without a restrictive path mode, a selective path pattern or DIFFERENT EDGES".into(),
                    ));
                }
                if length_zero(node) {
                    out.push(violation(
                        &path,
                        "16.7 SR 8",
                        "a quantified primary of minimum path length 0".into(),
                    ));
                }
                if nests_quantifier(node) {
                    out.push(violation(
                        &path,
                        "16.7 SR 9",
                        "a quantified primary directly under a quantified primary".into(),
                    ));
                }
            }
            "fixed quantifier" if bound_value(node) == 0 => {
                out.push(violation(
                    &path,
                    "16.11 SR 3",
                    "a fixed quantifier of 0, an upper bound of 0".into(),
                ));
            }
            "questioned path primary" | "simplified questioned" if length_zero(node) => {
                out.push(violation(
                    &path,
                    "16.7 SR 8",
                    "a questioned primary of minimum path length 0".into(),
                ));
            }
            "path pattern" => {
                if let Some(e) = own(node, "path pattern expression")
                    && minimums(e).nodes == 0
                {
                    out.push(violation(
                        &path,
                        "16.7 SR 16",
                        "the path pattern can match no node".into(),
                    ));
                }
            }
            "parenthesized path pattern expression" => {
                if own(node, "subpath variable declaration").is_some()
                    && let Some(e) = own(node, "path pattern expression")
                    && minimums(e).nodes == 0
                {
                    out.push(violation(
                        &path,
                        "16.7 SR 20",
                        "the named subpath can match no node".into(),
                    ));
                }
            }
            "upper bound" if bound_value(node) == 0 => {
                out.push(violation(&path, "16.11 SR 3", "an upper bound of 0".into()));
            }
            // 18.9 SR 7, 10, 13, 21: a max length is at least 1 and at or above the min
            // length, a fixed length at least 1.
            "character string type" | "byte string type" => {
                let min = own(node, "min length").map(integer_value);
                let max = own(node, "max length").map(integer_value);
                if max == Some(0) {
                    out.push(violation(&path, "18.9 SR 7", "a max length of 0".into()));
                }
                if own(node, "fixed length").map(integer_value) == Some(0) {
                    out.push(violation(&path, "18.9 SR 10", "a fixed length of 0".into()));
                }
                if let (Some(min), Some(max)) = (min, max)
                    && min > max
                {
                    let rule = if name == "character string type" {
                        "18.9 SR 13"
                    } else {
                        "18.9 SR 21"
                    };
                    out.push(violation(
                        &path,
                        rule,
                        "the min length is above the max length".into(),
                    ));
                }
            }
            "list value type" if own(node, "max length").map(integer_value) == Some(0) => {
                out.push(violation(&path, "18.9 SR 7", "a max length of 0".into()));
            }
            // 18.9 SR 29, 38, 40: a precision is at least 1 (2 in an approximate numeric
            // type), and a scale is at most the precision of its exact numeric type.
            "decimal exact numeric type"
            | "signed binary exact numeric type"
            | "unsigned binary exact numeric type"
            | "verbose binary exact numeric type"
            | "approximate numeric type" => {
                let precision = own(node, "precision").map(integer_value);
                let scale = own(node, "scale").map(integer_value);
                let approximate = name == "approximate numeric type";
                match precision {
                    Some(0) => {
                        out.push(violation(&path, "18.9 SR 29", "a precision of 0".into()));
                    }
                    Some(1) if approximate => out.push(violation(
                        &path,
                        "18.9 SR 40",
                        "an approximate numeric type of precision 1".into(),
                    )),
                    _ => {}
                }
                if !approximate
                    && let (Some(p), Some(s)) = (precision, scale)
                    && s > p
                {
                    out.push(violation(
                        &path,
                        "18.9 SR 38",
                        "the scale is above the precision".into(),
                    ));
                }
            }
            // 20.24 SR 3 b i 1 (byte strings by the reading in `refine::TrimOperands`): FROM
            // in a TRIM follows a specification or a trim string.
            "trim operands" | "byte string trim operands" => {
                let from = flat(children)
                    .iter()
                    .any(|c| matches!(c, Plain::Kw(k) if k.eq_ignore_ascii_case("FROM")));
                let has = ["trim specification", "trim character string", "trim byte string"]
                    .iter()
                    .any(|w| own(node, w).is_some());
                if from && !has {
                    out.push(violation(
                        &path,
                        "20.24 SR 3",
                        "FROM with neither a trim specification nor a trim string".into(),
                    ));
                }
            }
            // 21.3 SR 4: a delimited identifier is not empty. (A guard, so that a non-empty one
            // goes on to the 21.3 SR 5 arm below.)
            "delimited identifier"
                if !contains(node, "double quoted character representation")
                    && !contains(node, "accent quoted character representation") =>
            {
                out.push(violation(
                    &path,
                    "21.3 SR 4",
                    "an empty delimited identifier".into(),
                ));
            }
            // 16.11 SR 3 a ii: the lower bound is at most the upper.
            "general quantifier" => {
                if let Some(l) = own(node, "lower bound")
                    && let Some(u) = own(node, "upper bound")
                    && bound_value(u) < bound_value(l)
                {
                    out.push(violation(
                        &path,
                        "16.11 SR 3 a ii",
                        "the upper bound is below the lower".into(),
                    ));
                }
            }
            "simplified negation"
                if complex(node) || contains(node, "simplified direction override") =>
            {
                out.push(violation(
                    &path,
                    "16.12 SR 1",
                    "a concatenation, quantifier, ?, alternation or direction override in a negation".into(),
                ));
            }
            "simplified direction override" => {
                if children
                    .iter()
                    .any(|c| contains(c, "simplified direction override"))
                {
                    out.push(violation(
                        &path,
                        "16.12 SR 2",
                        "a direction override inside a direction override".into(),
                    ));
                }
                if complex(node) {
                    out.push(violation(
                        &path,
                        "16.12 SR 3",
                        "a concatenation, quantifier, ? or multiset alternation in a direction override".into(),
                    ));
                }
            }
            "simplified conjunction"
                if complex(node) || contains(node, "simplified direction override") =>
            {
                out.push(violation(
                    &path,
                    "16.12 SR 4",
                    "a concatenation, quantifier, ?, alternation or direction override in a conjunction".into(),
                ));
            }
            "graph pattern" => {
                let keep = flat(children)
                    .into_iter()
                    .any(|c| def_name(c) == Some("keep clause"));
                let searched = path_patterns(node).into_iter().any(|pp| {
                    own(pp, "path pattern prefix")
                        .is_some_and(|p| contains(p, "path search prefix"))
                });
                // 16.4 SR 6 with "contains" as written: a path pattern nested anywhere below.
                let mut all = Vec::new();
                find(node, "path pattern", &mut all);
                let nested_searched = all.iter().any(|pp| {
                    own(pp, "path pattern prefix").is_some_and(|p| contains(p, "path search prefix"))
                });
                if keep && nested_searched && !searched {
                    out.push(violation(
                        &path,
                        "16.4 SR 6 nested",
                        "a nested path pattern has a search prefix under a KEEP clause".into(),
                    ));
                }
                if keep && searched {
                    out.push(violation(
                        &path,
                        "16.4 SR 6",
                        "a path pattern has its own search prefix next to a KEEP clause".into(),
                    ));
                }
                // A missing mode may be DIFFERENT EDGES unless the default is known not to be
                // (the strict side for this rule, 16.4 SR 10).
                let different = match own(node, "match mode") {
                    Some(mode) => contains(mode, "different edges match mode"),
                    None => id086 != MatchModeDefault::RepeatableElements,
                };
                let patterns = path_patterns(node);
                let keep_selective = flat(children).into_iter().any(|c| {
                    def_name(c) == Some("keep clause")
                        && own(c, "path pattern prefix").is_some_and(|p| {
                            own(p, "path search prefix")
                                .is_some_and(|sp| own(sp, "all path search").is_none())
                        })
                });
                if different
                    && patterns.len() > 1
                    && (keep_selective || patterns.iter().any(|pp| selective(pp)))
                {
                    out.push(violation(
                        &path,
                        "16.4 SR 12",
                        "a selective path pattern beside another under DIFFERENT EDGES".into(),
                    ));
                }
            }
            // 18.2 SR 2, 3: in a closed node reference value type, no alias, key label set or
            // type name; with a type name, no key label set and no alias. "Simply contains":
            // without an intervening node type specification.
            "node type specification" => {
                let simply = |want: &str| simply_contains(node, want, name);
                let closed = ancestors
                    .last()
                    .is_some_and(|p| def_name(p) == Some("closed node reference value type"));
                if closed
                    && let Some(found) = ["local node type alias", "node type key label set", "node type name"]
                        .into_iter()
                        .find(|w| simply(w))
                {
                    out.push(violation(
                        &path,
                        "18.2 SR 2",
                        format!("a <{found}> in a closed node reference value type"),
                    ));
                }
                if simply("node type name") && (simply("node type key label set") || simply("local node type alias")) {
                    out.push(violation(
                        &path,
                        "18.2 SR 3",
                        "a named node type with a key label set or an alias".into(),
                    ));
                }
            }
            // 18.3 SR 2, 3, 4: in a closed edge reference value type, no key label set, type
            // name, endpoint alias, or key label set in an endpoint; with a type name, no key
            // label set; DIRECTED or UNDIRECTED matches the shape (reading in
            // `refine::ElementTypeShape`: a pattern with no edge kind is free).
            "edge type specification" => {
                let simply = |want: &str| simply_contains(node, want, name);
                let closed = ancestors
                    .last()
                    .is_some_and(|p| def_name(p) == Some("closed edge reference value type"));
                if closed
                    && let Some(found) = [
                        "edge type key label set",
                        "edge type name",
                        "source node type alias",
                        "destination node type alias",
                        "node type key label set",
                    ]
                    .into_iter()
                    .find(|w| simply(w))
                {
                    out.push(violation(
                        &path,
                        "18.3 SR 2",
                        format!("a <{found}> in a closed edge reference value type"),
                    ));
                }
                if simply("edge type name") && simply("edge type key label set") {
                    out.push(violation(
                        &path,
                        "18.3 SR 3",
                        "a named edge type with a key label set".into(),
                    ));
                }
                let mut kinds = Vec::new();
                find_simply(node, "edge kind", name, &mut kinds);
                let directed = kinds.iter().any(|k| k.text().eq_ignore_ascii_case("DIRECTED"));
                let undirected = kinds.iter().any(|k| k.text().eq_ignore_ascii_case("UNDIRECTED"));
                if directed && !simply("endpoint pair directed") && !simply("edge type pattern directed") {
                    out.push(violation(&path, "18.3 SR 4", "DIRECTED with an undirected shape".into()));
                }
                if undirected && !simply("endpoint pair undirected") && !simply("edge type pattern undirected") {
                    out.push(violation(&path, "18.3 SR 4", "UNDIRECTED with a directed shape".into()));
                }
            }
            // 20.16 SR 1 a, by the reading in `refine::IntegerCount`: TRIM's list count is
            // built of integer forms only.
            "trim list function" => {
                if let Some(count) = own(node, "numeric value expression")
                    && let Some(bad) = not_integer_shaped(count)
                {
                    out.push(violation(
                        &path,
                        "20.16 SR 1",
                        format!("<{bad}> in TRIM's list count, not an integer form"),
                    ));
                }
            }
            // 16.6 SR 2 b ii: a literal number of paths or groups is positive.
            "number of paths" | "number of groups" => {
                let mut ints = Vec::new();
                find(node, "unsigned integer", &mut ints);
                if ints.iter().any(|i| unsigned_integer_value(&i.text()) == 0) {
                    out.push(violation(
                        &path,
                        "16.6 SR 2",
                        "a number of paths or groups of 0".into(),
                    ));
                }
            }
            // 9.1 SR 5-7: what the statements of each kind of procedure specification are.
            // Its own statements are the ones it simply contains: those of its body's block,
            // not of a body nested in one of them. 9.1 SR 4 classifies a <procedure
            // specification> by what its body contains; with SR 5-7 on the kind the tree
            // gives it, a mismatch is reported here.
            "catalog-modifying procedure specification"
            | "data-modifying procedure specification"
            | "query specification" => {
                let kinds: Vec<&str> = own_statements(node)
                    .iter()
                    .filter_map(|st| inner(st).and_then(def_name))
                    .collect();
                let catalog = kinds.iter().filter(|k| **k == "linear catalog-modifying statement").count();
                let data = kinds.iter().filter(|k| **k == "linear data-modifying statement").count();
                let (rule, bad) = match name.as_str() {
                    "catalog-modifying procedure specification" => ("9.1 SR 5", catalog != kinds.len()),
                    "data-modifying procedure specification" => ("9.1 SR 6", catalog > 0 || data == 0),
                    _ => ("9.1 SR 7", catalog > 0 || data > 0),
                };
                if bad {
                    out.push(violation(
                        &path,
                        rule,
                        format!("a <{name}> whose statements are {kinds:?}"),
                    ));
                }
            }
            // 12.8 SR 2, 13.6 SR 2, 14.5 SR 2: an inline call's procedure has the kind of the
            // statement that calls it.
            "call catalog-modifying procedure statement"
            | "call data-modifying procedure statement"
            | "call query statement" => {
                let (rule, want) = match name.as_str() {
                    "call catalog-modifying procedure statement" => {
                        ("12.8 SR 2", "catalog-modifying procedure specification")
                    }
                    "call data-modifying procedure statement" => {
                        ("13.6 SR 2", "data-modifying procedure specification")
                    }
                    _ => ("14.5 SR 2", "query specification"),
                };
                let mut specs = Vec::new();
                find(node, "procedure specification", &mut specs);
                if let Some(ps) = specs.first()
                    && inner(ps).and_then(def_name) != Some(want)
                {
                    out.push(violation(
                        &path,
                        rule,
                        format!("the inline procedure is not a <{want}>"),
                    ));
                }
            }
            // 9.2 SR 4-7 over the statements a block directly contains.
            "statement block" => {
                let statements = own_block_statements(node);
                let catalog = statements.iter().any(|st| {
                    inner(st).and_then(def_name) == Some("linear catalog-modifying statement")
                });
                if catalog && statements.len() > 1 {
                    out.push(violation(
                        &path,
                        "9.2 SR 4",
                        "a catalog-modifying statement beside another statement".into(),
                    ));
                }
                let mut direct = Vec::new();
                for st in &statements {
                    find_directly(
                        st,
                        &[
                            "focused linear query statement",
                            "ambient linear query statement",
                            "focused linear data-modifying statement",
                            "ambient linear data-modifying statement",
                            "linear query statement",
                        ],
                        &mut direct,
                    );
                }
                // 14.12 SR 1, 27: a SELECT is judged as its replacement, which is ambient.
                let is_select = |d: &&Plain| inner(d).and_then(def_name) == Some("select statement");
                let has = |n: &str| direct.iter().any(|d| def_name(d) == Some(n));
                let focused = direct.iter().any(|d| {
                    (def_name(d) == Some("focused linear query statement") && !is_select(d))
                        || def_name(d) == Some("focused linear data-modifying statement")
                });
                let ambient = has("ambient linear query statement")
                    || has("ambient linear data-modifying statement")
                    || direct.iter().any(|d| def_name(d) == Some("focused linear query statement") && is_select(d));
                if focused && ambient {
                    out.push(violation(
                        &path,
                        "9.2 SR 5",
                        "focused and ambient statements in one block".into(),
                    ));
                }
                let queries: Vec<&&Plain> = direct
                    .iter()
                    .filter(|d| def_name(d) == Some("linear query statement"))
                    .collect();
                let select = |q: &Plain| {
                    inner(q).and_then(inner).and_then(def_name) == Some("select statement")
                };
                if queries.iter().any(|q| select(q)) && !queries.iter().all(|q| select(q)) {
                    out.push(violation(
                        &path,
                        "9.2 SR 6",
                        "a SELECT beside another linear query statement".into(),
                    ));
                }
                // Judged on the replacements: a SELECT is a RETURN (14.12 SR 27 a), an EXISTS
                // over a pattern holds a RETURN (19.4 SR 2, 3).
                let results = |q: &Plain| {
                    contains(q, "primitive result statement")
                        || contains(q, "select statement")
                        || contains(q, "exists predicate")
                };
                if queries.iter().any(|q| results(q)) && !queries.iter().all(|q| results(q)) {
                    out.push(violation(
                        &path,
                        "9.2 SR 7",
                        "a linear query statement with a result statement beside one without".into(),
                    ));
                }
            }
            // 14.2 SR 3, 4: one conjunction, and focused or ambient operands, per composite
            // query expression; the ones it directly contains are along its left spine.
            "composite query expression" if own(node, "query conjunction").is_some() => {
                let mut conjunctions = Vec::new();
                let mut operands = Vec::new();
                let mut at = node;
                loop {
                    if let Some(qc) = own(at, "query conjunction") {
                        conjunctions.push(conjunction(qc));
                    }
                    if let Some(cqp) = own(at, "composite query primary") {
                        operands.push(cqp);
                    }
                    match own(at, "composite query expression") {
                        Some(next) => at = next,
                        None => break,
                    }
                }
                if conjunctions.windows(2).any(|w| w[0] != w[1]) {
                    out.push(violation(
                        &path,
                        "14.2 SR 3",
                        format!("mixed query conjunctions {conjunctions:?}"),
                    ));
                }
                let mut direct = Vec::new();
                for op in operands {
                    find_directly(
                        op,
                        &["focused linear query statement", "ambient linear query statement"],
                        &mut direct,
                    );
                }
                let is_select = |d: &&Plain| inner(d).and_then(def_name) == Some("select statement");
                let focused = direct
                    .iter()
                    .any(|d| def_name(d) == Some("focused linear query statement") && !is_select(d));
                let ambient = direct.iter().any(|d| {
                    def_name(d) == Some("ambient linear query statement")
                        || (def_name(d) == Some("focused linear query statement") && is_select(d))
                });
                if focused && ambient {
                    out.push(violation(
                        &path,
                        "14.2 SR 4",
                        "focused and ambient operands in one composite query".into(),
                    ));
                }
            }
            // 14.12 SR 26 b ii: a FROM's nested query is ambient after a graph expression,
            // focused without one.
            "select query specification" => {
                let graph = own(node, "graph expression").is_some();
                if let Some(nqs) = own(node, "nested query specification") {
                    let mut found = Vec::new();
                    find_simply(nqs, "focused linear query statement", "nested query specification", &mut found);
                    let focused = !found.is_empty();
                    found.clear();
                    find_simply(nqs, "ambient linear query statement", "nested query specification", &mut found);
                    let ambient = !found.is_empty();
                    if (graph && !ambient) || (!graph && !focused) {
                        out.push(violation(
                            &path,
                            "14.12 SR 26",
                            if graph {
                                "a FROM with a graph expression over a nested query with no ambient statement".into()
                            } else {
                                "a FROM with no graph expression over a nested query with no focused statement".into()
                            },
                        ));
                    }
                }
            }
            // 17.6 SR 1: after a bare `/` schema reference no solidus, after any other one a
            // solidus (`//` is no parent reference).
            "catalog object parent reference" => {
                let kids = flat(children);
                let schema = kids.iter().find(|k| def_name(k) == Some("schema reference"));
                let solidus = kids.iter().any(|k| def_name(k) == Some("solidus"));
                // Reading in `refine::ParentSolidus`: with no schema reference, "otherwise"
                // asks for a solidus that cannot be there.
                if schema.is_none() {
                    out.push(violation(
                        &path,
                        "17.6 SR 1",
                        "a parent reference with no schema reference (reading)".into(),
                    ));
                }
                if let Some(sr) = schema {
                    let bare = sr.text() == "/";
                    if bare == solidus {
                        out.push(violation(
                            &path,
                            "17.6 SR 1",
                            if bare {
                                "a solidus after the bare / schema reference".into()
                            } else {
                                "no solidus after the schema reference".into()
                            },
                        ));
                    }
                }
            }
            // 21.3 SR 5 b-d: an identifier's representative form is at most 16383 characters,
            // with no Cc, Cf, Cn, Cs, Zl, Zp, and no Zs but the space.
            "regular identifier" | "extended identifier" | "delimited identifier" => {
                let text = node.text();
                let form: String = if name == "delimited identifier" && text.len() >= 2 {
                    let q = text.chars().next().unwrap();
                    let inner = &text[q.len_utf8()..text.len() - q.len_utf8()];
                    inner.replace(&format!("{q}{q}"), &q.to_string())
                } else {
                    text.clone()
                };
                if form.chars().count() > 16383 {
                    out.push(violation(&path, "21.3 SR 5", "an identifier over 16383 characters".into()));
                }
                use GeneralCategory as G;
                if let Some(c) = form.chars().find(|&c| {
                    let g = get_general_category(c);
                    matches!(
                        g,
                        G::Control | G::Format | G::Unassigned | G::Surrogate | G::LineSeparator | G::ParagraphSeparator
                    ) || (g == G::SpaceSeparator && c != ' ')
                }) {
                    out.push(violation(
                        &path,
                        "21.3 SR 5",
                        format!("{c:?} in an identifier"),
                    ));
                }
            }
            // 21.2 SR 18, 20 under hypothesis H2: the implementation's exact types reach 18
            // decimal digits and its approximate literal type the range of a 32 bit float. A
            // literal past that is reported (reading).
            "exact numeric literal" => {
                let t = ascii_digits(&node.text()).to_ascii_uppercase().replace('_', "");
                let radix = t.len() > 1 && t.starts_with('0') && matches!(t.as_bytes()[1], b'X' | b'O' | b'B');
                let t = if radix { t.as_str() } else { t.trim_end_matches('M') };
                let (mantissa, exp) = match t.split_once('E').filter(|_| !radix) {
                    Some((m, e)) => (m.to_string(), e.parse::<i64>().unwrap_or(i64::MAX)),
                    None => (t.to_string(), 0),
                };
                let digits = mantissa.chars().filter(|c| c.is_ascii_digit()).count() as i64;
                let fraction = mantissa.split_once('.').map_or(0, |(_, f)| f.len() as i64);
                let integer_part = digits - fraction;
                let too_big = if radix {
                    unsigned_integer_value(t) >= 1_000_000_000_000_000_000
                } else {
                    digits > 18 || exp.abs() > 18 || integer_part + exp > 18 || fraction - exp > 18
                };
                if too_big {
                    out.push(violation(
                        &path,
                        "21.2 SR 18",
                        format!("no exact numeric type of 18 digits holds {} (reading, H2)", node.text()),
                    ));
                }
            }
            "approximate numeric literal" => {
                let t = ascii_digits(&node.text()).to_ascii_uppercase().replace('_', "");
                let t = t.trim_end_matches(['F', 'D']);
                let v: Option<f64> = t.parse().ok();
                if !v.is_some_and(|v| v.is_finite() && (v == 0.0 || (1.2e-38..=3.4e38).contains(&v.abs()))) {
                    out.push(violation(
                        &path,
                        "21.2 SR 20",
                        format!("{} is outside a 32 bit float's range (reading, H2)", node.text()),
                    ));
                }
            }
            // 18.10 SR 2: field names in one field type list are distinct.
            "field type list" => {
                let mut names = std::collections::BTreeSet::new();
                // Simply contained: a field's record type is a list of its own.
                let mut fts = Vec::new();
                find_simply(node, "field type", "field type list", &mut fts);
                for ft in fts {
                    if let Some(fname) = own(ft, "field name")
                        && !names.insert(fname.text())
                    {
                        out.push(violation(
                            &path,
                            "18.10 SR 2",
                            format!("field {} declared twice", fname.text()),
                        ));
                    }
                }
            }
            // 18.7 SR 4 by the reading in `refine::PropertyValueTypes` (H2): a property value
            // type is a predefined type, neither a reference nor an immaterial one. The types
            // checker reports the same on the type itself.
            "property value type" => {
                let ok = own(node, "value type")
                    .and_then(|vt| inner(vt))
                    .filter(|p| def_name(p) == Some("predefined type"))
                    .and_then(inner)
                    .and_then(def_name)
                    .is_some_and(|d| !matches!(d, "reference value type" | "immaterial value type"));
                if !ok {
                    out.push(violation(
                        &path,
                        "18.7 SR 4",
                        "not a predefined material non-reference type (reading, H2)".into(),
                    ));
                }
            }
            // 10.1 SR 8, 10.2 SR 8 by the reading in `refine::ClosedInitializerTypes`: no
            // closed declared graph type, no declared binding table type (always closed).
            "opt typed binding table initializer"
                if own(node, "binding table reference value type").is_some() =>
            {
                out.push(violation(
                    &path,
                    "10.2 SR 8",
                    "a declared binding table type, closed (reading)".into(),
                ));
            }
            "opt typed graph initializer"
                if own(node, "graph reference value type")
                    .is_some_and(|g| own(g, "closed graph reference value type").is_some()) =>
            {
                out.push(violation(
                    &path,
                    "10.1 SR 8",
                    "a declared closed graph type (reading)".into(),
                ));
            }
            // 18.9 SR 88: a union's components agree on nullability (SR 4: a <not null>
            // without an intervening <value type>).
            "component type list" => {
                let mut types = Vec::new();
                find_simply(node, "value type", "value type", &mut types);
                // SR 4 a, b: a <not null> without an intervening value type, or NOTHING.
                let nn = |vt: &Plain| {
                    let mut nots = Vec::new();
                    find_simply(vt, "not null", "value type", &mut nots);
                    find_simply(vt, "empty type", "value type", &mut nots);
                    !nots.is_empty()
                };
                let known: Vec<bool> = types.iter().map(|t| nn(t)).collect();
                if known.iter().any(|b| *b) && known.iter().any(|b| !*b) {
                    out.push(violation(
                        &path,
                        "18.9 SR 88",
                        "components both known not nullable and possibly nullable".into(),
                    ));
                }
            }
            // 21.2 SR 73, 75: the elements of a list literal and the field values of a record
            // literal conform to the Format of <literal>: a signed number, a general literal,
            // or a list or record of such (judged on the tree, H3).
            "list literal" | "record literal" => {
                let want = if name == "list literal" { "list element" } else { "field" };
                let mut items = Vec::new();
                find(node, want, &mut items);
                if let Some(bad) = items.iter().find(|i| {
                    own(i, "value expression").is_some_and(|ve| !literal_shaped(ve))
                }) {
                    let rule = if name == "list literal" { "21.2 SR 73" } else { "21.2 SR 75" };
                    out.push(violation(
                        &path,
                        rule,
                        format!("{} is not a literal", bad.text()),
                    ));
                }
            }
            // 14.12 SR 27 b (reading in `refine::NoSelectBody`): a SELECT with a FROM is
            // judged as its replacement, which the checker does not build.
            "select statement" if own(node, "select statement body").is_some() => {
                out.push(violation(
                    &path,
                    "14.12 SR 27",
                    "a SELECT with a FROM: its replacement is not modelled (reading)".into(),
                ));
            }
            // 14.12 SR 16, 21, 27 b: a HAVING needs an aggregating select item.
            "select statement" if own(node, "having clause").is_some() => {
                let mut aggs = Vec::new();
                if let Some(list) = own(node, "select item list") {
                    find_directly(list, &["aggregate function"], &mut aggs);
                }
                if aggs.is_empty() {
                    out.push(violation(
                        &path,
                        "14.12 SR 27",
                        "a HAVING with no aggregating select item: its replacement filters on an undeclared name".into(),
                    ));
                }
            }
            // 10.1 SR 8, 7.1 SR 6 c i (4.17.4.2 reading): no NOT NULL declared graph type.
            "opt typed graph initializer"
                if own(node, "graph reference value type").is_some_and(|g| contains(g, "not null")) =>
            {
                out.push(violation(
                    &path,
                    "10.1 SR 8",
                    "a NOT NULL declared graph type: no value is known not nullable (reading)".into(),
                ));
            }
            // 22.1 SR 3: a `$$` reference's validity is the substituted text's, which no
            // sentence holds: outside the claim, reported.
            "substituted parameter reference" => {
                out.push(violation(
                    &path,
                    "22.1 SR 3",
                    "a substituted parameter: its validity depends on text outside the sentence".into(),
                ));
            }
            // 16.7 SR 10 then 20: each multiset alternation operand becomes a named subpath,
            // which matches a node.
            "path multiset alternation" if minimums(node).nodes == 0 => {
                out.push(violation(
                    &path,
                    "16.7 SR 20",
                    "a multiset alternation operand that can match no node (a named subpath by 16.7 SR 10)".into(),
                ));
            }
            "simplified multiset alternation"
                if matches!(simplified(node), Factor::Other(m) if m.nodes == 0) =>
            {
                out.push(violation(
                    &path,
                    "16.7 SR 20",
                    "a multiset alternation operand that can match no node (a named subpath by 16.7 SR 10)".into(),
                ));
            }
            // 20.7 SR 2 g, 19.8-19.10 SR 2 (reading in `refine::NoElementWhen`): an element
            // predicate as a when operand needs the case operand to be a singleton element
            // variable reference; none is generated, one is reported.
            "when operand"
                if flat(children).iter().any(|c| def_name(c).is_some_and(|d| {
                    matches!(
                        d,
                        "directed predicate part 2"
                            | "labeled predicate part 2"
                            | "source predicate part 2"
                            | "destination predicate part 2"
                    )
                })) =>
            {
                out.push(violation(
                    &path,
                    "20.7 SR 2",
                    "an element predicate as a when operand (reading)".into(),
                ));
            }
            // 12.4 SR 3, 12.5 SR 2, 12.6 SR 2, 12.7 SR 2: a CREATE or DROP parent identifies a
            // schema, which a parent with an object name never does.
            "create graph statement" | "drop graph statement" | "create graph type statement" | "drop graph type statement" => {
                // The parent of the name the statement makes or drops, not of a graph it copies.
                let pan = own(node, "catalog graph parent and name")
                    .or_else(|| own(node, "catalog graph type parent and name"));
                let parent = pan.and_then(|p| own(p, "catalog object parent reference"));
                if parent.is_some_and(|p| flat(match p { Plain::Def { children, .. } => children, _ => unreachable!() }).iter().any(|c| def_name(c) == Some("object name"))) {
                    let rule = match name.as_str() {
                        "create graph statement" => "12.4 SR 3",
                        "drop graph statement" => "12.5 SR 2",
                        "create graph type statement" => "12.6 SR 2",
                        _ => "12.7 SR 2",
                    };
                    out.push(violation(
                        &path,
                        rule,
                        "a parent with an object name identifies no schema".into(),
                    ));
                }
            }
            // 8.2 SR 2: exactly one access mode.
            "transaction characteristics" => {
                let mut modes = Vec::new();
                find(node, "transaction access mode", &mut modes);
                if modes.len() != 1 {
                    out.push(violation(
                        &path,
                        "8.2 SR 2",
                        format!("{} transaction access modes, not one", modes.len()),
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

/// The first node below a TRIM list count (20.16 SR 1, the reading in `refine::IntegerCount`)
/// that is not an integer form: an <unsigned integer>, a dynamic parameter, a length or
/// cardinality expression, and signs, parentheses, `+`, `-`, `*` over them.
fn not_integer_shaped(node: &Plain) -> Option<String> {
    let Plain::Def { name, children, .. } = node else {
        return None;
    };
    let kids = flat(children);
    let defs: Vec<&str> = kids.iter().filter_map(|k| def_name(k)).collect();
    let tokens: Vec<String> = kids
        .iter()
        .filter(|k| matches!(k, Plain::Kw(_) | Plain::Term(_)))
        .map(|k| k.text())
        .collect();
    let ok = match name.as_str() {
        "unsigned integer" | "length expression" | "cardinality expression"
        | "dynamic parameter specification" => return None,
        "numeric value expression" | "factor" | "numeric primary" | "value expression primary"
        | "parenthesized value expression" | "sign" | "plus sign" | "minus sign" | "asterisk"
        | "left paren" | "right paren" => true,
        "term" => !defs.contains(&"solidus") && !tokens.iter().any(|t| t == "/"),
        "value expression" => defs == ["common value expression"],
        "common value expression" => defs == ["numeric value expression"],
        "numeric value function" => {
            defs == ["length expression"] || defs == ["cardinality expression"]
        }
        "non-parenthesized value expression primary" => {
            defs == ["non-parenthesized value expression primary special case"]
        }
        "non-parenthesized value expression primary special case" => {
            defs == ["unsigned value specification"]
        }
        "unsigned value specification" => {
            defs == ["unsigned literal"] || defs == ["general value specification"]
        }
        "general value specification" => defs == ["dynamic parameter specification"],
        "unsigned literal" => defs == ["unsigned numeric literal"],
        "unsigned numeric literal" => defs == ["exact numeric literal"],
        "exact numeric literal" => defs == ["unsigned integer"] && tokens.is_empty(),
        _ => false,
    };
    if !ok {
        return Some(name.clone());
    }
    kids.into_iter().find_map(not_integer_shaped)
}

/// Whether a value expression's tree is a literal's (21.2 SR 73, 75): a chain of one-child
/// wrappers down to an <unsigned literal>, a sign on an <unsigned numeric literal>, or a list or
/// record constructor whose elements are literal-shaped themselves.
fn literal_shaped(node: &Plain) -> bool {
    let Some(n) = def_name(node) else { return false };
    let Plain::Def { children, .. } = node else { return false };
    let kids = flat(children);
    let defs: Vec<&&Plain> = kids.iter().filter(|k| matches!(k, Plain::Def { .. })).collect();
    match n {
        "unsigned literal" | "unsigned numeric literal" | "general literal" => true,
        "list value constructor" | "list value constructor by enumeration" | "record constructor"
        | "fields specification" | "field list" | "list element list" => {
            let mut items = Vec::new();
            find(node, "list element", &mut items);
            find(node, "field", &mut items);
            items
                .iter()
                .all(|i| own(i, "value expression").is_none_or(literal_shaped))
        }
        // A sign on a number: <factor> ::= [ <sign> ] <numeric primary>.
        "factor" => {
            let tokens_ok = kids.iter().all(|k| matches!(k, Plain::Def { .. }));
            tokens_ok
                && defs.iter().all(|d| {
                    def_name(d) == Some("sign") || literal_shaped(d)
                })
        }
        "sign" => true,
        _ => {
            // A wrapper: one definition and nothing else.
            kids.len() == 1 && defs.len() == 1 && literal_shaped(defs[0])
        }
    }
}

/// The <statement>s a procedure specification simply contains: those of its body's
/// statement block.
fn own_statements(spec: &Plain) -> Vec<&Plain> {
    let mut bodies = Vec::new();
    find(spec, "procedure body", &mut bodies);
    bodies
        .first()
        .and_then(|pb| own(pb, "statement block"))
        .map(own_block_statements)
        .unwrap_or_default()
}

/// The <statement>s a statement block directly contains: its first and each NEXT's.
fn own_block_statements(sb: &Plain) -> Vec<&Plain> {
    let mut out: Vec<&Plain> = own(sb, "statement").into_iter().collect();
    let Plain::Def { children, .. } = sb else { return out };
    for next in flat(children) {
        if def_name(next) == Some("next statement")
            && let Some(st) = own(next, "statement")
        {
            out.push(st);
        }
    }
    out
}

/// Every node below `node` (itself included) named in `want`, not looking inside a
/// <procedure body>: what `node` directly contains.
fn find_directly<'t>(node: &'t Plain, want: &[&str], out: &mut Vec<&'t Plain>) {
    if let Some(n) = def_name(node) {
        if n == "procedure body" {
            return;
        }
        if want.contains(&n) {
            out.push(node);
        }
    }
    if let Plain::Def { children, .. } = node {
        for c in children {
            find_directly(c, want, out);
        }
    }
}

/// A query conjunction as 14.2 SR 1 normalises it: a set operator with its quantifier,
/// DISTINCT when none is given.
fn conjunction(qc: &Plain) -> String {
    fn tokens(node: &Plain, out: &mut Vec<String>) {
        match node {
            Plain::Def { children, .. } => children.iter().for_each(|c| tokens(c, out)),
            leaf => out.push(leaf.text().to_ascii_uppercase()),
        }
    }
    let mut words = Vec::new();
    tokens(qc, &mut words);
    let text = words.join(" ");
    match text.as_str() {
        "UNION" | "EXCEPT" | "INTERSECT" => format!("{text} DISTINCT"),
        _ => text,
    }
}

/// Whether `node` simply contains a `<want>`: contains one without an intervening `<boundary>`
/// (the standard's definition, `boundary` being `node`'s own definition).
fn simply_contains(node: &Plain, want: &str, boundary: &str) -> bool {
    let mut found = Vec::new();
    find_simply(node, want, boundary, &mut found);
    !found.is_empty()
}

/// Every `<want>` below `node` with no intervening `<boundary>`, outermost first.
fn find_simply<'t>(node: &'t Plain, want: &str, boundary: &str, out: &mut Vec<&'t Plain>) {
    let Plain::Def { children, .. } = node else { return };
    for child in children {
        match def_name(child) {
            Some(n) if n == want => out.push(child),
            Some(n) if n == boundary => {}
            _ => find_simply(child, want, boundary, out),
        }
    }
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
/// 16.4 SR 14 read with "contains" as written: guarded with respect to every enclosing graph
/// pattern, a nested one's included (a prefix guard on the way out counts for all of them; a
/// match mode only for its own pattern).
fn guarded_everywhere(ancestors: &[&Plain], id086: MatchModeDefault) -> bool {
    let mut prefix = false;
    // A KEEP prefix moves onto the path patterns of its own graph pattern only (16.4 SR 6).
    let mut innermost = true;
    for a in ancestors.iter().rev() {
        match def_name(a) {
            Some("parenthesized path pattern expression") => {
                prefix |= own(a, "path mode prefix").is_some_and(prefix_guards);
            }
            Some("path pattern") => {
                prefix |= own(a, "path pattern prefix").is_some_and(prefix_guards);
            }
            Some("graph pattern") => {
                let keep = innermost && own(a, "keep clause").is_some_and(prefix_guards);
                innermost = false;
                let different = match own(a, "match mode") {
                    Some(mode) => contains(mode, "different edges match mode"),
                    None => id086 == MatchModeDefault::DifferentEdges,
                };
                if !(prefix || keep || different) {
                    return false;
                }
            }
            _ => {}
        }
    }
    true
}

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

// --- 16.7 SR 7 and 15: minimum path length and minimum node count ---------------------
//
// Computed after 16.7 SR 14's transform (an edge pattern under a quantifier or `?` is
// parenthesized; a bare edge pattern in a path term gets an implicit node pattern on each
// side it has none) and 16.12 SR 5-6's rewrite of simplified expressions (a label, negation,
// conjunction or direction override is one edge pattern; a concatenation puts two edges in
// one term; a union or alternation one edge per operand; a quantifier or `?` applies to the
// parenthesized edge; `( contents )` is a parenthesized expression). Reading: a non-ASCII
// decimal digit in a bound counts as 1.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Min {
    nodes: u64,
    len: u64,
}

impl Min {
    fn times(self, k: u64) -> Min {
        Min {
            nodes: self.nodes.saturating_mul(k),
            len: self.len.saturating_mul(k),
        }
    }

    fn min(self, other: Min) -> Min {
        Min {
            nodes: self.nodes.min(other.nodes),
            len: self.len.min(other.len),
        }
    }
}

const ZERO: Min = Min { nodes: 0, len: 0 };

/// One factor of a path term, as SR 14 b-d and SR 15 c see it.
enum Factor {
    Node,
    Edge,
    Other(Min),
}

/// The minimums of a path term: SR 14 b-d insert a node pattern before a bare edge not
/// preceded by one and after a bare edge not followed by one, SR 15 c i counts two touching
/// node patterns once.
fn term(factors: &[Factor]) -> Min {
    let mut m = ZERO;
    let mut preceded_by_node = false;
    let mut prev_node_pattern = false;
    for (i, f) in factors.iter().enumerate() {
        match f {
            Factor::Node => {
                m.nodes += 1;
                if prev_node_pattern {
                    m.nodes -= 1;
                }
                preceded_by_node = true;
                prev_node_pattern = true;
            }
            Factor::Edge => {
                if !preceded_by_node {
                    m.nodes += 1;
                }
                m.len += 1;
                if !matches!(factors.get(i + 1), Some(Factor::Node)) {
                    m.nodes += 1;
                }
                preceded_by_node = true;
                prev_node_pattern = false;
            }
            Factor::Other(o) => {
                m.nodes += o.nodes;
                m.len += o.len;
                preceded_by_node = false;
                prev_node_pattern = false;
            }
        }
    }
    m
}

/// The first non-synthetic child that is a definition.
fn inner(node: &Plain) -> Option<&Plain> {
    let Plain::Def { children, .. } = node else {
        return None;
    };
    flat(children)
        .into_iter()
        .find(|c| matches!(c, Plain::Def { .. }))
}

/// The factors of a path term, its left-recursive concatenations flattened.
fn factors<'t>(node: &'t Plain, out: &mut Vec<&'t Plain>) {
    match def_name(node) {
        Some("path term") => {
            if let Some(c) = inner(node) {
                factors(c, out);
            }
        }
        Some("path concatenation") => {
            let Plain::Def { children, .. } = node else {
                return;
            };
            for c in flat(children) {
                factors(c, out);
            }
        }
        Some("path factor") => out.push(node),
        _ => {}
    }
}

/// A path factor as the term sees it.
fn factor(pf: &Plain) -> Factor {
    match inner(pf) {
        Some(p) if def_name(p) == Some("path primary") => factor_of_primary(p),
        Some(q) => Factor::Other(minimums(q)),
        None => Factor::Other(ZERO),
    }
}

/// A path primary as a factor: a node pattern, a bare edge pattern, or its minimums.
fn factor_of_primary(primary: &Plain) -> Factor {
    match inner(primary).and_then(|e| {
        if def_name(e) == Some("element pattern") {
            inner(e).and_then(def_name)
        } else {
            def_name(e)
        }
    }) {
        Some("node pattern") => Factor::Node,
        Some("edge pattern") => Factor::Edge,
        _ => Factor::Other(minimums(primary)),
    }
}

/// 16.7 SR 9: a quantified primary below this quantified node at the same depth of graph
/// pattern matching (not inside a WHERE or a filler, where a nested graph pattern starts
/// its own).
fn nests_quantifier(node: &Plain) -> bool {
    fn below(node: &Plain) -> bool {
        match node {
            Plain::Def { name, children, .. } => match name.as_str() {
                "quantified path primary" | "simplified quantified" => true,
                "graph pattern"
                | "element pattern filler"
                | "parenthesized path pattern where clause" => false,
                _ => children.iter().any(below),
            },
            _ => false,
        }
    }
    let Plain::Def { children, .. } = node else {
        return false;
    };
    children.iter().any(below)
}

/// 16.7 SR 8: what this quantified or questioned node repeats has minimum path length 0.
fn length_zero(node: &Plain) -> bool {
    match own(node, "path primary") {
        Some(p) => repeated(p).len == 0,
        None => own(node, "simplified tertiary").is_some_and(|t| term(&[simplified(t)]).len == 0),
    }
}

/// What a quantifier or `?` repeats: SR 14 a parenthesizes an edge pattern first.
fn repeated(primary: &Plain) -> Min {
    match factor_of_primary(primary) {
        Factor::Edge => term(&[Factor::Edge]),
        Factor::Node => term(&[Factor::Node]),
        Factor::Other(m) => m,
    }
}

/// Minimum path length and node count of a path node (SR 7, 15).
fn minimums(node: &Plain) -> Min {
    let Plain::Def { children, .. } = node else {
        return ZERO;
    };
    match def_name(node) {
        Some("node pattern") => Min { nodes: 1, len: 0 },
        Some("edge pattern") => Min { nodes: 0, len: 1 },
        Some("path term" | "path concatenation") => {
            let mut fs = Vec::new();
            factors(node, &mut fs);
            let fs: Vec<Factor> = fs.into_iter().map(factor).collect();
            term(&fs)
        }
        // A factor on its own is a term of one.
        Some("path factor") => term(&[factor(node)]),
        Some("path pattern union" | "path multiset alternation") => flat(children)
            .into_iter()
            .filter(|c| def_name(c) == Some("path term"))
            .map(minimums)
            .reduce(Min::min)
            .unwrap_or(ZERO),
        Some("quantified path primary") => {
            let p = own(node, "path primary").map_or(ZERO, repeated);
            p.times(lower_bound(own(node, "graph pattern quantifier")))
        }
        Some("questioned path primary") => ZERO,
        Some("parenthesized path pattern expression") => {
            own(node, "path pattern expression").map_or(ZERO, minimums)
        }
        // 16.12 SR 5: `( SPPE )`, whose term is the rewritten contents.
        Some("simplified path pattern expression") => inner(node)
            .and_then(|d| own(d, "simplified contents"))
            .map_or(ZERO, |c| term(&[simplified(c)])),
        // Wrappers: path pattern expression, path primary, element pattern.
        _ => inner(node).map_or(ZERO, minimums),
    }
}

/// A simplified node as a factor of the term its rewrite lands in (16.12 SR 6).
fn simplified(node: &Plain) -> Factor {
    let Plain::Def { children, .. } = node else {
        return Factor::Other(ZERO);
    };
    match def_name(node) {
        Some("simplified primary") => match own(node, "simplified contents") {
            // `( PREFIX INNER SUFFIX )`
            Some(c) => Factor::Other(term(&[simplified(c)])),
            None => Factor::Edge,
        },
        Some(
            "simplified negation" | "simplified conjunction" | "simplified direction override",
        ) => Factor::Edge,
        Some("simplified concatenation") => {
            let mut fs = Vec::new();
            simplified_factors(node, &mut fs);
            let fs: Vec<Factor> = fs.into_iter().map(simplified).collect();
            Factor::Other(term(&fs))
        }
        Some("simplified path union" | "simplified multiset alternation") => Factor::Other(
            flat(children)
                .into_iter()
                .filter(|c| def_name(c) == Some("simplified term"))
                .map(|t| term(&[simplified(t)]))
                .reduce(Min::min)
                .unwrap_or(ZERO),
        ),
        Some("simplified quantified") => {
            let m = own(node, "simplified tertiary").map_or(ZERO, |t| term(&[simplified(t)]));
            Factor::Other(m.times(lower_bound(own(node, "graph pattern quantifier"))))
        }
        Some("simplified questioned") => Factor::Other(ZERO),
        // Wrappers: contents, term, factor low, factor high, tertiary, secondary.
        _ => inner(node).map_or(Factor::Other(ZERO), simplified),
    }
}

/// The factor lows of a simplified term, its left-recursive concatenations flattened.
fn simplified_factors<'t>(node: &'t Plain, out: &mut Vec<&'t Plain>) {
    match def_name(node) {
        Some("simplified term") => {
            if let Some(c) = inner(node) {
                simplified_factors(c, out);
            }
        }
        Some("simplified concatenation") => {
            let Plain::Def { children, .. } = node else {
                return;
            };
            for c in flat(children) {
                simplified_factors(c, out);
            }
        }
        Some("simplified factor low") => out.push(node),
        _ => {}
    }
}

/// 16.11 SR 2: the lower bound a quantifier normalizes to.
fn lower_bound(q: Option<&Plain>) -> u64 {
    let Some(q) = q else {
        return 1;
    };
    match inner(q).map(|c| (def_name(c), c)) {
        Some((Some("asterisk"), _)) => 0,
        Some((Some("plus sign"), _)) => 1,
        Some((Some("fixed quantifier"), f)) => bound_value(f),
        Some((Some("general quantifier"), g)) => own(g, "lower bound").map_or(0, bound_value),
        _ => 1,
    }
}

/// The value of the <unsigned integer> under a bound, a missing integer as 0.
fn bound_value(node: &Plain) -> u64 {
    own(node, "unsigned integer").map_or(0, |n| unsigned_integer_value(&n.text()))
}

/// The value of a length, precision or scale: the integer its text spells.
fn integer_value(node: &Plain) -> u64 {
    unsigned_integer_value(&node.text())
}

/// The value an <unsigned integer> spells: decimal, or 0x, 0o, 0b prefixed, underscores
/// skipped, a digit of any script by `digit_value`.
pub fn unsigned_integer_value(text: &str) -> u64 {
    let lower = text.to_ascii_lowercase();
    let (digits, radix): (&str, u32) = match lower.as_bytes() {
        [b'0', b'x', ..] => (&lower[2..], 16),
        [b'0', b'o', ..] => (&lower[2..], 8),
        [b'0', b'b', ..] => (&lower[2..], 2),
        _ => (lower.as_str(), 10),
    };
    digits.chars().filter(|c| *c != '_').fold(0u64, |v, c| {
        let digit = c.to_digit(radix).or_else(|| digit_value(c)).unwrap_or(0);
        v.saturating_mul(u64::from(radix))
            .saturating_add(u64::from(digit))
    })
}

/// `text` with every decimal digit of another script (21.4 SR 2) read as its ASCII digit.
fn ascii_digits(text: &str) -> String {
    text.chars()
        .map(|c| match digit_value(c) {
            Some(v) if !c.is_ascii_digit() => char::from_digit(v, 10).unwrap_or(c),
            _ => c,
        })
        .collect()
}

/// The value of a decimal digit of any script (21.4 SR 2: general category Nd): Unicode's Nd
/// digits come in runs of ten in order, zero first (UAX #44), so a digit's value is its
/// distance from the start of the run of Nd characters it is in, modulo ten. `None` for a
/// character that is not a decimal digit.
pub fn digit_value(c: char) -> Option<u32> {
    if let Some(v) = c.to_digit(10) {
        return Some(v);
    }
    let decimal = |u: u32| {
        char::from_u32(u).is_some_and(|p| get_general_category(p) == GeneralCategory::DecimalNumber)
    };
    if !decimal(c as u32) {
        return None;
    }
    let mut start = c as u32;
    while start > 0 && decimal(start - 1) {
        start -= 1;
    }
    Some((c as u32 - start) % 10)
}

/// 16.12 SR 1, 3, 4: a concatenation, quantifier, `?` or multiset alternation below.
fn complex(node: &Plain) -> bool {
    [
        "simplified concatenation",
        "simplified quantified",
        "simplified questioned",
        "simplified multiset alternation",
    ]
    .iter()
    .any(|w| contains(node, w))
}

/// 16.6 SR 4: a path pattern with a search prefix other than ALL.
fn selective(pp: &Plain) -> bool {
    own(pp, "path pattern prefix").is_some_and(|prefix| {
        let mut searches = Vec::new();
        find(prefix, "path search prefix", &mut searches);
        searches.iter().any(|s| own(s, "all path search").is_none())
    })
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

/// 6 SR 4 under hypothesis H2: the implementation's relation of visually confusable names
/// (IW014) relates two different names only if they share a skeleton under the ASCII
/// confusables of UTS #39 (`rn`/`m`, `vv`/`w`, `cl`/`d`, `1`/`I`/`l`, `0`/`O`/`o`), compared
/// without case. Two different identifiers of one tree with one skeleton are reported.
fn confusables(tree: &Plain, out: &mut Vec<Violation>) {
    fn skeleton(name: &str) -> String {
        let mut s = name.to_lowercase();
        for (from, to) in [("rn", "m"), ("vv", "w"), ("cl", "d"), ("1", "l"), ("i", "l"), ("0", "o")] {
            s = s.replace(from, to);
        }
        s
    }
    // Regular and delimited identifiers alike: the representative form is what is compared.
    let mut ids = Vec::new();
    find(tree, "regular identifier", &mut ids);
    find(tree, "delimited identifier", &mut ids);
    let mut seen: std::collections::BTreeMap<String, String> = Default::default();
    for id in ids {
        let raw = id.text();
        let text = if def_name(id) == Some("delimited identifier") && raw.len() >= 2 {
            let q = raw.chars().next().unwrap();
            raw[q.len_utf8()..raw.len() - q.len_utf8()].replace(&format!("{q}{q}"), &q.to_string())
        } else {
            raw
        };
        let sk = skeleton(&text);
        match seen.get(&sk) {
            Some(other) if other.to_lowercase() != text.to_lowercase() => out.push(Violation {
                path: String::new(),
                rule: "6 SR 4",
                detail: format!("{other} and {text} are confusable (reading, H2)"),
            }),
            Some(_) => {}
            None => {
                seen.insert(sk, text);
            }
        }
    }
}

/// 12.2 SR 5, 12.4 SR 6, 12.6 SR 5 with H1: a name a CREATE makes (without IF NOT EXISTS or OR
/// REPLACE) names no existing object, while every other name the program uses names an existing
/// one (17.x); the same text in both places is met by no environment (a schema's graphs and
/// graph types share its names, reading).
fn created_names(tree: &Plain, out: &mut Vec<Violation>) {
    const NAMES: [&str; 5] = ["graph name", "graph type name", "binding table name", "procedure name", "schema name"];
    let mut all = Vec::new();
    for n in NAMES {
        find(tree, n, &mut all);
    }
    for (stmt, made, rule) in [
        ("create schema statement", "schema name", "12.2 SR 5"),
        ("create graph statement", "graph name", "12.4 SR 6"),
        ("create graph type statement", "graph type name", "12.6 SR 5"),
    ] {
        let mut stmts = Vec::new();
        find(tree, stmt, &mut stmts);
        for st in stmts {
            let kws: Vec<String> = flat(match st { Plain::Def { children, .. } => children, _ => continue })
                .iter()
                .filter(|k| matches!(k, Plain::Kw(_)))
                .map(|k| k.text().to_ascii_uppercase())
                .collect();
            if kws.iter().any(|k| k == "NOT" || k == "REPLACE") {
                continue;
            }
            let mut mades = Vec::new();
            find(st, made, &mut mades);
            let Some(m) = mades.first() else { continue };
            let text = m.text();
            if all.iter().any(|o| !std::ptr::eq(*o, *m) && o.text() == text) {
                out.push(Violation {
                    path: String::new(),
                    rule,
                    detail: format!("{text} is created and named elsewhere: it must and must not exist (H1)"),
                });
            }
        }
    }
}
