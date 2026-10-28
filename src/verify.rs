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
use std::collections::{HashMap, HashSet};
use std::fmt;
use unicode_general_category::{GeneralCategory, get_general_category};

/// The rules the checker reports and no generator rule keeps: the gate alone keeps them out of
/// what is printed (a flagged tree is withheld), so a generated tree may break them. The
/// value-size limits under H2 (no automaton counts digits) and the graph type bodies of
/// 18.1-18.5 (every alias, label and name is spelled `a`, so a body's consistency is a matter of
/// which specifications sit together, not followed).
pub const GATE_ONLY: &[&str] = &[
    // types::check's second pass, in the dynamic environment (H1 made a check)
    "H1 environment",
    // The audit's `checked` rows (tools/inventory/audit.py requires each listed here).
    "14.12 SR 22",
    "16.4 SR 6 nested",
    "16.4 SR 14 nested",
    "7.1 SR 6",
    "9.2 SR 7",
    "20.8 SR 11 d",
    "22.19 SR 2",
    "17.1 SR 2",
    "17.2 SR 2",
    "12.6 SR 7",
    "21.3 SR 4 names",
    "9.1 SR 5 nested",
    "16.6 SR 8 nested",
    "12.3 SR 7",
    "14.10 SR 4 let",
    "14.5 SR 3 kinds",
    "15.1 SR 9 yield",
    "16.7 SR 22 group",
    "withheld family",
    // a key label set omitted under a claim without GG22: the generator follows no claim's
    // graph type bodies this way; the gate does
    "18.2 SR 9",
    "18.3 SR 10",
    // the unknowns audit: a null source or two null list operands give no element type
    "14.8 SR 10 null",
    // the eighteenth review: H2's list cardinality, and H1 for a parameter in a combination
    "18.9 SR 73",
    "21.2 SR 14",
    "17.1 SR 6 at",
    "22.19 SR 2 unknown",
    "11.1 SR 3 material",
    "11.2 SR 4 material",
    "20.15 SR 2 null",
    // H2's limits, which the generator keeps by settling values (tree.rs); the gate makes them
    // rest on no generator
    "16.11 SR 1",
    "18.9 SR 17",
    "18.9 SR 25",
    "18.9 SR 32",
    "18.9 SR 42",
    // 20.8 SR 5's "CO specifies NULL" read as containing one anywhere: the generator does not
    // follow NULLs below a cast operand
    "20.8 SR 5 contains",
    // The category over a bare primary, on the printed tree: the generator loses a deferred
    // variable's narrowing when the variable is projected away at a RETURN (scope's view there
    // has no kind), so `MATCH ( x ) RETURN x` is accepted on the tree reading x as a number;
    // the gate keeps these out.
    "20.13 SR 2 primary",
    "20.21 SR 3 primary",
    "20.23 SR 2 primary",
    "20.23 SR 4 primary",
    "20.15 SR 1 primary",
    "20.20 SR 3 primary",
    "20.1 SR 4-6 primary",
    "20.28 SR 1 primary",
    // a computed or null value as a graph or binding table expression, on this tree: the
    // generator types MIN or MAX of a dynamic value dynamic, which such a site takes
    "11.1 SR 3 primary",
    "11.2 SR 4 primary",
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
    /// The claim lacks GG22, so no key label set may be omitted (18.2 SR 9 a ii, 18.3 SR 10 a
    /// ii; the seventeenth review).
    key_label_sets_required: bool,
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
            key_label_sets_required: false,
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
    /// Without GG22 every node and edge type specification has a key label set.
    pub fn with_key_label_sets_required(mut self, required: bool) -> Self {
        self.key_label_sets_required = required;
        self
    }

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
            catalog_root(tree, &mut out);
            if self.key_label_sets_required {
                for (spec, key, rule) in [
                    ("node type specification", "node type key label set", "18.2 SR 9"),
                    ("edge type specification", "edge type key label set", "18.3 SR 10"),
                ] {
                    let mut specs = Vec::new();
                    find(tree, spec, &mut specs);
                    if specs.iter().any(|s| !contains(s, key)) {
                        out.push(Violation {
                            path: String::new(),
                            rule,
                            detail: format!("a <{spec}> omits its key label set, and the claim lacks GG22"),
                        });
                    }
                }
            }
            like_sources(tree, &mut out);
            schema_drops(tree, &mut out);
            h2_bounds(tree, &mut out);
            procedure_kinds(tree, &mut out);
            procedure_yields(tree, &mut out);
            group_variables(tree, &mut out);
            unprinted_families(tree, &mut out);
            delimited_names(tree, &mut out);
            one_kind_per_name(tree, &mut out);
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
                // at least one field: `P` and `PT` alone match the productions (the twelfth
                // review), and a duration of no field is none
                if (self.chars_match("iso8601 years and months", &chars)
                    || self.chars_match("iso8601 days and time", &chars))
                    && chars.iter().any(|c| c.is_ascii_digit())
                {
                    Ok(())
                } else {
                    Err((
                        "21.2 SR 68",
                        format!("{content:?} is not an iso8601 duration"),
                    ))
                }
            }
            // the exact shape first: chrono skips spaces and takes one digit (the twelfth
            // review: `'2024-01- 1'` passed)
            "date string" => temporal(node, "21.2 SR 59", |c| {
                iso_shape(c, "dddd-dd-dd") && NaiveDate::parse_from_str(c, "%Y-%m-%d").is_ok()
            }),
            "time string" => temporal(node, "21.2 SR 62", |c| {
                iso_shape(c, "dd:dd:dd") && NaiveTime::parse_from_str(c, "%H:%M:%S%.f").is_ok()
            }),
            "datetime string" => temporal(node, "21.2 SR 64", |c| {
                iso_shape(c, "dddd-dd-ddTdd:dd:dd")
                    && NaiveDateTime::parse_from_str(c, "%Y-%m-%dT%H:%M:%S%.f").is_ok()
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
        // RFC 3986: a scheme (a letter, then letters, digits, + - .), a colon, something
        // after it (the twelfth review: `1:x` passed)
        "external object reference" => ok(
            text.split_once(':').is_some_and(|(scheme, rest)| {
                scheme.chars().next().is_some_and(|c| c.is_ascii_alphabetic())
                    && scheme.chars().all(|c| c.is_ascii_alphanumeric() || matches!(c, '+' | '-' | '.'))
                    && !rest.is_empty()
            }) && !text.contains("//")
                && !text.chars().any(char::is_whitespace),
            "17.8 SR 2, 3",
        ),
        "SQL-datetime literal" => ok(
            text.strip_prefix("DATE '")
                .and_then(|r| r.strip_suffix('\''))
                .is_some_and(|d| iso_shape(d, "dddd-dd-dd") && NaiveDate::parse_from_str(d, "%Y-%m-%d").is_ok()),
            "21.2 SR 69",
        ),
        "SQL-interval literal" => ok(
            text.strip_prefix("INTERVAL '")
                .and_then(|r| r.split_once("' "))
                .is_some_and(|(n, unit)| {
                    // the default leading field precision is 2 (the twelfth review)
                    !n.is_empty()
                        && n.len() <= 2
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

/// Whether `c` has the shape `pattern` (`d` an ASCII digit, any other character itself),
/// optionally followed by `.` and ASCII digits (a fraction of seconds).
fn iso_shape(c: &str, pattern: &str) -> bool {
    let n = pattern.len();
    if c.len() < n || !c.is_char_boundary(n) {
        return false;
    }
    let (head, tail) = c.split_at(n);
    let head_ok = head
        .chars()
        .zip(pattern.chars())
        .all(|(x, p)| if p == 'd' { x.is_ascii_digit() } else { x == p });
    let tail_ok = tail.is_empty()
        || (pattern.contains(':')
            && tail.len() > 1
            && tail.starts_with('.')
            && tail[1..].chars().all(|x| x.is_ascii_digit()));
    head_ok && tail_ok
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
                // a value past 64 bits saturates and is not compared (the twelfth review): such
                // a length is refused, H2 bounding what S writes far below it
                if let (Some(min), Some(max)) = (min, max)
                    && (min > max || min == u64::MAX || max == u64::MAX)
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
                    && (s > p || s == u64::MAX || p == u64::MAX)
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
                // 16.6 SR 8 (reading): a selective path pattern holds no subquery, so no reference
                // inside one can reach outside it unseen (the eleventh review: subqueries do sit in
                // graph patterns, `( { a : EXISTS { <- } } )`). Selective by its own prefix or by the
                // graph pattern's KEEP.
                {
                let selective_prefix = |n: &Plain| {
                    let mut found = Vec::new();
                    find(n, "path search prefix", &mut found);
                    found.first().is_some_and(|p| own(p, "all path search").is_none())
                };
                let keep = own(node, "keep clause").is_some_and(|k| selective_prefix(k));
                let mut pps = Vec::new();
                find(node, "path pattern", &mut pps);
                for pp in pps {
                    let own_prefix = own(pp, "path pattern prefix").is_some_and(|p| selective_prefix(p));
                    if (keep || own_prefix)
                        && (contains(pp, "procedure body") || contains(pp, "exists predicate"))
                    {
                        out.push(violation(
                            &path,
                            "16.6 SR 8 nested",
                            "a subquery inside a selective path pattern (reading)".into(),
                        ));
                    }
                }
                }
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
                let mut keeps = Vec::new();
                find(node, "keep clause", &mut keeps);
                let own_keep = own(node, "keep clause");
                let nested_searched = all.iter().any(|pp| {
                    own(pp, "path pattern prefix").is_some_and(|p| contains(p, "path search prefix"))
                }) || keeps.iter().any(|k| {
                    // a nested graph pattern's own KEEP with a search prefix (the twelfth review)
                    !own_keep.is_some_and(|o| std::ptr::eq(o, *k)) && contains(k, "path search prefix")
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
                // a subquery in the catalog procedure's definitions holds statements it simply
                // contains too (no catalog specification intervenes; the twelfth review)
                let definition_statements = name == "catalog-modifying procedure specification" && {
                    // this procedure's own body's definitions, not a nested CALL's
                    let mut bodies = Vec::new();
                    find(node, "procedure body", &mut bodies);
                    bodies
                        .first()
                        .and_then(|pb| own(pb, "binding variable definition block"))
                        // an EXISTS holds a statement after 19.4 SR 2, 3's replacement
                        .is_some_and(|b| contains(b, "statement") || contains(b, "exists predicate"))
                };
                if definition_statements {
                    out.push(violation(
                        &path,
                        "9.1 SR 5 nested",
                        "a subquery's statement in a catalog procedure's definitions (reading)".into(),
                    ));
                }
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
                // A SELECT is focused as written and ambient as replaced (14.12 SR 1, 27): read
                // strictly, it is both, so it stands beside no other focused or ambient
                // statement (the tenth review: `INSERT ( ) NEXT SELECT ..` passed as ambient).
                let is_select = |d: &&Plain| inner(d).and_then(def_name) == Some("select statement");
                let has = |n: &str| direct.iter().any(|d| def_name(d) == Some(n));
                let select = direct.iter().any(|d| def_name(d) == Some("focused linear query statement") && is_select(d));
                let focused = direct.iter().any(|d| {
                    (def_name(d) == Some("focused linear query statement") && !is_select(d))
                        || def_name(d) == Some("focused linear data-modifying statement")
                });
                let ambient = has("ambient linear query statement") || has("ambient linear data-modifying statement");
                if (focused && ambient) || (select && (focused || ambient)) {
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
                // a SELECT both focused and ambient, as in 9.2 SR 5 above
                let is_select = |d: &&Plain| inner(d).and_then(def_name) == Some("select statement");
                let select = direct.iter().any(|d| def_name(d) == Some("focused linear query statement") && is_select(d));
                let focused = direct
                    .iter()
                    .any(|d| def_name(d) == Some("focused linear query statement") && !is_select(d));
                let ambient = direct.iter().any(|d| def_name(d) == Some("ambient linear query statement"));
                if (focused && ambient) || (select && (focused || ambient)) {
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
                // 4.2.5.3, 17.6 SR 5 b (reading): a parent with an object name is a catalog
                // object, which holds no catalog object; whatever is wanted in it, no
                // environment has.
                if kids.iter().any(|k| def_name(k) == Some("object name")) {
                    out.push(violation(
                        &path,
                        "17.6 SR 5",
                        "a parent with an object name: a catalog object holds no catalog object (reading)".into(),
                    ));
                }
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
                let known: Vec<bool> = types.iter().map(|t| known_not_null(t)).collect();
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
            // 16.8 SR 4 a ii, 11.1 SR 3 (reading): a closed graph type is not followed, so no
            // value is given one where it could become a working graph (a cast target, a
            // declared value type, a union component of either). a list or record element can
            // become one, through a property reference or a FOR variable; the types checker's
            // "11.1 SR 3 material" refuses every static graph type under VARIABLE (the
            // nineteenth review). found by the sixth review.
            "cast target" | "opt typed value initializer" if closed_graph_outside_collections(node) => {
                out.push(violation(
                    &path,
                    "16.8 SR 4",
                    "a value given a closed graph type: its labels are not followed (reading)".into(),
                ));
            }
            // 20.5 SR 5 (reading, the twin of refine::UntypedLetValues): no typed definition in
            // a let value expression, whose names have their initializers' types
            "let value expression" => {
                let mut typed = Vec::new();
                find(node, "opt typed value initializer", &mut typed);
                // this expression's own definitions: a nested LET's are judged at its own node
                if let Some(list) = own(node, "let variable definition list")
                    && typed.iter().any(|t| own(t, "value type").is_some() && {
                        let mut lists = Vec::new();
                        find(list, "opt typed value initializer", &mut lists);
                        lists.iter().any(|l| std::ptr::eq(*l, *t))
                    })
                {
                    out.push(violation(
                        &path,
                        "20.5 SR 5",
                        "a typed definition in a let value expression (reading)".into(),
                    ));
                }
            }
            // 21.2 SR 72 with 68 (reading, the twin of refine::NoSqlInterval): no SQL interval
            // literal, whose equivalent duration string conforms to no form of SR 68
            "duration literal" if contains(node, "SQL-interval literal") => {
                out.push(violation(
                    &path,
                    "21.2 SR 72",
                    "an SQL interval literal: its equivalent duration string breaks SR 68 (reading)".into(),
                ));
            }
            // 20.29 GR 2 with 20.28 SR 1 (reading, the twin of refine::NoDurationRecord): a
            // DURATION over a record has no declared type the text gives when its fields name
            // no unit (`DURATION ( { } )`), so no record argument is taken (the seventeenth
            // review)
            "duration function parameters" if own(node, "record constructor").is_some() => {
                out.push(violation(
                    &path,
                    "20.28 SR 1 record",
                    "a DURATION over a record (reading)".into(),
                ));
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
        // The Format of <literal> signs only an <unsigned numeric literal> (the twelfth review:
        // `[ - NULL ]` passed).
        "factor" => {
            let tokens_ok = kids.iter().all(|k| matches!(k, Plain::Def { .. }));
            let signed = defs.iter().any(|d| def_name(d) == Some("sign"));
            tokens_ok
                && defs.iter().all(|d| {
                    def_name(d) == Some("sign")
                        || if signed { numeric_literal_shaped(d) } else { literal_shaped(d) }
                })
        }
        "sign" => true,
        _ => {
            // A wrapper: one definition and nothing else.
            kids.len() == 1 && defs.len() == 1 && literal_shaped(defs[0])
        }
    }
}

/// 18.9 SR 4, 85, 86: a value type known not nullable: a <not null> or NOTHING without an
/// intervening value type, or a closed union every component of which is (the twelfth review:
/// a nested `ANY < INT NOT NULL >` component was read as nullable).
fn known_not_null(vt: &Plain) -> bool {
    let mut nots = Vec::new();
    find_simply(vt, "not null", "value type", &mut nots);
    find_simply(vt, "empty type", "value type", &mut nots);
    if !nots.is_empty() {
        return true;
    }
    let mut unions = Vec::new();
    find_simply(vt, "component type list", "value type", &mut unions);
    unions.first().is_some_and(|ctl| {
        let mut comps = Vec::new();
        find_simply(ctl, "value type", "value type", &mut comps);
        !comps.is_empty() && comps.iter().all(|c| known_not_null(c))
    })
}

/// One-child wrappers down to an <unsigned numeric literal>.
fn numeric_literal_shaped(node: &Plain) -> bool {
    if def_name(node) == Some("unsigned numeric literal") {
        return true;
    }
    let Plain::Def { children, .. } = node else { return false };
    let kids = flat(children);
    kids.len() == 1 && matches!(kids[0], Plain::Def { .. }) && numeric_literal_shaped(kids[0])
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

/// A closed graph reference value type in `node`, not inside a list or record type, nor in a
/// nested expression.
fn closed_graph_outside_collections(node: &Plain) -> bool {
    fn walk(n: &Plain) -> bool {
        match def_name(n) {
            Some("closed graph reference value type") => true,
            Some("list value type" | "record type" | "value initializer") => false,
            _ => match n {
                Plain::Def { children, .. } => children.iter().any(walk),
                _ => false,
            },
        }
    }
    match node {
        Plain::Def { children, .. } => children.iter().any(walk),
        _ => false,
    }
}

/// 17.2 SR 2 d i 1 to 17.5 SR 3 b ii (the object a parent holds under the name is of the
/// kind wanted) with H1: a schema holds one object per name, so one name used as two kinds of
/// object is met by no environment. Reading: the parents are not compared, so the same name at
/// two kinds is refused under any parents (found by the sixth review).
fn one_kind_per_name(tree: &Plain, out: &mut Vec<Violation>) {
    let mut kinds: HashMap<String, &'static str> = HashMap::new();
    // a bare name in a graph or table expression is a catalog name of that kind (11.1 SR 2,
    // 11.2 SR 3, reading: even where a variable of that name is in scope); a directory and
    // a schema share their parent's names (the eleventh review)
    let bare = |expr: &str| {
        let mut exprs = Vec::new();
        find(tree, expr, &mut exprs);
        exprs
            .into_iter()
            .filter_map(|e| own(e, "object name or binding variable"))
            .collect::<Vec<_>>()
    };
    let bare_graphs = bare("graph expression");
    let bare_tables = bare("binding table expression");
    for kind in ["graph name", "graph type name", "binding table name", "procedure name", "schema name", "directory name"] {
        let mut names = Vec::new();
        find(tree, kind, &mut names);
        match kind {
            "graph name" => {
                names.extend(bare_graphs.iter().copied());
                find(tree, "delimited graph name", &mut names);
            }
            "binding table name" => {
                names.extend(bare_tables.iter().copied());
                find(tree, "delimited binding table name", &mut names);
            }
            _ => {}
        }
        // schemas and directories share a directory's names, apart from the objects a
        // schema holds
        let container = matches!(kind, "schema name" | "directory name");
        for n in names {
            let rep = graph_type::ident(n);
            let key = if container { format!("/{rep}") } else { rep.clone() };
            match kinds.get(&key) {
                Some(k) if *k != kind => {
                    out.push(Violation {
                        path: String::new(),
                        rule: "17.2 SR 2",
                        detail: format!("{rep} is used as a <{k}> and a <{kind}>: one object per name (H1)"),
                    });
                    return;
                }
                _ => {
                    kinds.insert(key, kind);
                }
            }
        }
    }
}

/// Reading: no delimited identifier as a binding variable, a field, property or parameter
/// name, or an alias. The checkers compare such names in many places, and a delimited one
/// (`"x"`) stands for the same name as a regular one; refusing it keeps every comparison on
/// one spelling (the twelfth review found raw-text comparisons in scope, LET, YIELD, records
/// and SET). Labels, graph and type names keep their delimited forms (compared by
/// representative form).
fn delimited_names(tree: &Plain, out: &mut Vec<Violation>) {
    let mut names = Vec::new();
    for want in [
        "binding variable",
        "binding variable reference",
        "field name",
        "property name",
        "parameter name",
        "return item alias",
        "select item alias",
    ] {
        find(tree, want, &mut names);
    }
    if names.iter().any(|n| contains(n, "delimited identifier")) {
        out.push(Violation {
            path: String::new(),
            rule: "21.3 SR 4 names",
            detail: "a delimited identifier as a variable, field, property or parameter name or an alias (reading)".into(),
        });
    }
}

/// 12.8, 13.6, 14.5 SR 3 with H1: a procedure has one kind (4.10.2.2, 4.10.2.4), so one named
/// procedure called as two kinds in a program is met by no environment (the sixteenth review).
/// Reading: procedures compared by their written reference.
fn procedure_kinds(tree: &Plain, out: &mut Vec<Violation>) {
    let mut seen: HashMap<String, &'static str> = HashMap::new();
    for kind in [
        "call query statement",
        "call data-modifying procedure statement",
        "call catalog-modifying procedure statement",
    ] {
        let mut calls = Vec::new();
        find(tree, kind, &mut calls);
        for c in calls {
            // the named procedures this call statement calls itself, not those in a nested body
            let mut pcs = Vec::new();
            find(c, "procedure call", &mut pcs);
            let Some(npc) = pcs.first().and_then(|pc| own(pc, "named procedure call")) else { continue };
            let Some(r) = own(npc, "procedure reference") else { continue };
            // by the representative form of the procedure's own name, its parent left out: `a`,
            // `. / a`, `CURRENT_SCHEMA / a` and `"a"` may all name one procedure (17.5 SR 1,
            // 17.1 SR 4 b, 21.3 SR 20), and two procedures of one name in two schemas are read
            // as one, the strict side (the twenty-fifth review)
            let name = rep_names(r).pop().unwrap_or_else(|| r.text());
            match seen.get(&name) {
                Some(k) if *k != kind => {
                    out.push(Violation {
                        path: String::new(),
                        rule: "14.5 SR 3 kinds",
                        detail: format!("{name} is called as a <{k}> and a <{kind}>: one kind per procedure (H1)"),
                    });
                    return;
                }
                _ => {
                    seen.insert(name, kind);
                }
            }
        }
    }
}

/// 15.1 SR 9 with H1: a named procedure called without YIELD returns no column named like a
/// field of the call's incoming record or table, which H1 assumes and no check sees. a YIELD on
/// another call of it shows a column S may then meet (the twenty-fifth review: `MATCH ( x )
/// CALL a ( ) .. NEXT CALL a ( ) YIELD x`), so a procedure called both with and without YIELD
/// is refused (a reading, the strict side).
fn procedure_yields(tree: &Plain, out: &mut Vec<Violation>) {
    let mut npcs = Vec::new();
    find(tree, "named procedure call", &mut npcs);
    let mut with: HashMap<String, bool> = HashMap::new();
    for npc in npcs {
        let Some(r) = own(npc, "procedure reference") else { continue };
        let name = rep_names(r).pop().unwrap_or_else(|| r.text());
        let y = own(npc, "yield clause").is_some();
        if with.insert(name.clone(), y).is_some_and(|before| before != y) {
            out.push(Violation {
                path: String::new(),
                rule: "15.1 SR 9 yield",
                detail: format!("{name} is called with and without YIELD (reading, H1)"),
            });
            return;
        }
    }
}

/// Group variables and group list types are refused on the tree: an element variable declared
/// under a quantifier (16.7 SR 22 e) and a written GROUP list type (18.9 SR 68). no set prints
/// either, and rounds 28 and 29 found the checkers disagree on them (a union's degree, a
/// parenthesized WHERE, vertical aggregates, 20.1 SR 7 by degree rather than type), so the
/// family is withheld whole rather than read (a reading, the strict side; gate-only).
fn group_variables(tree: &Plain, out: &mut Vec<Violation>) {
    let mut qs = Vec::new();
    find(tree, "quantified path primary", &mut qs);
    let declared = qs.iter().any(|q| contains(q, "element variable declaration"));
    let mut names = Vec::new();
    find(tree, "list value type name", &mut names);
    let written = names.iter().any(|n| n.text().to_ascii_uppercase().starts_with("GROUP"));
    if declared || written {
        out.push(Violation {
            path: String::new(),
            rule: "16.7 SR 22 group",
            detail: "a group variable or a group list type (withheld, reading)".into(),
        });
    }
}

/// Families no set prints and on which rounds 18-28 found the checkers' logic wrong, withheld
/// whole rather than read (the strict side; gate-only; the thirtieth review mapped them, each
/// detector with no hit in a printed set):
/// - a parameter inside a combination (CASE, COALESCE, NULLIF, a list constructor or a list
///   concatenation): the H1 remap of a parameter written once
/// - a session parameter one SESSION SET sets and another command reads (7.1 SR 6, 22.1 SR 5)
/// - a named procedure call with YIELD (15.1 SR 9, 16.14)
/// - a selective path pattern that declares an element variable (16.6 SR 5-8)
/// - a path pattern union or multiset alternation that declares an element variable (16.7
///   SR 10, 11, 22 d)
fn unprinted_families(tree: &Plain, out: &mut Vec<Violation>) {
    let mut push = |what: &str| {
        out.push(Violation {
            path: String::new(),
            rule: "withheld family",
            detail: format!("{what} (withheld whole, reading)"),
        })
    };
    let param_name = |n: &Plain| {
        let mut pn = Vec::new();
        find(n, "parameter name", &mut pn);
        pn.first().map_or_else(|| n.text(), |p| graph_type::ident(p))
    };
    let declares = |n: &Plain| contains(n, "element variable declaration");
    // an input of a combination that is, through one-child nodes, a bare parameter
    let mut inputs = Vec::new();
    for c in ["simple case", "searched case"] {
        let mut cases = Vec::new();
        find(tree, c, &mut cases);
        for case in cases {
            find(case, "result expression", &mut inputs);
        }
    }
    let mut lists = Vec::new();
    find(tree, "list value constructor by enumeration", &mut lists);
    for l in lists {
        find(l, "list element", &mut inputs);
    }
    for c in ["case abbreviation", "list concatenation"] {
        let mut nodes = Vec::new();
        find(tree, c, &mut nodes);
        for n in nodes {
            inputs.extend(def_kids(n));
        }
    }
    if inputs.iter().any(|i| bare_parameter(i)) {
        push("a parameter as a combination's input");
    }
    let mut commands = Vec::new();
    find(tree, "session set command", &mut commands);
    for (i, c) in commands.iter().enumerate() {
        let mut sps = Vec::new();
        find(c, "session parameter specification", &mut sps);
        let set: Vec<String> = sps.iter().map(|s| param_name(s)).collect();
        let read = commands.iter().enumerate().any(|(j, d)| {
            let mut dps = Vec::new();
            find(d, "dynamic parameter specification", &mut dps);
            j != i && dps.iter().any(|p| set.contains(&param_name(p)))
        });
        if read {
            push("a session parameter set by one command and read by another");
            break;
        }
    }
    let mut npcs = Vec::new();
    find(tree, "named procedure call", &mut npcs);
    if npcs.iter().any(|n| own(n, "yield clause").is_some()) {
        push("a named procedure call with YIELD");
    }
    let mut pps = Vec::new();
    find(tree, "path pattern", &mut pps);
    if pps.iter().any(|p| (contains(p, "any path search") || contains(p, "shortest path search")) && declares(p)) {
        push("a selective path pattern that declares an element variable");
    }
    let mut unions = Vec::new();
    find(tree, "path pattern union", &mut unions);
    find(tree, "path multiset alternation", &mut unions);
    if unions.iter().any(|u| declares(u)) {
        push("a path pattern union or alternation that declares an element variable");
    }
}

/// The non-terminal children of `node`, synthetic groups flattened.
fn def_kids(node: &Plain) -> Vec<&Plain> {
    let mut out = Vec::new();
    if let Plain::Def { children, .. } = node {
        for c in children {
            match c {
                Plain::Def { synthetic: true, .. } => out.extend(def_kids(c)),
                Plain::Def { .. } => out.push(c),
                _ => {}
            }
        }
    }
    out
}

/// `node` is, through nodes with one child each, a <dynamic parameter specification>.
fn bare_parameter(node: &Plain) -> bool {
    let mut n = node;
    loop {
        if matches!(n, Plain::Def { name, .. } if name == "dynamic parameter specification") {
            return true;
        }
        let Plain::Def { children, .. } = n else { return false };
        let all: Vec<&Plain> = children.iter().collect();
        match def_kids(n).as_slice() {
            [only] if all.len() == 1 || all.iter().all(|c| matches!(c, Plain::Def { .. })) => n = only,
            _ => return false,
        }
    }
}

/// H2's implementation limits, checked on the tree so they rest on no generator (the
/// fifteenth review: `{ 256 }` passed): quantifier bounds at most 255 (16.11 SR 1, IL018),
/// character lengths at most 16383 and byte lengths at most 65534, the maxima the text
/// guarantees (18.9 SR 17, 25, IL013), an exact precision of at most 18 digits (SR 32, IL011),
/// an approximate precision of at most 112, FLOAT128's (SR 43 d), and a scale of at most 8
/// (SR 42, IL011).
fn h2_bounds(tree: &Plain, out: &mut Vec<Violation>) {
    let mut push = |rule: &'static str, what: String| {
        out.push(Violation { path: String::new(), rule, detail: format!("{what} is past the limit H2 names") })
    };
    for q in ["fixed quantifier", "lower bound", "upper bound"] {
        let mut nodes = Vec::new();
        find(tree, q, &mut nodes);
        for n in nodes {
            let mut ints = Vec::new();
            find(n, "unsigned integer", &mut ints);
            if ints.iter().any(|i| integer_value(i) > 255) {
                push("16.11 SR 1", format!("a quantifier bound in {}", n.text()));
            }
        }
    }
    for (ty, most, rule) in [("character string type", 16383, "18.9 SR 17"), ("byte string type", 65534, "18.9 SR 25")] {
        let mut nodes = Vec::new();
        find(tree, ty, &mut nodes);
        for n in nodes {
            for l in ["min length", "max length", "fixed length"] {
                if own(n, l).is_some_and(|v| integer_value(v) > most) {
                    push(rule, format!("a length in {}", n.text()));
                }
            }
        }
    }
    // 21.2 SR 14, IL010: an unsigned integer of at most 9 digits, the least the text
    // guarantees (the twenty-fifth review: it rested on H2's general clause alone)
    let mut ints = Vec::new();
    find(tree, "unsigned integer", &mut ints);
    for i in ints {
        let t = i.text().to_ascii_lowercase();
        let digits = t.strip_prefix("0x").or_else(|| t.strip_prefix("0o")).or_else(|| t.strip_prefix("0b")).unwrap_or(&t);
        // written digits, and the decimal digits of the value a 0x, 0o or 0b form is
        // rewritten to (21.2 SR 6-8)
        if digits.chars().filter(|c| *c != '_').count() > 9 || integer_value(i) > 999_999_999 {
            push("21.2 SR 14", format!("the unsigned integer {}", i.text()));
        }
    }
    // 18.9 SR 73 d i: a list's maximum cardinality is IL015's, which no guarantee bounds; H2
    // names the most S declares, 888 (the eighteenth review: `LIST [ 99999999999999999999 ]`)
    let mut lists = Vec::new();
    find(tree, "list value type", &mut lists);
    for n in lists {
        if own(n, "max length").is_some_and(|v| integer_value(v) > 888) {
            push("18.9 SR 73", format!("a maximum cardinality in {}", n.text()));
        }
    }
    for (ty, precision, scale, rule) in [
        ("exact numeric type", 18, 18, "18.9 SR 32"),
        ("approximate numeric type", 112, 8, "18.9 SR 42"),
    ] {
        let mut nodes = Vec::new();
        find(tree, ty, &mut nodes);
        for n in nodes {
            let mut ps = Vec::new();
            find(n, "precision", &mut ps);
            let mut ss = Vec::new();
            find(n, "scale", &mut ss);
            if ps.iter().any(|p| integer_value(p) > precision) || ss.iter().any(|v| integer_value(v) > scale) {
                push(rule, format!("a precision or scale in {}", n.text()));
            }
        }
    }
}

/// 12.3 SR 7 a, b with H1 (one environment, judged before execution): a schema a program
/// drops is not the working schema it sets with AT, and holds nothing the program names
/// through it (the fourteenth review: `AT / a DROP SCHEMA / a`, `DROP GRAPH / a / b DROP
/// SCHEMA / a`). Reading: schemas compared by their written absolute paths.
fn schema_drops(tree: &Plain, out: &mut Vec<Violation>) {
    let mut drops = Vec::new();
    find(tree, "drop schema statement", &mut drops);
    if drops.is_empty() {
        return;
    }
    // by the representative form of the dropped schema's own name: a working schema whose
    // reference ends in it, or a parent path through it, is read as the dropped one, whatever
    // the rest of the path (the strict side; the twenty-fifth review: `AT / "a" DROP SCHEMA
    // / a` and `DROP GRAPH / "a" / b DROP SCHEMA / a` compared the written text)
    for d in drops {
        let Some(pan) = own(d, "catalog schema parent and name") else { continue };
        let Some(dropped) = rep_names(pan).pop() else { continue };
        let mut ats = Vec::new();
        find(tree, "at schema clause", &mut ats);
        let set = ats.iter().any(|a| {
            own(a, "schema reference").is_some_and(|r| rep_names(r).last() == Some(&dropped))
        });
        let mut parents = Vec::new();
        find(tree, "catalog object parent reference", &mut parents);
        let inside = parents.iter().any(|p| rep_names(p).contains(&dropped));
        if set || inside {
            out.push(Violation {
                path: String::new(),
                rule: "12.3 SR 7",
                detail: format!("{dropped} is dropped while the program works in it or names something in it (H1)"),
            });
        }
    }
}

/// The representative forms of the <identifier>s under `node`, in order.
fn rep_names(node: &Plain) -> Vec<String> {
    let mut ids = Vec::new();
    find(node, "identifier", &mut ids);
    ids.into_iter().map(graph_type::ident).collect()
}

/// 12.6 SR 7 b iv (and 12.4 through its GR 5 rewrite): a LIKE source's declared type has a
/// constraining graph type. The current graph and a catalog graph have one (H1); a value or a
/// binding variable may be open, so neither is taken (reading; the eleventh review:
/// `LIKE CAST ( NULL AS PROPERTY GRAPH )`).
fn like_sources(tree: &Plain, out: &mut Vec<Violation>) {
    let mut likes = Vec::new();
    find(tree, "graph type like graph", &mut likes);
    if likes.is_empty() {
        return;
    }
    let mut bvs = Vec::new();
    find(tree, "binding variable", &mut bvs);
    let bound: Vec<String> = bvs.iter().map(|b| graph_type::ident(b)).collect();
    for like in likes {
        let fine = own(like, "graph expression").is_some_and(|ge| {
            own(ge, "current graph").is_some()
                || own(ge, "graph reference").is_some()
                || own(ge, "object name or binding variable")
                    .is_some_and(|n| !bound.contains(&graph_type::ident(n)))
        });
        if !fine {
            out.push(Violation {
                path: String::new(),
                rule: "12.6 SR 7",
                detail: "a LIKE source not known to have a constraining graph type (reading)".into(),
            });
        }
    }
}

/// 17.1 SR 2 a i and SR 5 with H1: a bare `/` schema reference needs the catalog root to be a
/// schema, an absolute directory path needs it to be a directory; one program using both is met
/// by no environment (found by the fifth review).
fn catalog_root(tree: &Plain, out: &mut Vec<Violation>) {
    let mut refs = Vec::new();
    find(tree, "absolute catalog schema reference", &mut refs);
    let schema = refs.iter().any(|r| r.text() == "/");
    let mut dirs = Vec::new();
    find(tree, "absolute directory path", &mut dirs);
    // a `..` step needs a directory above the working schema, which a root schema has not
    // (the eleventh review)
    find(tree, "relative directory path", &mut dirs);
    if schema && !dirs.is_empty() {
        out.push(Violation {
            path: String::new(),
            rule: "17.1 SR 2",
            detail: "the catalog root is used as a schema (/) and as a directory (an absolute directory path): no environment has both (H1)".into(),
        });
    }
    // 17.1 SR 6 d i: the `..` steps start below the root. an AT with an absolute reference
    // fixes the working schema, and with it how many steps there are room for, so the depth is
    // no longer H1's; any `..` in such a program is refused (a reading, the strict side; the
    // twenty-sixth review: `AT / s CREATE GRAPH .. / .. / t / g ANY`)
    let mut ats = Vec::new();
    find(tree, "at schema clause", &mut ats);
    let fixed = ats.iter().any(|a| contains(a, "absolute catalog schema reference"));
    let mut rdps = Vec::new();
    find(tree, "relative directory path", &mut rdps);
    if fixed && !rdps.is_empty() {
        out.push(Violation {
            path: String::new(),
            rule: "17.1 SR 6 at",
            detail: "a `..` step in a program whose AT fixes the working schema (reading)".into(),
        });
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
    // a bare name in a graph or table expression names a catalog object too (11.1 SR 2,
    // 11.2 SR 3; the eleventh review)
    find(tree, "object name or binding variable", &mut all);
    // a delimited graph or table name too (the twelfth review)
    find(tree, "delimited graph name", &mut all);
    find(tree, "delimited binding table name", &mut all);
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
            // representative forms (21.3 SR 3, 4): `"a"` and `a` are one name
            let text = graph_type::ident(m);
            // another name: not the made one, nor a node inside it (a `<graph name>` holds its
            // `<delimited graph name>`)
            let inside = |o: &Plain| {
                fn holds(n: &Plain, o: &Plain) -> bool {
                    std::ptr::eq(n, o)
                        || match n {
                            Plain::Def { children, .. } => children.iter().any(|c| holds(c, o)),
                            _ => false,
                        }
                }
                holds(m, o)
            };
            if all.iter().any(|o| !inside(o) && graph_type::ident(o) == text) {
                out.push(Violation {
                    path: String::new(),
                    rule,
                    detail: format!("{text} is created and named elsewhere: it must and must not exist (H1)"),
                });
            }
        }
    }
}
