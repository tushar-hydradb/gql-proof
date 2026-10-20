//! Static check that rendering a tree as "tokens joined by one space" yields GQL source text.
//!
//! ISO/IEC 39075:2024 21.3 Syntax Rules 13 and 14: a token other than a byte string literal
//! contains no separator, and any token may be followed by a separator. So a rendered query is
//! valid source text if every chunk printed as one token really is one token. The renderer
//! prints a chunk for every literal in a syntactic rule and for every subtree rooted at a
//! lexical definition (one reachable from `<token>`). This module proves, over the grammar and
//! once for all trees, that each of those chunks can only ever be a single token.
//!
//! It works on the ISO EBNF directly and depends on nothing but `bnf`, so it is part of the
//! trusted base, separate from the generator.

use crate::bnf::{Bnf, Ebnf, visit_refs};
use std::collections::{BTreeSet, HashMap, HashSet};

/// Prose leaves allowed in syntactic rules, printed as one chunk. The grammar cannot show
/// these are tokens, so each is an explicit assumption with the rule that backs it.
pub const ASSUMED_TOKENS: &[(&str, &str)] = &[
    (
        "SQL-datetime literal",
        "21.2 SR 69: the <datetime literal> of ISO/IEC 9075-2:2023, a keyword and a string",
    ),
    (
        "SQL-interval literal",
        "21.2 SR 70: the <interval literal> of ISO/IEC 9075-2:2023, keyword, string, qualifier",
    ),
    (
        "external object reference",
        "17.8 SR 2, 3: a URI with a scheme; the stub avoids `//`, which would open a comment",
    ),
];

/// Prose leaves with no portable form. The generator never produces them and the verifier
/// rejects them.
pub const EXCLUDED: &[(&str, &str)] = &[(
    "implementation-defined access mode",
    "8.2 SR 3: Format and Syntax Rules are implementation-defined (IE002)",
)];

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Literal {
    Kw(String),
    Term(String),
}

#[derive(Debug)]
pub struct Report {
    pub start: String,
    /// Definitions reachable from the start without entering the token layer.
    pub syntactic: usize,
    /// Lexical definitions referenced from those, each printed as one token.
    pub boundary: usize,
    /// Definitions provably deriving only single tokens (`<token> =>* d`).
    pub token_defs: usize,
    pub failures: Vec<String>,
    pub assumptions: Vec<(&'static str, &'static str)>,
    pub excluded: Vec<(&'static str, &'static str)>,
}

impl Report {
    pub fn passed(&self) -> bool {
        self.failures.is_empty()
    }
}

pub struct Grammar<'b> {
    bnf: &'b Bnf,
    defs: HashMap<&'b str, &'b Ebnf>,
    nullable: HashSet<&'b str>,
}

impl<'b> Grammar<'b> {
    pub fn new(bnf: &'b Bnf) -> Self {
        let defs: HashMap<&str, &Ebnf> =
            bnf.defs.iter().map(|d| (d.name.as_str(), &d.rhs)).collect();
        let mut g = Grammar {
            bnf,
            defs,
            nullable: HashSet::new(),
        };
        // Least fixed point. Prose leaves count as non-empty, which only makes every check
        // below stricter.
        loop {
            let next: HashSet<&str> = g
                .defs
                .iter()
                .filter(|(_, e)| g.nullable(e))
                .map(|(&name, _)| name)
                .collect();
            if next.len() == g.nullable.len() {
                break;
            }
            g.nullable = next;
        }
        g
    }

    fn nullable(&self, e: &Ebnf) -> bool {
        match e {
            Ebnf::Seq(items) => items.iter().all(|i| self.nullable(i)),
            Ebnf::Alt(alts) => alts.iter().any(|a| self.nullable(a)),
            Ebnf::Opt(_) => true,
            Ebnf::Repeat(inner) => self.nullable(inner),
            Ebnf::Ref(name) => self.nullable.contains(name.as_str()),
            Ebnf::Kw(_) | Ebnf::Term(_) | Ebnf::Opaque(_) => false,
        }
    }

    /// References and literals `e` can derive on their own, every sibling deriving nothing.
    fn units(&self, e: &'b Ebnf, refs: &mut Vec<&'b str>, lits: &mut BTreeSet<Literal>) {
        match e {
            Ebnf::Ref(name) => refs.push(name),
            Ebnf::Kw(k) => {
                lits.insert(Literal::Kw(k.clone()));
            }
            Ebnf::Term(t) => {
                lits.insert(Literal::Term(t.clone()));
            }
            Ebnf::Opaque(_) => {}
            Ebnf::Opt(inner) | Ebnf::Repeat(inner) => self.units(inner, refs, lits),
            Ebnf::Alt(alts) => alts.iter().for_each(|a| self.units(a, refs, lits)),
            Ebnf::Seq(items) => {
                for (i, item) in items.iter().enumerate() {
                    let rest_empty = items
                        .iter()
                        .enumerate()
                        .all(|(j, other)| i == j || self.nullable(other));
                    if rest_empty {
                        self.units(item, refs, lits);
                    }
                }
            }
        }
    }

    /// Definitions reachable from `from`, including itself.
    pub fn reachable(&self, from: &str) -> HashSet<&'b str> {
        let mut seen = HashSet::new();
        let mut stack = vec![self.key(from)];
        while let Some(name) = stack.pop() {
            if seen.insert(name) {
                visit_refs(self.defs[name], &mut |r| stack.push(self.key(r)));
            }
        }
        seen
    }

    fn key(&self, name: &str) -> &'b str {
        self.defs
            .get_key_value(name)
            .map(|(k, _)| *k)
            .expect("refs resolve")
    }

    /// Definitions every derivation of which is a single token: `<token> =>* d`, plus the
    /// literals derivable that way.
    fn token_closure(&self) -> (HashSet<&'b str>, BTreeSet<Literal>) {
        let mut defs = HashSet::from([self.key("token")]);
        let mut lits = BTreeSet::new();
        let mut stack = vec![self.key("token")];
        while let Some(name) = stack.pop() {
            let mut refs = Vec::new();
            self.units(self.defs[name], &mut refs, &mut lits);
            for r in refs {
                if defs.insert(r) {
                    stack.push(r);
                }
            }
        }
        (defs, lits)
    }

    /// In the token closure, or every alternative is: `<sign> ::= <plus sign> | <minus sign>`.
    fn token_only(&self, name: &str, closure: &HashSet<&str>, depth: u32) -> bool {
        if closure.contains(name) {
            return true;
        }
        if depth == 0 {
            return false;
        }
        let alts: Vec<&Ebnf> = match self.defs[name] {
            Ebnf::Alt(alts) => alts.iter().collect(),
            other => vec![other],
        };
        alts.iter().all(|a| match a {
            Ebnf::Ref(r) => self.token_only(r, closure, depth - 1),
            _ => false,
        })
    }

    /// Lexical definitions: those reachable from `<token>`. The renderer prints each subtree
    /// rooted at the first lexical definition on its path as one chunk.
    pub fn lexical(&self) -> HashSet<&'b str> {
        self.reachable("token")
    }

    /// Keywords that may not be used as identifiers (21.3 SR 18).
    pub fn reserved_words(&self) -> HashSet<String> {
        let mut words = HashSet::new();
        for def in ["reserved word", "pre-reserved word"] {
            let mut refs = Vec::new();
            let mut lits = BTreeSet::new();
            self.units(self.defs[def], &mut refs, &mut lits);
            words.extend(lits.into_iter().filter_map(|l| match l {
                Literal::Kw(k) => Some(k),
                Literal::Term(_) => None,
            }));
        }
        words
    }

    pub fn rhs(&self, name: &str) -> Option<&'b Ebnf> {
        self.defs.get(name).copied()
    }

    pub fn bnf(&self) -> &'b Bnf {
        self.bnf
    }

    pub fn check(&self, start: &str) -> Report {
        let lexical = self.lexical();
        let (closure, token_lits) = self.token_closure();
        let mut failures = Vec::new();

        // The syntactic region: walk from the start, stopping at lexical definitions.
        let mut syntactic = BTreeSet::new();
        let mut boundary = BTreeSet::new();
        let mut stack = vec![self.key(start)];
        while let Some(name) = stack.pop() {
            if lexical.contains(name) {
                boundary.insert(name);
            } else if syntactic.insert(name) {
                visit_refs(self.defs[name], &mut |r| stack.push(self.key(r)));
            }
        }

        for &name in &boundary {
            if !self.token_only(name, &closure, 8) {
                failures.push(format!(
                    "<{name}> is printed as one token but can derive something that is not a token"
                ));
            }
        }
        for &name in &closure {
            if self.nullable.contains(name) {
                failures.push(format!("<{name}> can derive the empty string, not a token"));
            }
        }

        let assumed: HashMap<&str, &str> = ASSUMED_TOKENS.iter().copied().collect();
        let excluded: HashMap<&str, &str> = EXCLUDED.iter().copied().collect();
        let mut assumptions = BTreeSet::new();
        let mut exclusions = BTreeSet::new();
        for &name in &syntactic {
            let mut lits = Vec::new();
            literals(self.defs[name], &mut lits);
            for lit in lits {
                match lit {
                    Ebnf::Kw(k) if !token_lits.contains(&Literal::Kw(k.clone())) => failures
                        .push(format!("keyword {k} in <{name}> is not a token")),
                    Ebnf::Term(t) if !token_lits.contains(&Literal::Term(t.clone())) => {
                        failures.push(format!("terminal {t:?} in <{name}> is not a token"))
                    }
                    Ebnf::Opaque(d) => match (assumed.get_key_value(d.as_str()), excluded.get_key_value(d.as_str())) {
                        (Some(pair), _) => {
                            assumptions.insert((*pair.0, *pair.1));
                        }
                        (_, Some(pair)) => {
                            exclusions.insert((*pair.0, *pair.1));
                        }
                        _ => failures.push(format!(
                            "prose definition <{d}> is printed as a token with no stated justification"
                        )),
                    },
                    _ => {}
                }
            }
        }
        failures.sort();
        failures.dedup();

        Report {
            start: start.to_string(),
            syntactic: syntactic.len(),
            boundary: boundary.len(),
            token_defs: closure.len(),
            failures,
            assumptions: assumptions.into_iter().collect(),
            excluded: exclusions.into_iter().collect(),
        }
    }
}

fn literals<'e>(e: &'e Ebnf, out: &mut Vec<&'e Ebnf>) {
    match e {
        Ebnf::Seq(items) | Ebnf::Alt(items) => items.iter().for_each(|i| literals(i, out)),
        Ebnf::Opt(inner) | Ebnf::Repeat(inner) => literals(inner, out),
        Ebnf::Kw(_) | Ebnf::Term(_) | Ebnf::Opaque(_) => out.push(e),
        Ebnf::Ref(_) => {}
    }
}
