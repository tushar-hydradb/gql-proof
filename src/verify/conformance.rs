//! The conformance rules, read straight from the definitions of 5.3.2.1 over a whole tree:
//! search every node, walk its descendants, compare yields. Nothing is shared with the
//! automaton in `features` beyond the pattern data.

use crate::features::{Cond, How, Pattern};
use crate::verify::Plain;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Def,
    Group,
    Token,
}

struct N<'a> {
    def: &'a str,
    kind: Kind,
    parent: Option<usize>,
    children: Vec<usize>,
    /// The tokens this node spells: `tokens[lo..hi]`.
    lo: usize,
    hi: usize,
}

pub struct Tree<'a> {
    nodes: Vec<N<'a>>,
    tokens: Vec<&'a str>,
}

impl<'a> Tree<'a> {
    pub fn new(root: &'a Plain) -> Tree<'a> {
        let mut t = Tree {
            nodes: Vec::new(),
            tokens: Vec::new(),
        };
        t.add(root, None);
        t
    }

    fn add(&mut self, p: &'a Plain, parent: Option<usize>) -> usize {
        let id = self.nodes.len();
        let lo = self.tokens.len();
        let (def, kind) = match p {
            Plain::Def {
                name, synthetic, ..
            } => (
                name.as_str(),
                if *synthetic { Kind::Group } else { Kind::Def },
            ),
            Plain::Leaf { def, .. } => (def.as_str(), Kind::Token),
            Plain::Kw(_) | Plain::Term(_) => ("", Kind::Token),
        };
        self.nodes.push(N {
            def,
            kind,
            parent,
            children: Vec::new(),
            lo,
            hi: lo,
        });
        match p {
            Plain::Def { children, .. } => {
                for c in children {
                    let c = self.add(c, Some(id));
                    self.nodes[id].children.push(c);
                }
            }
            Plain::Kw(t) | Plain::Term(t) | Plain::Leaf { text: t, .. } => self.tokens.push(t),
        }
        self.nodes[id].hi = self.tokens.len();
        id
    }

    fn is_def(&self, i: usize, name: &str) -> bool {
        self.nodes[i].kind == Kind::Def && self.nodes[i].def == name
    }

    /// The children of `i` as its definition's right hand side reads them: groups seen
    /// through.
    fn rhs(&self, i: usize) -> Vec<usize> {
        let mut out = Vec::new();
        for &c in &self.nodes[i].children {
            if self.nodes[c].kind == Kind::Group {
                out.extend(self.rhs(c));
            } else {
                out.push(c);
            }
        }
        out
    }

    /// The nearest definition above `i`.
    fn parent_def(&self, i: usize) -> Option<usize> {
        let mut p = self.nodes[i].parent;
        while let Some(x) = p {
            if self.nodes[x].kind == Kind::Def {
                return Some(x);
            }
            p = self.nodes[x].parent;
        }
        None
    }

    /// Definitions strictly inside `i`, each with the definitions strictly between.
    fn below(&self, i: usize) -> Vec<(usize, Vec<usize>)> {
        let mut out = Vec::new();
        let mut todo: Vec<(usize, Vec<usize>)> = self.nodes[i]
            .children
            .iter()
            .map(|&c| (c, Vec::new()))
            .collect();
        while let Some((n, between)) = todo.pop() {
            let mut next = between.clone();
            if self.nodes[n].kind == Kind::Def {
                out.push((n, between));
                next.push(n);
            }
            for &c in &self.nodes[n].children {
                todo.push((c, next.clone()));
            }
        }
        out
    }

    /// Where `words` occur in a row in the yield of `i`.
    fn occurrences(&self, i: usize, words: &[String]) -> Vec<usize> {
        let (lo, hi) = (self.nodes[i].lo, self.nodes[i].hi);
        let k = words.len();
        (lo..(hi + 1).saturating_sub(k))
            .filter(|&s| (0..k).all(|j| self.tokens[s + j].eq_ignore_ascii_case(&words[j])))
            .collect()
    }

    /// Definitions strictly inside `i` whose yield covers tokens `s..e`.
    fn covering(&self, i: usize, s: usize, e: usize) -> Vec<usize> {
        self.below(i)
            .into_iter()
            .map(|(n, _)| n)
            .filter(|&n| self.nodes[n].lo <= s && e <= self.nodes[n].hi)
            .collect()
    }

    /// Whether some node of the tree matches `p`.
    pub fn occurs(&self, p: &Pattern) -> bool {
        match (&p.nt, &p.words) {
            (None, Some(words)) => !self.occurrences(0, words).is_empty(),
            _ => (0..self.nodes.len()).any(|i| self.matches(i, p)),
        }
    }

    fn matches(&self, i: usize, p: &Pattern) -> bool {
        let Some(nt) = &p.nt else { return false };
        if !self.is_def(i, nt) {
            return false;
        }
        if let Some(words) = &p.words
            && self.occurrences(i, words).is_empty()
        {
            return false;
        }
        p.conds.iter().all(|c| self.holds(i, nt, c))
    }

    fn holds(&self, i: usize, nt: &str, c: &Cond) -> bool {
        match c {
            Cond::Contains(c) => {
                let n: usize = c.any.iter().map(|alt| self.count(i, nt, c.how, alt)).sum();
                let held = if c.exactly_one { n == 1 } else { n > 0 };
                held != c.negated
            }
            Cond::Is(is) => {
                let held = is.any.iter().any(|alt| match (&alt.nt, &alt.words) {
                    // A1 is B1: the text of A1 is the text of an instance of <B> in it.
                    (Some(b), _) => {
                        self.is_def(i, b)
                            || (self.nodes[i].lo < self.nodes[i].hi
                                && self.below(i).iter().any(|&(m, _)| {
                                    self.is_def(m, b)
                                        && (self.nodes[m].lo, self.nodes[m].hi)
                                            == (self.nodes[i].lo, self.nodes[i].hi)
                                }))
                    }
                    (None, Some(words)) => !self.occurrences(i, words).is_empty(),
                    (None, None) => false,
                });
                held != is.negated
            }
            Cond::FollowedBy(pairs) => {
                let shape: Vec<&str> = self
                    .rhs(i)
                    .into_iter()
                    .filter(|&c| self.nodes[c].lo < self.nodes[c].hi)
                    .map(|c| match self.nodes[c].kind {
                        Kind::Def => self.nodes[c].def,
                        _ => "#",
                    })
                    .collect();
                pairs.iter().any(|[a, b]| shape == [a.as_str(), b.as_str()])
            }
            Cond::Parent(p) => {
                let held = self.parent_def(i).is_some_and(|x| self.is_def(x, &p.nt));
                held != p.negated
            }
            Cond::Juxtaposed(j) => self.juxtaposed(i, j),
            Cond::Unflanked(u) => {
                let (lo, hi) = (self.nodes[i].lo, self.nodes[i].hi);
                let defs = (0..self.nodes.len()).filter(|&n| self.is_def(n, &u.by));
                let (mut before, mut after) = (false, false);
                for n in defs {
                    before |= self.nodes[n].hi == lo && self.nodes[n].lo < lo;
                    after |= self.nodes[n].lo == hi && self.nodes[n].hi > hi;
                }
                !(before && after)
            }
        }
    }

    /// Two instances of `first` then `then` in `i`, both at `i`'s depth of graph pattern
    /// matching (no `<procedure body>` or `<graph pattern>` between), with not one token
    /// between them inside an instance of `unless` or inside a deeper depth.
    fn juxtaposed(&self, i: usize, j: &crate::features::Juxtaposed) -> bool {
        let nested = |n: usize| self.is_def(n, "procedure body") || self.is_def(n, "graph pattern");
        let below = self.below(i);
        let same: Vec<usize> = below
            .iter()
            .filter(|(_, between)| !between.iter().any(|&b| nested(b)))
            .map(|&(n, _)| n)
            .collect();
        // Spans whose tokens break a juxtaposition.
        let breaks: Vec<(usize, usize)> = below
            .iter()
            .map(|&(n, _)| n)
            .filter(|&n| nested(n) || j.unless.iter().any(|u| self.is_def(n, u)))
            .map(|n| (self.nodes[n].lo, self.nodes[n].hi))
            .collect();
        same.iter()
            .filter(|&&f| self.is_def(f, &j.first))
            .any(|&f| {
                same.iter()
                    .filter(|&&t| {
                        t != f && self.is_def(t, &j.then) && self.nodes[t].lo >= self.nodes[f].hi
                    })
                    .any(|&t| {
                        let (s, e) = (self.nodes[f].hi, self.nodes[t].lo);
                        !(s..e).any(|k| breaks.iter().any(|&(a, b)| a <= k && k < b))
                    })
            })
    }

    /// How many instances of `alt` `i` contains in the way `how` says (5.3.2.1).
    fn count(&self, i: usize, outer: &str, how: How, alt: &Pattern) -> usize {
        match (&alt.nt, &alt.words) {
            (Some(inner), _) => {
                let candidates: Vec<usize> = match how {
                    How::Immediately => self
                        .rhs(i)
                        .into_iter()
                        .filter(|&c| self.nodes[c].kind == Kind::Def)
                        .collect(),
                    How::Any => self.below(i).into_iter().map(|(n, _)| n).collect(),
                    How::Simply => self
                        .below(i)
                        .into_iter()
                        .filter(|(_, between)| {
                            !between
                                .iter()
                                .any(|&b| self.is_def(b, outer) || self.is_def(b, inner))
                        })
                        .map(|(n, _)| n)
                        .collect(),
                    How::Directly => self
                        .below(i)
                        .into_iter()
                        .filter(|(_, between)| {
                            !between.iter().any(|&b| self.is_def(b, "procedure body"))
                        })
                        .map(|(n, _)| n)
                        .collect(),
                };
                candidates
                    .into_iter()
                    .filter(|&n| self.matches(n, alt))
                    .count()
            }
            (None, Some(words)) => {
                let k = words.len();
                let found = match how {
                    How::Immediately => self.rhs(i).into_iter().any(|c| {
                        self.nodes[c].kind == Kind::Token
                            && k == 1
                            && self.tokens[self.nodes[c].lo].eq_ignore_ascii_case(&words[0])
                    }),
                    How::Any => !self.occurrences(i, words).is_empty(),
                    How::Simply => self.occurrences(i, words).into_iter().any(|s| {
                        !self
                            .covering(i, s, s + k)
                            .iter()
                            .any(|&n| self.is_def(n, outer))
                    }),
                    How::Directly => self.occurrences(i, words).into_iter().any(|s| {
                        !self
                            .covering(i, s, s + k)
                            .iter()
                            .any(|&n| self.is_def(n, "procedure body"))
                    }),
                };
                usize::from(found)
            }
            (None, None) => 0,
        }
    }
}
