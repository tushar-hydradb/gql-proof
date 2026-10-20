//! ISO/IEC 39075's optional features: the map `tools/conformance.py` extracts from the
//! standard, claims over it, and the conformance rules of unclaimed features compiled into a
//! `refine::Rule`.
//!
//! A conformance rule is a tree pattern in the vocabulary of 5.3.2.1: contain, immediately,
//! simply and directly contain, "is", followed by. It is compiled into a tree automaton with
//! both passes `refine` offers:
//! - an outer definition sends a flag down to the part of its subtree the relation reaches
//!   (all of it for "contains", its own right hand side for "immediately", up to the next
//!   instance of either side for "simply", up to the next `<procedure body>` for "directly"),
//!   and a matching inner definition sends a hit back up. Both live only under an actual
//!   outer instance, so copies of definitions appear only where a rule can apply
//! - keyword phrases are matched over the yield, with facts for "ends with the first j
//!   keywords", "starts with the last ones" and "is exactly a middle piece", again only inside
//!   the definition that asks
//! - "is" and "followed by" read the yield's shape: a single non-empty child, or exactly two
//!
//! Nothing here is trusted. `verify` reads each pattern again straight from 5.3.2.1, and a test
//! keeps the two in agreement.

use crate::MatchModeDefault;
use crate::cfg::{Cfg, Lit, NtId, Sym};
use crate::leaf::StubProvider;
use crate::purdom::{Analysis, Config, Generator, Length};
use crate::refine::{FIRST_FREE_FACT, Fact, Item, Node, Rule, State, all_rules, refine};
use crate::verify::{Plain, Verifier};
use anyhow::{Context, Result, bail};
use fixedbitset::FixedBitSet;
use serde::Deserialize;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::Path;

/// Where `just features` writes the map.
pub const CONFORMANCE_JSON: &str = "grammar/conformance.json";

#[derive(Debug, Clone, Deserialize)]
pub struct Conformance {
    pub features: Vec<Feature>,
    pub statements: Vec<Statement>,
    /// Rules every claim is under: syntax ISO uses as a specification device, and one more.
    pub devices: Vec<Device>,
    /// Table 10: claiming the first implies the second.
    pub implies: Vec<[String; 2]>,
    /// 24.2 and 24.3.
    pub claim_rules: Vec<ClaimConstraint>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Feature {
    pub code: String,
    pub name: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Statement {
    pub feature: String,
    pub subclause: Option<String>,
    pub section: Option<String>,
    pub rule: Option<String>,
    pub origin: String,
    /// `pattern`, or who enforces it instead: `typed`, `context`, `structural`, `lexical`,
    /// `semantic`.
    pub kind: String,
    #[serde(default)]
    pub forbid: Vec<Pattern>,
    pub owner: Option<String>,
    /// "Immediately contains" read through single-item rules, because as written it can
    /// match nothing: each the chain of definitions it now goes through.
    #[serde(default)]
    pub readings: Vec<String>,
    /// Such containments with no single chain to read them through, left as written.
    #[serde(default)]
    pub vacuous: Vec<String>,
    pub sha256: String,
}

impl Statement {
    pub fn cite(&self) -> String {
        let mut out = format!(
            "{} {}",
            self.feature,
            self.subclause.as_deref().unwrap_or("?")
        );
        if self.section.as_deref() == Some("Conformance Rules") {
            out.push_str(" CR");
        }
        if let Some(rule) = &self.rule {
            out.push_str(&format!(" {rule}"));
        }
        out
    }
}

#[derive(Debug, Clone, Deserialize)]
pub struct Device {
    pub subclause: Option<String>,
    pub rule: Option<String>,
    pub kind: String,
    #[serde(default)]
    pub forbid: Vec<Pattern>,
    #[serde(default)]
    pub readings: Vec<String>,
    pub sha256: String,
}

/// If any of `if_any` is claimed (always, when absent), all of one of `one_of` is.
#[derive(Debug, Clone, Deserialize)]
pub struct ClaimConstraint {
    pub if_any: Option<Vec<String>>,
    pub one_of: Vec<Vec<String>>,
}

/// An instance of `nt` (or, with no `nt`, a keyword phrase), whose yield contains `words`
/// when given, and that meets every condition.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Deserialize)]
pub struct Pattern {
    pub nt: Option<String>,
    pub words: Option<Vec<String>>,
    pub conds: Vec<Cond>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Cond {
    Contains(Contains),
    Is(Is),
    /// Is one of these pairs, the first followed by the second.
    FollowedBy(Vec<[String; 2]>),
    Parent(Parent),
    /// Holds an instance of `first` followed by one of `then`, at the same depth of graph
    /// pattern matching, with no instance of any of `unless` between them (16.7 CR 14).
    Juxtaposed(Juxtaposed),
    /// Is not immediately preceded and followed by an instance of `by` (16.7 CR 15).
    Unflanked(Unflanked),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Deserialize)]
pub struct Juxtaposed {
    pub first: String,
    pub then: String,
    pub unless: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Deserialize)]
pub struct Unflanked {
    pub by: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Deserialize)]
pub struct Contains {
    pub how: How,
    pub negated: bool,
    pub exactly_one: bool,
    pub any: Vec<Pattern>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum How {
    Any,
    Simply,
    Immediately,
    Directly,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Deserialize)]
pub struct Is {
    pub negated: bool,
    pub any: Vec<Pattern>,
}

/// Immediately contained in an instance of `nt` (or not, when negated).
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Deserialize)]
pub struct Parent {
    pub negated: bool,
    pub how: How,
    pub nt: String,
}

impl Conformance {
    pub fn load(path: impl AsRef<Path>) -> Result<Conformance> {
        let path = path.as_ref();
        let text = std::fs::read_to_string(path)
            .with_context(|| format!("{} is missing, run `just features`", path.display()))?;
        serde_json::from_str(&text).with_context(|| format!("reading {}", path.display()))
    }

    pub fn codes(&self) -> BTreeSet<&str> {
        self.features.iter().map(|f| f.code.as_str()).collect()
    }

    /// The rules a claim leaves in force: every pattern of every unclaimed feature, and the
    /// devices.
    pub fn forbidden(&self, claim: &Claim) -> Vec<Forbidden> {
        let mut out: Vec<Forbidden> = self
            .devices
            .iter()
            .filter(|d| d.kind == "pattern")
            .map(|d| Forbidden {
                label: format!(
                    "{} CR {} (every claim)",
                    d.subclause.as_deref().unwrap_or("?"),
                    d.rule.as_deref().unwrap_or("?")
                ),
                feature: None,
                patterns: d.forbid.clone(),
                readings: d.readings.clone(),
            })
            .collect();
        out.extend(
            self.statements
                .iter()
                .filter(|s| s.kind == "pattern" && !claim.features.contains(&s.feature))
                .map(|s| Forbidden {
                    label: s.cite(),
                    feature: Some(s.feature.clone()),
                    patterns: s.forbid.clone(),
                    readings: s.readings.clone(),
                }),
        );
        out.extend(claim.deviations.iter().map(|d| Forbidden {
            label: format!("deviation {}", d.text),
            feature: None,
            patterns: vec![d.pattern.clone()],
            readings: Vec::new(),
        }));
        out
    }

    /// The statements of unclaimed features that something other than the grammar enforces.
    pub fn unenforced<'a>(&'a self, claim: &Claim) -> Vec<&'a Statement> {
        self.statements
            .iter()
            .filter(|s| s.kind != "pattern" && !claim.features.contains(&s.feature))
            .collect()
    }
}

/// One rule in force: a tree must contain no match of any of its patterns.
#[derive(Debug, Clone)]
pub struct Forbidden {
    pub label: String,
    pub feature: Option<String>,
    pub patterns: Vec<Pattern>,
    /// The readings through single-item rules its patterns rely on.
    pub readings: Vec<String>,
}

/// A set of claimed features, closed under table 10, and the mandatory syntax the
/// implementation leaves out.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Claim {
    pub features: BTreeSet<String>,
    pub deviations: Vec<Deviation>,
}

/// Mandatory syntax an implementation does not support, stated in its claim: a whole
/// definition (`-<name>`) or a keyword phrase (`-'KEYWORDS'`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Deviation {
    pub text: String,
    pub pattern: Pattern,
}

impl Deviation {
    fn parse(text: &str) -> Result<Deviation> {
        let pattern = if let Some(name) = text.strip_prefix('<').and_then(|t| t.strip_suffix('>')) {
            Pattern {
                nt: Some(name.to_string()),
                words: None,
                conds: Vec::new(),
            }
        } else if let Some(words) = text.strip_prefix('\'').and_then(|t| t.strip_suffix('\'')) {
            Pattern {
                nt: None,
                words: Some(words.split_whitespace().map(str::to_uppercase).collect()),
                conds: Vec::new(),
            }
        } else {
            bail!("a deviation is -<definition> or -'KEYWORDS', got -{text}");
        };
        Ok(Deviation {
            text: text.to_string(),
            pattern,
        })
    }
}

impl Claim {
    /// `all`, `none` (only what 24.2 requires: its first option), or a file: feature codes,
    /// and lines `-<definition>` or `-'KEYWORDS'` for mandatory syntax left out, `#` starting
    /// a comment. Deviation names are checked against the grammar when the claim is compiled.
    pub fn parse(spec: &str, conf: &Conformance) -> Result<Claim> {
        let codes = conf.codes();
        let mut deviations = Vec::new();
        let named: BTreeSet<String> = match spec {
            "all" => codes.iter().map(|c| c.to_string()).collect(),
            "none" => conf
                .claim_rules
                .iter()
                .filter(|r| r.if_any.is_none())
                .flat_map(|r| r.one_of[0].clone())
                .collect(),
            path => {
                let text =
                    std::fs::read_to_string(path).with_context(|| format!("reading {path}"))?;
                let mut named = BTreeSet::new();
                for line in text.lines() {
                    let line = line.split('#').next().unwrap_or("").trim();
                    if let Some(d) = line.strip_prefix('-') {
                        deviations.push(Deviation::parse(d.trim())?);
                    } else {
                        named.extend(line.split_whitespace().map(str::to_string));
                    }
                }
                named
            }
        };
        for c in &named {
            if !codes.contains(c.as_str()) {
                bail!("{c} is not a feature of ISO/IEC 39075");
            }
        }
        let mut claim = Claim::closed(named, conf)?;
        claim.deviations = deviations;
        Ok(claim)
    }

    /// The claim closed under table 10, checked against 24.2 and 24.3.
    pub fn closed(mut features: BTreeSet<String>, conf: &Conformance) -> Result<Claim> {
        loop {
            let more: Vec<String> = conf
                .implies
                .iter()
                .filter(|[a, b]| features.contains(a) && !features.contains(b))
                .map(|[_, b]| b.clone())
                .collect();
            if more.is_empty() {
                break;
            }
            features.extend(more);
        }
        for rule in &conf.claim_rules {
            let applies = rule
                .if_any
                .as_ref()
                .is_none_or(|a| a.iter().any(|c| features.contains(c)));
            let met = rule
                .one_of
                .iter()
                .any(|set| set.iter().all(|c| features.contains(c)));
            if applies && !met {
                let need: Vec<String> = rule.one_of.iter().map(|s| s.join("+")).collect();
                match &rule.if_any {
                    None => bail!("24.2: a claim needs one of {}", need.join(", ")),
                    Some(a) => bail!(
                        "24.3: a claim to any of {} needs one of {}",
                        a.join(", "),
                        need.join(", ")
                    ),
                }
            }
        }
        Ok(Claim {
            features,
            deviations: Vec::new(),
        })
    }
}

/// The shortest tree from `start` that keeps the syntax rules (with this ID086) and every rule
/// in `forbidden`, and matches `required`: with its rendering. `None` if there is none.
pub fn witness(
    base: &Cfg,
    start: NtId,
    id086: MatchModeDefault,
    seed: u64,
    forbidden: &[Forbidden],
    required: &Pattern,
) -> Result<Option<(Plain, String)>> {
    let mut rules = all_rules(id086);
    rules.push(Box::new(ClaimRules::new(
        base,
        start,
        forbidden,
        std::slice::from_ref(required),
    )?));
    // Refinement fails when the rules reject every tree.
    let Ok(refined) = refine(base, &rules, start) else {
        return Ok(None);
    };
    let analysis = Analysis::new(&refined.cfg, &StubProvider);
    let config = Config {
        seed,
        max_depth: analysis.reference_height(refined.start),
        length: Length::Unbounded,
    };
    Ok(Generator::new(&analysis, config, StubProvider)
        .shortest(refined.start)
        .map(|t| (t.export(&refined.cfg), t.render(&refined.cfg))))
}

/// What the search for a negative test finds.
pub enum Negative {
    /// A query that breaks the rule and no rule of another feature the claim leaves out.
    Query(Plain, String),
    /// None. The other unclaimed features the shortest query breaking the rule brings in.
    Needs(BTreeSet<String>),
}

/// The shortest query breaking `pattern`, one of statement `s`'s, that breaks no rule of
/// another unclaimed feature, as `verifier` reads them: it checks the syntax rules and the
/// rules `claim` leaves in force. Tried first with only what every claim forbids, which is
/// usually enough, then with every other unclaimed feature forbidden too.
#[allow(clippy::too_many_arguments)]
pub fn negative(
    base: &Cfg,
    start: NtId,
    id086: MatchModeDefault,
    seed: u64,
    conf: &Conformance,
    claim: &Claim,
    verifier: &Verifier,
    s: &Statement,
    pattern: &Pattern,
) -> Result<Negative> {
    let own: BTreeSet<String> = conf
        .statements
        .iter()
        .filter(|t| t.feature == s.feature)
        .map(Statement::cite)
        .collect();
    // What every claim forbids, and what this implementation leaves out.
    let always = conf.forbidden(&Claim {
        features: conf.codes().into_iter().map(str::to_string).collect(),
        deviations: claim.deviations.clone(),
    });
    let others: Vec<Forbidden> = conf
        .forbidden(claim)
        .into_iter()
        .filter(|f| f.feature.as_ref() != Some(&s.feature))
        .collect();
    let mut needs = BTreeSet::new();
    for forbidden in [&always, &others] {
        let Some((tree, sentence)) = witness(base, start, id086, seed, forbidden, pattern)? else {
            continue;
        };
        let violations = verifier.verify(&tree, &sentence);
        let own_only = violations
            .iter()
            .all(|v| v.rule == "conformance rule" && own.contains(&v.detail));
        if own_only && violations.iter().any(|v| v.detail == s.cite()) {
            return Ok(Negative::Query(tree, sentence));
        }
        for f in verifier.broken_conformance(&tree) {
            if let Some(code) = &f.feature
                && *code != s.feature
            {
                needs.insert(code.clone());
            }
        }
    }
    Ok(Negative::Needs(needs))
}

/// A keyword phrase matched over the yield, for one definition that asks (or everywhere).
struct PhraseUse {
    words: Vec<String>,
    /// The definition whose subtree is searched and how; `None` searches every tree.
    owner: Option<(String, How)>,
    scope: Fact,
    found: Fact,
    /// `starts[i]`: the yield starts with the words from `i` on.
    starts: BTreeMap<usize, Fact>,
    /// `ends[j]`: the yield ends with the first `j` words.
    ends: BTreeMap<usize, Fact>,
    /// `middle[(i, j)]`: the yield is exactly words `i..j`, neither end included.
    middle: BTreeMap<(usize, usize), Fact>,
    /// Definitions whose yield can hold one of the words.
    reach: FixedBitSet,
}

/// One alternative of a containment condition with a definition inside: flag down, hits up.
struct HitUse {
    owner: usize,
    how: How,
    alt: usize,
    flag: Fact,
    hit: Fact,
    /// Two or more hits, kept only for "exactly one".
    hits2: Option<Fact>,
    /// Definitions that can be or hold the alternative's definition.
    reach: FixedBitSet,
    /// The owner is a rule on its own, "no X contains Q" with Q a bare definition: a Q under
    /// the flag breaks it whatever else holds, so it is rejected right there.
    immediate: bool,
}

enum Compiled {
    Contains {
        negated: bool,
        exactly_one: bool,
        hits: Vec<usize>,
        phrases: Vec<usize>,
        tokens: Vec<String>,
    },
    Is {
        negated: bool,
        nts: Vec<String>,
        phrases: Vec<usize>,
    },
    FollowedBy(Vec<[String; 2]>),
    Parent {
        negated: bool,
        fact: Fact,
    },
}

struct PNode {
    nt: Option<String>,
    words: Option<usize>,
    conds: Vec<Compiled>,
}

/// The conformance rules a claim leaves in force, as one automaton.
pub struct ClaimRules {
    nodes: Vec<PNode>,
    /// Patterns that must match nowhere, by definition.
    tops: HashMap<String, Vec<usize>>,
    /// Patterns one of which must match somewhere: a negative test's feature. With the fact
    /// that one has, and the start definition, where it is checked.
    required: Vec<usize>,
    required_phrases: Vec<usize>,
    matched: Fact,
    start: String,
    /// The hit uses each pattern is an alternative of: it is looked for where their flags are.
    uses: Vec<Vec<usize>>,
    hits: Vec<HitUse>,
    phrases: Vec<PhraseUse>,
    empty: Fact,
    is: BTreeMap<String, Fact>,
    pairs: BTreeMap<String, Fact>,
    tokens: BTreeMap<String, Fact>,
    parents: BTreeMap<String, Fact>,
    juxta: Vec<JuxtaUse>,
    flank: Vec<FlankUse>,
    labels: Vec<(Fact, String)>,
    ids: HashMap<String, NtId>,
    cite: String,
}

/// "Between any two `first` and `then` in an `owner` there is an `unless`": searched inside
/// each owner at its depth of graph pattern matching, with facts for "ends with a `first` and
/// nothing that breaks since", "starts with nothing that breaks, then a `then`", and "holds
/// nothing that breaks at all".
struct JuxtaUse {
    owner: String,
    first: String,
    then: String,
    unless: Vec<String>,
    required: bool,
    scope: Fact,
    ends: Fact,
    starts: Fact,
    clean: Fact,
    /// Definitions that can hold a `first` or `then` at the same depth: the scope goes no
    /// further, and anything else counts as breaking.
    reach: FixedBitSet,
}

/// "Every `nt` is immediately preceded and followed by a `by`", with facts for the yield
/// starting and ending with each: `[starts nt, ends nt, starts by, ends by]`. An `nt` at the
/// edge of a yield waits for the node that has its neighbour.
///
/// With an `owner`, the facts live only inside one: the nearest definition every `nt` is
/// inside, at whose edges the grammar never puts a `by`, so an `nt` at an owner's edge is
/// decided there. Without one, they live everywhere and the start decides.
struct FlankUse {
    nt: String,
    by: String,
    required: bool,
    facts: [Fact; 4],
    owner: Option<(String, Fact)>,
    reach: FixedBitSet,
}

struct Builder<'c> {
    cfg: &'c Cfg,
    reach: Vec<FixedBitSet>,
    /// Definitions forbidden outright.
    gone: FixedBitSet,
    start: NtId,
    next: Fact,
    rules: ClaimRules,
    interned: HashMap<Pattern, usize>,
}

/// Definitions a set of patterns forbids outright.
fn outright(cfg: &Cfg, patterns: &[Pattern]) -> Result<FixedBitSet> {
    let mut gone = FixedBitSet::with_capacity(cfg.nts.len());
    for p in patterns {
        if let (Some(nt), None, true) = (&p.nt, &p.words, p.conds.is_empty()) {
            gone.insert(cfg.require(nt)? as usize);
        }
    }
    Ok(gone)
}

/// Where a keyword phrase can be in the yield of a definition, none in `gone` used.
struct Places {
    /// Some production can lay the whole phrase across its own right hand side: these are
    /// the lowest definitions an occurrence can have.
    anchor: FixedBitSet,
    /// Can hold the phrase, or a piece of one at an end of the yield: everywhere a search
    /// for it has to look.
    part: FixedBitSet,
}

/// Whether a production uses no definition in `gone`.
fn usable(cfg: &Cfg, gone: &FixedBitSet, p: u32) -> bool {
    cfg.prod(p)
        .rhs
        .iter()
        .all(|&s| !matches!(s, Sym::Nt(c) if gone.contains(c as usize)))
}

/// Definitions that can derive nothing, none in `gone` used.
fn nullable(cfg: &Cfg, gone: &FixedBitSet) -> FixedBitSet {
    let mut nullable = FixedBitSet::with_capacity(cfg.nts.len());
    let mut changed = true;
    while changed {
        changed = false;
        for (x, nt) in cfg.nts.iter().enumerate() {
            if gone.contains(x) || nullable.contains(x) {
                continue;
            }
            let empty = nt.prods.iter().any(|&p| {
                usable(cfg, gone, p)
                    && cfg
                        .prod(p)
                        .rhs
                        .iter()
                        .all(|&s| matches!(s, Sym::Nt(c) if nullable.contains(c as usize)))
            });
            if empty {
                nullable.insert(x);
                changed = true;
            }
        }
    }
    nullable
}

/// Per definition, the definitions its yield can start with and end with, itself included.
fn edges(cfg: &Cfg, gone: &FixedBitSet) -> (Vec<FixedBitSet>, Vec<FixedBitSet>) {
    let n = cfg.nts.len();
    let empty = nullable(cfg, gone);
    let mut first = vec![FixedBitSet::with_capacity(n); n];
    let mut last = vec![FixedBitSet::with_capacity(n); n];
    for x in 0..n {
        first[x].insert(x);
        last[x].insert(x);
    }
    let mut changed = true;
    while changed {
        changed = false;
        for (x, nt) in cfg.nts.iter().enumerate() {
            for &p in nt.prods.iter().filter(|&&p| usable(cfg, gone, p)) {
                let rhs = &cfg.prod(p).rhs;
                for (side, order) in [(&mut first, false), (&mut last, true)] {
                    let syms: Vec<Sym> = if order {
                        rhs.iter().rev().copied().collect()
                    } else {
                        rhs.clone()
                    };
                    for s in syms {
                        let Sym::Nt(c) = s else { break };
                        let c = c as usize;
                        let add = side[c].clone();
                        let before = side[x].count_ones(..);
                        side[x].union_with(&add);
                        changed |= side[x].count_ones(..) != before;
                        if !empty.contains(c) {
                            break;
                        }
                    }
                }
            }
        }
    }
    (first, last)
}

fn places(cfg: &Cfg, gone: &FixedBitSet, words: &[String]) -> Places {
    let (n, k) = (cfg.nts.len(), words.len());
    let usable = |p: u32| usable(cfg, gone, p);
    let lit = |s: Sym, j: usize| match s {
        Sym::Lit(l) => match &cfg.lits[l as usize] {
            Lit::Kw(t) | Lit::Term(t) => t.eq_ignore_ascii_case(&words[j]),
            Lit::Opaque(_) => false,
        },
        Sym::Nt(_) => false,
    };
    let nullable = nullable(cfg, gone);
    let mut changed;
    // Per definition: ends with the first j words, starts with the words from i, is exactly
    // words i..j (neither end), holds them all.
    let mut ends = vec![BTreeSet::new(); n];
    let mut starts = vec![BTreeSet::new(); n];
    let mut middle = vec![BTreeSet::new(); n];
    let mut contain = FixedBitSet::with_capacity(n);
    let mut anchor = FixedBitSet::with_capacity(n);
    changed = true;
    while changed {
        changed = false;
        for (x, nt) in cfg.nts.iter().enumerate() {
            if gone.contains(x) {
                continue;
            }
            for &p in nt.prods.iter().filter(|&&p| usable(p)) {
                let (mut open, mut found, mut holds) = (BTreeSet::new(), false, false);
                let mut front: BTreeSet<(usize, usize)> = (1..k).map(|i| (i, i)).collect();
                let mut starting = BTreeSet::new();
                for &sym in &cfg.prod(p).rhs {
                    let mut next = BTreeSet::new();
                    let mut fr = BTreeSet::new();
                    match sym {
                        Sym::Lit(_) => {
                            for j in open.iter().copied().chain([0]) {
                                if lit(sym, j) {
                                    if j + 1 == k {
                                        found = true;
                                    } else {
                                        next.insert(j + 1);
                                    }
                                }
                            }
                            for &(i, m) in &front {
                                if lit(sym, m) {
                                    if m + 1 == k {
                                        starting.insert(i);
                                    } else {
                                        fr.insert((i, m + 1));
                                    }
                                }
                            }
                        }
                        Sym::Nt(c) => {
                            let c = c as usize;
                            holds |= contain.contains(c);
                            for &j in &open {
                                found |= starts[c].contains(&j);
                                next.extend(
                                    middle[c].iter().filter(|&&(a, _)| a == j).map(|&(_, b)| b),
                                );
                            }
                            next.extend(ends[c].iter().copied());
                            for &(i, m) in &front {
                                if starts[c].contains(&m) {
                                    starting.insert(i);
                                }
                                fr.extend(
                                    middle[c]
                                        .iter()
                                        .filter(|&&(a, _)| a == m)
                                        .map(|&(_, b)| (i, b)),
                                );
                            }
                            if nullable.contains(c) {
                                next.extend(open.iter().copied());
                                fr.extend(front.iter().copied());
                            }
                        }
                    }
                    open = next;
                    front = fr;
                }
                let before = (
                    ends[x].len(),
                    starts[x].len(),
                    middle[x].len(),
                    contain.contains(x),
                    anchor.contains(x),
                );
                ends[x].extend(open);
                starts[x].extend(starting);
                middle[x].extend(front.into_iter().filter(|&(i, m)| i < m));
                if found {
                    anchor.insert(x);
                }
                if found || holds {
                    contain.insert(x);
                }
                changed |= before
                    != (
                        ends[x].len(),
                        starts[x].len(),
                        middle[x].len(),
                        contain.contains(x),
                        anchor.contains(x),
                    );
            }
        }
    }
    let mut part = contain;
    for x in 0..n {
        if !ends[x].is_empty() || !starts[x].is_empty() || !middle[x].is_empty() {
            part.insert(x);
        }
    }
    Places { anchor, part }
}

/// The phrase of a pattern that says no more than "an X whose yield holds this phrase".
fn phrase_only(p: &Pattern) -> Option<&[String]> {
    match (&p.nt, &p.words, p.conds.as_slice()) {
        (Some(_), Some(w), []) => Some(w),
        (Some(_), None, [Cond::Contains(c)])
            if !c.negated && !c.exactly_one && c.how == How::Any && c.any.len() == 1 =>
        {
            match &c.any[0] {
                Pattern {
                    nt: None,
                    words: Some(w),
                    conds,
                } if conds.is_empty() => Some(w),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Definitions some tree from `start` can hold without passing through `avoid`.
fn reachable_avoiding(cfg: &Cfg, start: NtId, avoid: &FixedBitSet) -> FixedBitSet {
    let mut seen = FixedBitSet::with_capacity(cfg.nts.len());
    let mut todo = vec![start as usize];
    while let Some(x) = todo.pop() {
        if avoid.contains(x) || seen.contains(x) {
            continue;
        }
        seen.insert(x);
        for &p in &cfg.nts[x].prods {
            for &sym in &cfg.prod(p).rhs {
                if let Sym::Nt(c) = sym {
                    todo.push(c as usize);
                }
            }
        }
    }
    seen
}

/// Rewrites "X contains Q" (or "simply contains", when no Q can hold another) into just "Q"
/// wherever every Q a tree from `start` can hold lies inside an X: the two forbid exactly the
/// same trees. Repeated until nothing changes, since every pattern that becomes a whole
/// definition removes that definition from the grammar for the next round. Returns the
/// patterns and a note per rewrite.
pub fn collapse(
    cfg: &Cfg,
    start: NtId,
    patterns: &[Pattern],
) -> Result<(Vec<Pattern>, Vec<String>)> {
    let mut pats = patterns.to_vec();
    let mut notes = Vec::new();
    loop {
        let gone = outright(cfg, &pats)?;
        let reach = closures(cfg, &gone);
        let mut changed = false;
        let mut next = Vec::new();
        for p in pats {
            let (Some(x), None, [Cond::Contains(c)]) = (&p.nt, &p.words, p.conds.as_slice()) else {
                next.push(p);
                continue;
            };
            if c.negated || c.exactly_one || !matches!(c.how, How::Any | How::Simply) {
                next.push(p);
                continue;
            }
            let mut avoid = gone.clone();
            avoid.insert(cfg.require(x)? as usize);
            let inside_only = reachable_avoiding(cfg, start, &avoid);
            let (mut moved, mut kept) = (Vec::new(), Vec::new());
            for alt in &c.any {
                let q = match &alt.nt {
                    Some(q) => cfg.require(q)? as usize,
                    None => {
                        kept.push(alt.clone());
                        continue;
                    }
                };
                // A Q inside another Q would let "simply" skip the inner one.
                let nests = cfg.nts[q].prods.iter().any(|&pr| {
                    cfg.prod(pr)
                        .rhs
                        .iter()
                        .any(|&s| matches!(s, Sym::Nt(c) if reach[c as usize].contains(q)))
                });
                if !inside_only.contains(q) && (c.how == How::Any || !nests) {
                    moved.push(alt.clone());
                } else {
                    kept.push(alt.clone());
                }
            }
            if moved.is_empty() {
                next.push(p);
                continue;
            }
            changed = true;
            let anywhere = reachable_avoiding(cfg, start, &gone);
            for alt in &moved {
                let q = alt.nt.as_deref().unwrap_or("?");
                let why = if anywhere.contains(cfg.require(q)? as usize) {
                    format!("every one is inside a <{x}>")
                } else {
                    "none can occur under the other rules anyway".to_string()
                };
                notes.push(format!("<{x}> containing <{q}> is forbidding <{q}>: {why}"));
            }
            next.extend(moved);
            if !kept.is_empty() {
                let mut c = c.clone();
                c.any = kept;
                next.push(Pattern {
                    nt: p.nt.clone(),
                    words: None,
                    conds: vec![Cond::Contains(c)],
                });
            }
        }
        // "X contains W" for a keyword phrase W and several X: when every place W can sit
        // lowest is inside one of those X, together they forbid W anywhere, which needs no
        // search scope.
        let mut by_phrase: BTreeMap<Vec<String>, Vec<usize>> = BTreeMap::new();
        for (i, p) in next.iter().enumerate() {
            if let Some(w) = phrase_only(p) {
                by_phrase.entry(w.to_vec()).or_default().push(i);
            }
        }
        let mut dropped = BTreeSet::new();
        for (w, idxs) in by_phrase {
            let mut avoid = gone.clone();
            for &i in &idxs {
                avoid.insert(cfg.require(next[i].nt.as_deref().unwrap_or_default())? as usize);
            }
            let inside_only = reachable_avoiding(cfg, start, &avoid);
            if places(cfg, &gone, &w)
                .anchor
                .ones()
                .any(|a| inside_only.contains(a))
            {
                continue;
            }
            let owners: Vec<String> = idxs
                .iter()
                .map(|&i| format!("<{}>", next[i].nt.as_deref().unwrap_or("?")))
                .collect();
            notes.push(format!(
                "{} containing {} is forbidding {} anywhere: it can occur only inside one of them",
                owners.join(", "),
                w.join(" "),
                w.join(" ")
            ));
            dropped.extend(idxs);
            changed = true;
            next.push(Pattern {
                nt: None,
                words: Some(w),
                conds: Vec::new(),
            });
        }
        pats = next
            .into_iter()
            .enumerate()
            .filter(|(i, _)| !dropped.contains(i))
            .map(|(_, p)| p)
            .collect();
        if !changed {
            return Ok((pats, notes));
        }
    }
}

impl ClaimRules {
    /// Compiles `forbidden` against the grammar its trees come from, for trees from `start`.
    /// With `required`, every tree must also match one of those patterns somewhere.
    pub fn new(
        cfg: &Cfg,
        start: NtId,
        forbidden: &[Forbidden],
        required: &[Pattern],
    ) -> Result<ClaimRules> {
        let all: Vec<Pattern> = forbidden.iter().flat_map(|f| f.patterns.clone()).collect();
        let (patterns, _) = collapse(cfg, start, &all)?;
        // Definitions forbidden outright never occur, so nothing is looked for through them.
        let gone = outright(cfg, &patterns)?;
        let reach = closures(cfg, &gone);
        let mut b = Builder {
            cfg,
            reach,
            gone,
            start,
            next: FIRST_FREE_FACT,
            rules: ClaimRules {
                nodes: Vec::new(),
                tops: HashMap::new(),
                required: Vec::new(),
                required_phrases: Vec::new(),
                matched: 0,
                start: cfg.base(start).to_string(),
                uses: Vec::new(),
                hits: Vec::new(),
                phrases: Vec::new(),
                empty: 0,
                is: BTreeMap::new(),
                pairs: BTreeMap::new(),
                tokens: BTreeMap::new(),
                parents: BTreeMap::new(),
                juxta: Vec::new(),
                flank: Vec::new(),
                labels: Vec::new(),
                ids: cfg
                    .nts
                    .iter()
                    .enumerate()
                    .map(|(i, nt)| (nt.base.clone(), i as NtId))
                    .collect(),
                cite: format!("{} conformance rules in force", forbidden.len()),
            },
            interned: HashMap::new(),
        };
        b.rules.empty = b.fact("empty");
        for p in &patterns {
            if b.order(p, false)? {
                continue;
            }
            match (&p.nt, &p.words) {
                (None, Some(words)) if p.conds.is_empty() => {
                    b.phrase(words, None)?;
                }
                (Some(nt), _) => {
                    b.require(nt)?;
                    let id = b.node(p)?;
                    b.rules.tops.entry(nt.clone()).or_default().push(id);
                }
                _ => bail!("a pattern with neither a definition nor a phrase: {p:?}"),
            }
        }
        // Forbidden rules of the shape "no X contains Q", nothing more, reject at the Q.
        let tops: BTreeSet<usize> = b.rules.tops.values().flatten().copied().collect();
        for h in &mut b.rules.hits {
            let owner = &b.rules.nodes[h.owner];
            let alt = &b.rules.nodes[h.alt];
            let lone = matches!(
                owner.conds.as_slice(),
                [Compiled::Contains {
                    negated: false,
                    exactly_one: false,
                    ..
                }]
            );
            h.immediate = tops.contains(&h.owner)
                && lone
                && owner.words.is_none()
                && alt.conds.is_empty()
                && alt.words.is_none();
        }
        b.rules.matched = b.fact("required");
        for p in required {
            if b.order(p, true)? {
                continue;
            }
            match (&p.nt, &p.words) {
                (None, Some(words)) if p.conds.is_empty() => {
                    let u = b.phrase(words, None)?;
                    b.rules.required_phrases.push(u);
                }
                (Some(nt), _) => {
                    b.require(nt)?;
                    let id = b.node(p)?;
                    b.rules.required.push(id);
                }
                _ => bail!("a pattern with neither a definition nor a phrase: {p:?}"),
            }
        }
        Ok(b.rules)
    }
}

impl Builder<'_> {
    fn fact(&mut self, label: impl Into<String>) -> Fact {
        let f = self.next;
        self.next += 1;
        self.rules.labels.push((f, label.into()));
        f
    }

    fn require(&self, nt: &str) -> Result<NtId> {
        self.rules
            .ids
            .get(nt)
            .copied()
            .with_context(|| format!("<{nt}> is not a definition of the grammar"))
    }

    fn node(&mut self, p: &Pattern) -> Result<usize> {
        if let Some(&id) = self.interned.get(p) {
            return Ok(id);
        }
        let id = self.rules.nodes.len();
        self.interned.insert(p.clone(), id);
        self.rules.nodes.push(PNode {
            nt: p.nt.clone(),
            words: None,
            conds: Vec::new(),
        });
        self.rules.uses.push(Vec::new());
        let nt =
            p.nt.clone()
                .context("a pattern inside another needs a definition")?;
        let words = match &p.words {
            Some(w) => Some(self.phrase(w, Some((nt.clone(), How::Any)))?),
            None => None,
        };
        let mut conds = Vec::new();
        for c in &p.conds {
            conds.push(self.cond(id, &nt, c)?);
        }
        self.rules.nodes[id].words = words;
        self.rules.nodes[id].conds = conds;
        Ok(id)
    }

    fn cond(&mut self, owner: usize, nt: &str, c: &Cond) -> Result<Compiled> {
        Ok(match c {
            Cond::Contains(c) => {
                let (mut hits, mut phrases, mut tokens) = (Vec::new(), Vec::new(), Vec::new());
                for alt in &c.any {
                    match (&alt.nt, &alt.words) {
                        (None, Some(w)) if c.how == How::Immediately => {
                            if w.len() != 1 {
                                bail!("immediately containing a phrase of {} keywords", w.len());
                            }
                            tokens.push(w[0].to_uppercase());
                            let label = format!("token {}", w[0]);
                            if !self.rules.tokens.contains_key(&w[0].to_uppercase()) {
                                let f = self.fact(label);
                                self.rules.tokens.insert(w[0].to_uppercase(), f);
                            }
                        }
                        (None, Some(w)) => {
                            phrases.push(self.phrase(w, Some((nt.to_string(), c.how)))?)
                        }
                        (Some(a), _) => {
                            let target = self.require(a)?;
                            let alt_id = self.node(alt)?;
                            let mut reach = self.reaching(&[target]);
                            reach.intersect_with(&self.reach[self.require(nt)? as usize]);
                            let k = self.rules.hits.len();
                            let flag = self.fact(format!("in<{nt}>{k}"));
                            let hit = self.fact(format!("has<{a}>{k}"));
                            let hits2 = c.exactly_one.then(|| self.fact(format!("has2<{a}>{k}")));
                            self.rules.hits.push(HitUse {
                                owner,
                                how: c.how,
                                alt: alt_id,
                                flag,
                                hit,
                                hits2,
                                reach,
                                immediate: false,
                            });
                            self.rules.uses[alt_id].push(k);
                            hits.push(k);
                        }
                        (None, None) => bail!("an empty alternative"),
                    }
                }
                if c.exactly_one && (!phrases.is_empty() || !tokens.is_empty()) {
                    bail!("counting keyword phrases");
                }
                Compiled::Contains {
                    negated: c.negated,
                    exactly_one: c.exactly_one,
                    hits,
                    phrases,
                    tokens,
                }
            }
            Cond::Is(is) => {
                let (mut nts, mut phrases) = (Vec::new(), Vec::new());
                for alt in &is.any {
                    match (&alt.nt, &alt.words) {
                        (Some(a), None) if alt.conds.is_empty() => {
                            self.require(a)?;
                            if !self.rules.is.contains_key(a) {
                                let f = self.fact(format!("is<{a}>"));
                                self.rules.is.insert(a.clone(), f);
                            }
                            nts.push(a.clone());
                        }
                        // Reading: "is KEYWORDS" holds when the yield contains them, since
                        // `<for ordinality or offset> that is WITH OFFSET` is followed by a
                        // variable and would otherwise never match.
                        (None, Some(w)) => {
                            phrases.push(self.phrase(w, Some((nt.to_string(), How::Any)))?)
                        }
                        _ => bail!("<{nt}> is a pattern with conditions of its own"),
                    }
                }
                Compiled::Is {
                    negated: is.negated,
                    nts,
                    phrases,
                }
            }
            Cond::FollowedBy(pairs) => {
                for name in pairs.iter().flatten() {
                    self.require(name)?;
                    if !self.rules.pairs.contains_key(name) {
                        let f = self.fact(format!("just<{name}>"));
                        self.rules.pairs.insert(name.clone(), f);
                    }
                }
                Compiled::FollowedBy(pairs.clone())
            }
            Cond::Parent(p) => {
                if p.how != How::Immediately {
                    bail!("only an immediate parent is supported");
                }
                self.require(&p.nt)?;
                let fact = match self.rules.parents.get(&p.nt) {
                    Some(&f) => f,
                    None => {
                        let f = self.fact(format!("under<{}>", p.nt));
                        self.rules.parents.insert(p.nt.clone(), f);
                        f
                    }
                };
                Compiled::Parent {
                    negated: p.negated,
                    fact,
                }
            }
            Cond::Juxtaposed(_) | Cond::Unflanked(_) => {
                bail!("<{nt}>: an order condition only stands alone in a rule")
            }
        })
    }

    /// A rule that is only an order condition on one definition: compiled on its own, since
    /// whether it holds is known only once the neighbours are. `false` for any other rule.
    fn order(&mut self, p: &Pattern, required: bool) -> Result<bool> {
        let (Some(nt), None) = (&p.nt, &p.words) else {
            return Ok(false);
        };
        match p.conds.as_slice() {
            [Cond::Juxtaposed(j)] => {
                for name in [nt, &j.first, &j.then].into_iter().chain(&j.unless) {
                    self.require(name)?;
                }
                let k = self.rules.juxta.len();
                let scope = self.fact(format!("in<{nt}>j{k}"));
                let ends = self.fact(format!("ends<{}>j{k}", j.first));
                let starts = self.fact(format!("starts<{}>j{k}", j.then));
                let clean = self.fact(format!("clean j{k}"));
                let mut targets: Vec<&str> = vec![&j.first, &j.then];
                targets.extend(j.unless.iter().map(String::as_str));
                let reach = self.shallow(&targets)?;
                self.rules.juxta.push(JuxtaUse {
                    owner: nt.clone(),
                    first: j.first.clone(),
                    then: j.then.clone(),
                    unless: j.unless.clone(),
                    required,
                    scope,
                    ends,
                    starts,
                    clean,
                    reach,
                });
                Ok(true)
            }
            [Cond::Unflanked(u)] => {
                self.require(nt)?;
                self.require(&u.by)?;
                let k = self.rules.flank.len();
                let facts = [
                    self.fact(format!("starts<{nt}>f{k}")),
                    self.fact(format!("ends<{nt}>f{k}")),
                    self.fact(format!("starts<{}>f{k}", u.by)),
                    self.fact(format!("ends<{}>f{k}", u.by)),
                ];
                let owner = self
                    .flank_owner(nt, &u.by)?
                    .map(|o| (o.clone(), self.fact(format!("in<{o}>f{k}"))));
                let reach = self.shallow(&[nt, &u.by])?;
                self.rules.flank.push(FlankUse {
                    nt: nt.clone(),
                    by: u.by.clone(),
                    required,
                    facts,
                    owner,
                    reach,
                });
                Ok(true)
            }
            conds
                if conds
                    .iter()
                    .any(|c| matches!(c, Cond::Juxtaposed(_) | Cond::Unflanked(_))) =>
            {
                bail!("<{nt}>: an order condition only stands alone in a rule")
            }
            _ => Ok(false),
        }
    }

    /// Definitions that are or can hold one of `targets` at the same depth of graph pattern
    /// matching: never through a `<procedure body>` or a `<graph pattern>`.
    fn shallow(&self, targets: &[&str]) -> Result<FixedBitSet> {
        let mut deeper = self.gone.clone();
        for d in ["procedure body", "graph pattern"] {
            deeper.insert(self.require(d)? as usize);
        }
        let reach = closures(self.cfg, &deeper);
        let ids: Vec<usize> = targets
            .iter()
            .map(|t| self.require(t).map(|i| i as usize))
            .collect::<Result<_>>()?;
        let mut out = FixedBitSet::with_capacity(self.cfg.nts.len());
        for (x, r) in reach.iter().enumerate() {
            if ids.iter().any(|&i| r.contains(i)) {
                out.insert(x);
            }
        }
        Ok(out)
    }

    /// The nearest definition every `nt` from the start is inside and whose yield the grammar
    /// never puts next to a `by`'s: an `nt` at its edge has no `by` beside it, decided there.
    fn flank_owner(&self, nt: &str, by: &str) -> Result<Option<String>> {
        let (target, by) = (self.require(nt)? as usize, self.require(by)? as usize);
        let (first, last) = edges(self.cfg, &self.gone);
        let empty = nullable(self.cfg, &self.gone);
        let dominates = |d: usize, x: usize| {
            let mut avoid = self.gone.clone();
            avoid.insert(d);
            !reachable_avoiding(self.cfg, self.start, &avoid).contains(x)
        };
        // At the same depth: the target is reached from it without a nested procedure body or
        // graph pattern on the way.
        let mut deeper = self.gone.clone();
        for name in ["procedure body", "graph pattern"] {
            deeper.insert(self.require(name)? as usize);
        }
        let level = |d: usize| {
            let mut cut = deeper.clone();
            cut.set(d, false);
            reachable_avoiding(self.cfg, d as NtId, &cut).contains(target)
        };
        let mut dominators: Vec<usize> = (0..self.cfg.nts.len())
            .filter(|&d| d != target && !self.gone.contains(d))
            .filter(|&d| dominates(d, target) && level(d))
            .collect();
        // Dominators form a chain: the nearest has the most of the others above it.
        let above: Vec<usize> = dominators
            .iter()
            .map(|&d| {
                dominators
                    .iter()
                    .filter(|&&e| e != d && dominates(e, d))
                    .count()
            })
            .collect();
        let mut order: Vec<usize> = (0..dominators.len()).collect();
        order.sort_by_key(|&i| std::cmp::Reverse(above[i]));
        dominators = order.into_iter().map(|i| dominators[i]).collect();
        let beside = |d: usize| {
            self.cfg.prods.iter().any(|prod| {
                let rhs = &prod.rhs;
                (0..rhs.len()).any(|i| {
                    let Sym::Nt(a) = rhs[i] else { return false };
                    // every later position up to the next one that cannot be empty
                    for &s in &rhs[i + 1..] {
                        let Sym::Nt(b) = s else { return false };
                        let (a, b) = (a as usize, b as usize);
                        if (last[a].contains(by) && first[b].contains(d))
                            || (last[a].contains(d) && first[b].contains(by))
                        {
                            return true;
                        }
                        if !empty.contains(b) {
                            return false;
                        }
                    }
                    false
                })
            })
        };
        Ok(dominators
            .into_iter()
            .find(|&d| !beside(d))
            .map(|d| self.cfg.nts[d].base.clone()))
    }

    fn phrase(&mut self, words: &[String], owner: Option<(String, How)>) -> Result<usize> {
        let k = words.len();
        let id = self.rules.phrases.len();
        let name = words.join(" ");
        let scope = self.fact(format!("seek'{name}'{id}"));
        let found = self.fact(format!("'{name}'{id}"));
        let mut starts = BTreeMap::new();
        let mut ends = BTreeMap::new();
        let mut middle = BTreeMap::new();
        for i in 1..k {
            starts.insert(i, self.fact(format!("'{}..'{id}", words[i..].join(" "))));
            ends.insert(i, self.fact(format!("'..{}'{id}", words[..i].join(" "))));
            for j in i + 1..k {
                middle.insert(
                    (i, j),
                    self.fact(format!("'.{}.'{id}", words[i..j].join(" "))),
                );
            }
        }
        let mut reach = places(self.cfg, &self.gone, words).part;
        if let Some((nt, _)) = &owner {
            reach.intersect_with(&self.reach[self.require(nt)? as usize]);
        }
        self.rules.phrases.push(PhraseUse {
            words: words.iter().map(|w| w.to_uppercase()).collect(),
            owner,
            scope,
            found,
            starts,
            ends,
            middle,
            reach,
        });
        Ok(id)
    }

    /// Definitions that are or can hold one of `targets`.
    fn reaching(&self, targets: &[NtId]) -> FixedBitSet {
        let mut out = FixedBitSet::with_capacity(self.cfg.nts.len());
        for (nt, r) in self.reach.iter().enumerate() {
            if targets.iter().any(|&t| r.contains(t as usize)) {
                out.insert(nt);
            }
        }
        out
    }
}

/// Per nonterminal: the nonterminals it is or can derive, never through one in `gone`.
fn closures(cfg: &Cfg, gone: &FixedBitSet) -> Vec<FixedBitSet> {
    let n = cfg.nts.len();
    let mut reach = vec![FixedBitSet::with_capacity(n); n];
    for (x, nt) in cfg.nts.iter().enumerate() {
        if gone.contains(x) {
            continue;
        }
        reach[x].insert(x);
        for &p in &nt.prods {
            for &sym in &cfg.prod(p).rhs {
                if let Sym::Nt(c) = sym
                    && !gone.contains(c as usize)
                {
                    reach[x].insert(c as usize);
                }
            }
        }
    }
    let mut changed = true;
    while changed {
        changed = false;
        for x in 0..n {
            let kids: Vec<usize> = reach[x].ones().collect();
            for c in kids {
                if c == x {
                    continue;
                }
                let r = reach[c].clone();
                let before = reach[x].count_ones(..);
                reach[x].union_with(&r);
                changed |= before != reach[x].count_ones(..);
            }
        }
    }
    reach
}

/// A keyword phrase's facts about one node, as `PhraseUse` names them.
#[derive(Default)]
struct Scan {
    found: bool,
    starts: BTreeSet<usize>,
    ends: BTreeSet<usize>,
    middle: BTreeSet<(usize, usize)>,
}

/// What a step knows about one position: the child's synthesized state, or a token.
struct View<'a> {
    node: &'a Node<'a>,
    children: &'a [State],
    empty: Fact,
}

impl View<'_> {
    fn is_empty(&self, i: usize) -> bool {
        match self.node.items[i] {
            Item::Def(_) | Item::Group(_) => self.children[i].has(self.empty),
            Item::Token(_) | Item::Prose(_) => false,
        }
    }

    fn non_empty(&self) -> Vec<usize> {
        (0..self.node.items.len())
            .filter(|&i| !self.is_empty(i))
            .collect()
    }
}

impl ClaimRules {
    /// Where each order rule decides: "`<nt>` flanked by `<by>`, decided in `<owner>`".
    pub fn order_scopes(&self) -> Vec<String> {
        self.flank
            .iter()
            .map(|u| match &u.owner {
                Some((o, _)) => format!("<{}> flanked by <{}>: decided in each <{o}>", u.nt, u.by),
                None => format!("<{}> flanked by <{}>: decided at the start", u.nt, u.by),
            })
            .collect()
    }

    /// How many definitions each flag and phrase search can travel through, widest first: what
    /// drives the size of the refined grammar.
    pub fn spread(&self) -> Vec<(String, usize)> {
        let label = |f: Fact| {
            self.labels
                .iter()
                .find(|(g, _)| *g == f)
                .map_or(String::new(), |(_, l)| l.clone())
        };
        let mut out: Vec<(String, usize)> = self
            .hits
            .iter()
            .map(|h| (label(h.flag), h.reach.count_ones(..)))
            .chain(
                self.phrases
                    .iter()
                    .map(|u| (label(u.scope), u.reach.count_ones(..))),
            )
            .collect();
        out.sort_by(|a, b| b.1.cmp(&a.1));
        out
    }

    fn id(&self, item: Item) -> Option<NtId> {
        match item {
            Item::Def(n) | Item::Group(n) => self.ids.get(n).copied(),
            _ => None,
        }
    }

    fn active(&self, p: usize, inh: &State) -> bool {
        let top = self.nodes[p]
            .nt
            .as_ref()
            .is_some_and(|nt| self.tops.get(nt).is_some_and(|t| t.contains(&p)));
        top || self.required.contains(&p)
            || self.uses[p].iter().any(|&h| inh.has(self.hits[h].flag))
    }

    /// Does the hit stop at this node on its way up (and the flag on its way down)?
    fn blocks(&self, h: &HitUse, node: &Node) -> bool {
        if node.group {
            return false;
        }
        let owner = self.nodes[h.owner].nt.as_deref();
        let alt = self.nodes[h.alt].nt.as_deref();
        match h.how {
            How::Any => false,
            How::Immediately => true,
            How::Simply => Some(node.def) == owner || Some(node.def) == alt,
            How::Directly => node.def == "procedure body",
        }
    }

    fn phrase_blocks(&self, u: &PhraseUse, node: &Node) -> bool {
        match &u.owner {
            _ if node.group => false,
            Some((owner, How::Simply)) => node.def == owner,
            Some((_, How::Directly)) => node.def == "procedure body",
            _ => false,
        }
    }

    /// The phrase facts of a node from its positions.
    fn scan(&self, u: &PhraseUse, v: &View) -> Scan {
        let k = u.words.len();
        let mut found = false;
        // Matches of the first j words ending here.
        let mut open: BTreeSet<usize> = BTreeSet::new();
        // (i, m): everything so far is words i..m.
        let mut front: BTreeSet<(usize, usize)> = (1..k).map(|i| (i, i)).collect();
        let mut starts = BTreeSet::new();
        for (i, &item) in v.node.items.iter().enumerate() {
            match item {
                Item::Token(t) => {
                    let eq = |j: usize| u.words[j].eq_ignore_ascii_case(t);
                    let mut next = BTreeSet::new();
                    for j in open.iter().copied().chain([0]) {
                        if eq(j) {
                            if j + 1 == k {
                                found = true;
                            } else {
                                next.insert(j + 1);
                            }
                        }
                    }
                    open = next;
                    front = front
                        .into_iter()
                        .filter_map(|(a, m)| {
                            if !eq(m) {
                                None
                            } else if m + 1 == k {
                                starts.insert(a);
                                None
                            } else {
                                Some((a, m + 1))
                            }
                        })
                        .collect();
                }
                Item::Prose(_) => {
                    open.clear();
                    front.clear();
                }
                Item::Def(_) | Item::Group(_) => {
                    if v.is_empty(i) {
                        continue;
                    }
                    let c = &v.children[i];
                    found |= c.has(u.found);
                    let mut next = BTreeSet::new();
                    for &j in &open {
                        found |= u.starts.get(&j).is_some_and(|&f| c.has(f));
                        for (&(a, b), &f) in &u.middle {
                            if a == j && c.has(f) {
                                next.insert(b);
                            }
                        }
                    }
                    for (&j, &f) in &u.ends {
                        if c.has(f) {
                            next.insert(j);
                        }
                    }
                    open = next;
                    let mut fr = BTreeSet::new();
                    for (a, m) in front {
                        if u.starts.get(&m).is_some_and(|&f| c.has(f)) {
                            starts.insert(a);
                        }
                        for (&(x, y), &f) in &u.middle {
                            if x == m && c.has(f) {
                                fr.insert((a, y));
                            }
                        }
                    }
                    front = fr;
                }
            }
        }
        Scan {
            found,
            starts,
            ends: open,
            middle: front.into_iter().filter(|&(a, m)| a < m).collect(),
        }
    }

    /// The flattened shape of a node's right hand side, groups seen through: definition names,
    /// `#` for a token, `?` for a group of more than one thing.
    fn shape(&self, v: &View) -> Vec<String> {
        v.non_empty()
            .into_iter()
            .map(|i| match v.node.items[i] {
                Item::Def(n) => n.to_string(),
                Item::Group(_) => self
                    .pairs
                    .iter()
                    .find(|&(_, &f)| v.children[i].has(f))
                    .map_or("?".to_string(), |(n, _)| n.clone()),
                Item::Token(_) | Item::Prose(_) => "#".to_string(),
            })
            .collect()
    }

    fn is_here(&self, nt: &str, v: &View) -> bool {
        let fact = self.is[nt];
        if !v.node.group && v.node.def == nt {
            return true;
        }
        let non_empty = v.non_empty();
        non_empty.len() == 1
            && matches!(v.node.items[non_empty[0]], Item::Def(_) | Item::Group(_))
            && v.children[non_empty[0]].has(fact)
    }

    fn count(&self, h: &HitUse, v: &View) -> usize {
        let n: usize = v
            .children
            .iter()
            .map(|c| {
                if h.hits2.is_some_and(|f| c.has(f)) {
                    2
                } else {
                    usize::from(c.has(h.hit))
                }
            })
            .sum();
        n.min(2)
    }

    fn matches(&self, p: usize, inh: &State, v: &View, found: &[bool]) -> bool {
        let node = &self.nodes[p];
        if v.node.group || node.nt.as_deref() != Some(v.node.def) {
            return false;
        }
        if node.words.is_some_and(|u| !found[u]) {
            return false;
        }
        node.conds.iter().all(|c| match c {
            Compiled::Contains {
                negated,
                exactly_one,
                hits,
                phrases,
                tokens,
            } => {
                let n: usize = hits.iter().map(|&h| self.count(&self.hits[h], v)).sum();
                let held = if *exactly_one {
                    n == 1
                } else {
                    n > 0
                        || phrases.iter().any(|&u| found[u])
                        || tokens.iter().any(|t| {
                            v.node
                                .items
                                .iter()
                                .zip(v.children)
                                .any(|(&item, c)| match item {
                                    Item::Token(x) => x.eq_ignore_ascii_case(t),
                                    Item::Group(_) => c.has(self.tokens[t]),
                                    _ => false,
                                })
                        })
                };
                held != *negated
            }
            Compiled::Is {
                negated,
                nts,
                phrases,
            } => {
                let held =
                    nts.iter().any(|n| self.is_here(n, v)) || phrases.iter().any(|&u| found[u]);
                held != *negated
            }
            Compiled::FollowedBy(pairs) => {
                let shape = self.shape(v);
                pairs.iter().any(|[a, b]| shape == [a.as_str(), b.as_str()])
            }
            Compiled::Parent { negated, fact } => inh.has(*fact) != *negated,
        })
    }
}

impl ClaimRules {
    /// A juxtaposition's facts at one node, `(ends, starts, clean)`, and whether it is found
    /// here.
    fn juxtaposition(&self, u: &JuxtaUse, v: &View) -> (bool, bool, bool, bool) {
        let node = v.node;
        if !node.group && u.unless.iter().any(|x| x == node.def) {
            return (false, false, false, false);
        }
        if !node.group && (node.def == u.first || node.def == u.then) {
            return (node.def == u.first, node.def == u.then, false, false);
        }
        let (mut open, mut clean, mut starts, mut found) = (false, true, false, false);
        for (i, &item) in node.items.iter().enumerate() {
            let name = match item {
                Item::Def(n) | Item::Group(n) => n,
                Item::Token(_) | Item::Prose(_) => continue,
            };
            if v.is_empty(i) {
                continue;
            }
            // A nested depth breaks; a child that cannot hold a `first`, `then` or `unless` at
            // this depth was not searched and holds nothing that breaks.
            let (c_ends, c_starts, c_clean) = if matches!(name, "procedure body" | "graph pattern")
            {
                (false, false, false)
            } else if self.id(item).is_some_and(|c| !u.reach.contains(c as usize)) {
                (false, false, true)
            } else {
                let c = &v.children[i];
                (c.has(u.ends), c.has(u.starts), c.has(u.clean))
            };
            found |= open && c_starts;
            starts |= clean && c_starts;
            open = c_ends || (open && c_clean);
            clean = clean && c_clean;
        }
        (open, starts, clean, found)
    }

    /// A flanking rule's facts at one node, `[starts nt, ends nt, starts by, ends by]`, and
    /// whether an `nt` here lacks a `by` on either side.
    fn flanking(&self, u: &FlankUse, v: &View) -> ([bool; 4], bool) {
        let node = v.node;
        if !node.group && node.def == u.by {
            return ([false, false, true, true], false);
        }
        if !node.group && node.def == u.nt {
            return ([true, true, false, false], false);
        }
        let sides: Vec<[bool; 4]> = node
            .items
            .iter()
            .enumerate()
            .filter_map(|(i, &item)| match item {
                Item::Def(_) | Item::Group(_) if v.is_empty(i) => None,
                Item::Def(_) | Item::Group(_) => Some(u.facts.map(|f| v.children[i].has(f))),
                Item::Token(_) | Item::Prose(_) => Some([false; 4]),
            })
            .collect();
        let mut lacking = sides
            .windows(2)
            .any(|w| (w[0][1] && !w[1][2]) || (w[1][0] && !w[0][3]));
        let first = sides.first().copied().unwrap_or([false; 4]);
        let last = sides.last().copied().unwrap_or([false; 4]);
        let facts = [first[0], last[1], first[2], last[3]];
        // Nothing comes before or after the start's yield.
        if !node.group && node.def == self.start {
            lacking |= facts[0] || facts[1];
        }
        (facts, lacking)
    }
}

impl Rule for ClaimRules {
    fn name(&self) -> &str {
        "conformance rules of unclaimed features"
    }

    fn cite(&self) -> &str {
        &self.cite
    }

    fn labels(&self) -> Vec<(Fact, String)> {
        self.labels.clone()
    }

    /// Flags, hits and phrase facts only enforce the rules: a production is not in a new
    /// context for carrying them.
    fn bookkeeping(&self) -> bool {
        true
    }

    fn rejects(&self, node: &Node, inh: &State) -> bool {
        !node.group
            && self.hits.iter().any(|h| {
                h.immediate && inh.has(h.flag) && self.nodes[h.alt].nt.as_deref() == Some(node.def)
            })
    }

    fn down(&self, node: &Node, inh: &State, pos: usize, out: &mut State) {
        let item = node.items[pos];
        let Some(child) = self.id(item) else { return };
        let child = child as usize;
        for h in &self.hits {
            let owner = self.nodes[h.owner].nt.as_deref();
            let emit = !node.group && owner == Some(node.def) && self.active(h.owner, inh);
            let pass = inh.has(h.flag) && (node.group || !self.blocks(h, node));
            if (emit || pass) && h.reach.contains(child) {
                out.set(h.flag, true);
            }
        }
        for (nt, &f) in &self.parents {
            if (!node.group && node.def == nt) || (node.group && inh.has(f)) {
                out.set(f, true);
            }
        }
        for u in &self.phrases {
            let Some((owner, _)) = &u.owner else { continue };
            let emit = !node.group && node.def == owner;
            if (emit || inh.has(u.scope)) && u.reach.contains(child) {
                out.set(u.scope, true);
            }
        }
        // A juxtaposition is looked for at its owner's depth of graph pattern matching: not
        // inside a nested procedure body or graph pattern.
        let deeper = matches!(
            item,
            Item::Def("procedure body") | Item::Def("graph pattern")
        );
        for u in &self.juxta {
            let emit = !node.group && node.def == u.owner;
            // A `first`, `then` or `unless` is decided whole, without looking inside.
            let unit = !node.group
                && (node.def == u.first
                    || node.def == u.then
                    || u.unless.iter().any(|x| x == node.def));
            if (emit || inh.has(u.scope)) && !unit && !deeper && u.reach.contains(child) {
                out.set(u.scope, true);
            }
        }
        for u in &self.flank {
            let Some((owner, scope)) = &u.owner else {
                continue;
            };
            let emit = !node.group && node.def == owner;
            if (emit || inh.has(*scope)) && !deeper && u.reach.contains(child) {
                out.set(*scope, true);
            }
        }
    }

    fn step(&self, node: &Node, inh: &State, children: &[State], mut syn: State) -> Option<State> {
        if self.rejects(node, inh) {
            return None;
        }
        let v = View {
            node,
            children,
            empty: self.empty,
        };
        let non_empty = v.non_empty();
        syn.set(self.empty, non_empty.is_empty());
        for (nt, &f) in &self.is {
            syn.set(f, self.is_here(nt, &v));
        }
        if !self.pairs.is_empty() {
            let shape = if node.group {
                self.shape(&v)
            } else {
                Vec::new()
            };
            for (nt, &f) in &self.pairs {
                syn.set(f, shape == [nt.as_str()]);
            }
        }
        for (t, &f) in &self.tokens {
            let here = node.group
                && node
                    .items
                    .iter()
                    .zip(children)
                    .any(|(&item, c)| match item {
                        Item::Token(x) => x.eq_ignore_ascii_case(t),
                        Item::Group(_) => c.has(f),
                        _ => false,
                    });
            syn.set(f, here);
        }

        let mut found = vec![false; self.phrases.len()];
        for (k, u) in self.phrases.iter().enumerate() {
            let in_scope = u.owner.is_none() || inh.has(u.scope);
            let owner_here = !node.group && u.owner.as_ref().is_some_and(|(o, _)| o == node.def);
            let Scan {
                found: f,
                starts,
                ends,
                middle,
            } = if in_scope || owner_here {
                self.scan(u, &v)
            } else {
                Scan::default()
            };
            found[k] = f;
            if u.owner.is_none() && f && !node.group && !self.required_phrases.contains(&k) {
                return None;
            }
            let keep = in_scope && !self.phrase_blocks(u, node);
            syn.set(u.found, keep && f);
            for (i, &fact) in &u.starts {
                syn.set(fact, keep && starts.contains(i));
            }
            for (j, &fact) in &u.ends {
                syn.set(fact, keep && ends.contains(j));
            }
            for (ij, &fact) in &u.middle {
                syn.set(fact, keep && middle.contains(ij));
            }
        }

        for h in &self.hits {
            let in_scope = inh.has(h.flag);
            let own = in_scope && self.matches(h.alt, inh, &v, &found);
            let below = if self.blocks(h, node) {
                0
            } else {
                self.count(h, &v)
            };
            let n = if in_scope {
                (below + usize::from(own)).min(2)
            } else {
                0
            };
            syn.set(h.hit, n >= 1);
            if let Some(f) = h.hits2 {
                syn.set(f, n >= 2);
            }
        }

        if !node.group
            && let Some(tops) = self.tops.get(node.def)
            && tops.iter().any(|&p| self.matches(p, inh, &v, &found))
        {
            return None;
        }

        // Order rules: forbidden ones reject where they are found, required ones count as a
        // match there.
        let mut ordered = false;
        for u in &self.juxta {
            let in_scope = inh.has(u.scope);
            let owner = !node.group && node.def == u.owner;
            let (ends, starts, clean, here) = if in_scope || owner {
                self.juxtaposition(u, &v)
            } else {
                Default::default()
            };
            if here {
                if !u.required {
                    return None;
                }
                ordered = true;
            }
            syn.set(u.ends, in_scope && ends);
            syn.set(u.starts, in_scope && starts);
            syn.set(u.clean, in_scope && clean);
        }
        for u in &self.flank {
            // With an owner, only inside one; the owner decides what is at its own edges.
            let (looked, owner_here) = match &u.owner {
                Some((owner, scope)) => {
                    let here = !node.group && node.def == owner;
                    (inh.has(*scope) || here, here)
                }
                None => (true, false),
            };
            let (facts, mut lacking) = if looked {
                self.flanking(u, &v)
            } else {
                Default::default()
            };
            if owner_here {
                lacking |= facts[0] || facts[1];
            }
            if lacking {
                if !u.required {
                    return None;
                }
                ordered = true;
            }
            let keep = match &u.owner {
                Some((_, scope)) => inh.has(*scope),
                None => true,
            };
            for (f, on) in u.facts.iter().zip(facts) {
                syn.set(*f, keep && on);
            }
        }

        let any_required = !self.required.is_empty()
            || !self.required_phrases.is_empty()
            || self.juxta.iter().any(|u| u.required)
            || self.flank.iter().any(|u| u.required);
        if any_required {
            let here = ordered
                || self
                    .required
                    .iter()
                    .any(|&p| self.matches(p, inh, &v, &found))
                || self.required_phrases.iter().any(|&u| found[u]);
            let has = here || children.iter().any(|c| c.has(self.matched));
            if !node.group && node.def == self.start && !has {
                return None;
            }
            syn.set(self.matched, has);
        }
        Some(syn)
    }
}
