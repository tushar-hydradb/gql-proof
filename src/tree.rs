//! Derivation trees and their printers.

use crate::cfg::{Cfg, Lit, NtId, ProdId, Sym};
use crate::verify::Plain;
use rand_chacha::ChaCha8Rng;

#[derive(Debug, Clone)]
pub struct Node {
    pub sym: Sym,
    /// The production expanded here; `None` for a literal leaf.
    pub prod: Option<ProdId>,
    /// The text of a literal leaf.
    pub text: Option<String>,
    pub children: Vec<Node>,
}

impl Node {
    /// The tree as names and text, for the independent checker in `verify`.
    pub fn export(&self, cfg: &Cfg) -> Plain {
        match self.sym {
            Sym::Nt(nt) => Plain::Def {
                name: cfg.base(nt).to_string(),
                synthetic: cfg.nts[nt as usize].synthetic,
                children: self.children.iter().map(|c| c.export(cfg)).collect(),
            },
            Sym::Lit(l) => {
                let text = self.text.clone().unwrap_or_default();
                match &cfg.lits[l as usize] {
                    Lit::Kw(_) => Plain::Kw(text),
                    Lit::Term(_) => Plain::Term(text),
                    Lit::Opaque(def) => Plain::Leaf {
                        def: def.clone(),
                        text,
                    },
                }
            }
        }
    }

    /// Leaves have height 0, a nonterminal is one above its tallest child.
    pub fn height(&self) -> u32 {
        match self.sym {
            Sym::Lit(_) => 0,
            Sym::Nt(_) => 1 + self.children.iter().map(Node::height).max().unwrap_or(0),
        }
    }

    /// Every production used in the tree, in preorder.
    pub fn prods(&self, out: &mut Vec<ProdId>) {
        out.extend(self.prod);
        self.children.iter().for_each(|c| c.prods(out));
    }

    /// Checks that each node's children spell out the right hand side of its production.
    pub fn validate(&self, cfg: &Cfg) -> Result<(), String> {
        let Sym::Nt(nt) = self.sym else { return Ok(()) };
        let p = self
            .prod
            .ok_or_else(|| format!("<{}> has no production", cfg.name(nt)))?;
        let prod = cfg.prod(p);
        let syms: Vec<Sym> = self.children.iter().map(|c| c.sym).collect();
        if prod.lhs != nt || prod.rhs != syms {
            return Err(format!(
                "<{}> children do not match production {p}",
                cfg.name(nt)
            ));
        }
        self.children.iter().try_for_each(|c| c.validate(cfg))
    }

    /// The sentence: lexical subtrees become one token each, tokens are joined by spaces.
    pub fn render(&self, cfg: &Cfg) -> String {
        let mut tokens = Vec::new();
        self.tokens(cfg, &mut tokens);
        tokens.retain(|t| !t.is_empty());
        tokens.join(" ")
    }

    fn tokens(&self, cfg: &Cfg, out: &mut Vec<String>) {
        match self.sym {
            Sym::Lit(_) => out.push(self.text.clone().unwrap_or_default()),
            Sym::Nt(nt) if cfg.nts[nt as usize].lexical => out.push(self.concat()),
            Sym::Nt(_) => self.children.iter().for_each(|c| c.tokens(cfg, out)),
        }
    }

    fn concat(&self) -> String {
        match &self.text {
            Some(text) => text.clone(),
            None => self.children.iter().map(Node::concat).collect(),
        }
    }

    /// A printable tree. Synthetic nonterminals (from `[...]`, `...` and `{a | b}`) are
    /// flattened into their parent; lexical subtrees collapse to one leaf unless
    /// `expand_lexical` is set.
    pub fn display(&self, cfg: &Cfg, expand_lexical: bool) -> termtree::Tree<String> {
        let label = self.label(cfg);
        let Sym::Nt(nt) = self.sym else {
            return termtree::Tree::new(label);
        };
        if cfg.nts[nt as usize].lexical && !expand_lexical {
            return termtree::Tree::new(format!("{label} {:?}", self.concat()));
        }
        let mut flat = Vec::new();
        self.flatten(cfg, &mut flat);
        termtree::Tree::new(label)
            .with_leaves(flat.into_iter().map(|c| c.display(cfg, expand_lexical)))
    }

    fn flatten<'a>(&'a self, cfg: &Cfg, out: &mut Vec<&'a Node>) {
        for child in &self.children {
            match child.sym {
                Sym::Nt(nt) if cfg.nts[nt as usize].synthetic => child.flatten(cfg, out),
                _ => out.push(child),
            }
        }
    }

    fn label(&self, cfg: &Cfg) -> String {
        match self.sym {
            Sym::Nt(nt) => format!("<{}>", cfg.base(nt)),
            Sym::Lit(l) => {
                let text = self.text.as_deref().unwrap_or_default();
                match &cfg.lits[l as usize] {
                    Lit::Kw(_) => text.to_string(),
                    Lit::Term(_) => format!("{text:?}"),
                    Lit::Opaque(_) => format!("{text:?} (see the syntax rules)"),
                }
            }
        }
    }
}

/// The values the syntax rules order, settled at spelling time. The engine knows an integer is
/// zero or not, never its value (the automaton in `refine`), so a tree can come out with one
/// below what a rule asks of it:
/// - 16.11 SR 3 a ii: a general quantifier's upper bound is at or above its lower (`{ 8 , 0o2 }`)
/// - 18.9 SR 7, 13, 21: a string type's max length is at least 1 and at or above its min
///   length; a list type's max length is at least 1
/// - 18.9 SR 10: a fixed length is at least 1
/// - 18.9 SR 29, 38: a precision is at least 1 and at or above its scale
/// - 18.9 SR 40: an approximate numeric type's precision is at least 2
/// - 16.6 SR 2 b ii: a literal number of paths or groups is at least 1
///
/// The integer is then re-spelled with digits prefixed to the ones it was extracted for, in its
/// own radix, to a value at or above the least: `{ 8 , 0o12 }`, `CHAR ( 0b10 )`. Its digits and
/// radix stay, so every production the tree was found for is still in it; the prefix only adds
/// digit productions. Like naming, this is the one place a value is looked at; both generators
/// (`context::extract::cover`, `purdom`) run it, and the checker (`verify`) reads the values
/// again. Returns whether an integer was re-spelled: the tree then holds more nodes than the
/// search that built it counted, so purdom's height and length caps do not hold for it.
pub fn order_bounds(
    cfg: &Cfg,
    root: &mut Node,
    spell: &impl Fn(NtId, &str) -> Option<Node>,
    rng: &mut ChaCha8Rng,
) -> bool {
    let values = settle_values(cfg, root, spell, rng);
    let fresh = fresh_created_names(cfg, root, spell);
    distinct_names(cfg, root, spell) || values || fresh
}

/// 18.5 SR 1, 18.10 SR 2, 20.19 SR 2: the names in one property type list, field type list
/// or field list are distinct. The leaf provider spells every name `a`; a repeated one is
/// re-spelled `ab`, `abb`, ... (the first spelling no earlier name in the list has), under
/// its own <property name> or <field name>, as naming does. A spelling the copy cannot
/// derive leaves the tree as it was: the checker reports it.
fn distinct_names(cfg: &Cfg, root: &mut Node, spell: &impl Fn(NtId, &str) -> Option<Node>) -> bool {
    let Sym::Nt(nt) = root.sym else { return false };
    let mut changed = false;
    let (item, name) = match cfg.base(nt) {
        "property type list" => ("property type", "property name"),
        "field type list" => ("field type", "field name"),
        "field list" => ("field", "field name"),
        _ => ("", ""),
    };
    if !item.is_empty() {
        let mut items: Vec<&mut Node> = Vec::new();
        collect(cfg, root, item, &mut items);
        let mut seen = std::collections::BTreeSet::new();
        for it in items {
            let Some(n) = through_groups(cfg, it, name) else { continue };
            let text = n.render(cfg);
            if seen.insert(text.clone()) {
                continue;
            }
            let Sym::Nt(name_nt) = n.sym else { continue };
            // The first of `a`, `ab`, `abb`, ... that no name of the list has and the copy
            // derives.
            let mut fresh = String::from("a");
            for _ in 0..64 {
                if !seen.contains(&fresh)
                    && let Some(spelt) = spell(name_nt, &fresh)
                {
                    *n = spelt;
                    seen.insert(fresh);
                    changed = true;
                    break;
                }
                fresh.push('b');
            }
        }
    }
    for child in &mut root.children {
        changed |= distinct_names(cfg, child, spell);
    }
    changed
}

/// The `<base>` nodes below `node` through synthetic groups and through `node`'s own list
/// definition (a list is left recursive or a repetition), not into the items themselves.
fn collect<'a>(cfg: &Cfg, node: &'a mut Node, base: &str, out: &mut Vec<&'a mut Node>) {
    let list = match node.sym {
        Sym::Nt(nt) => cfg.base(nt).to_string(),
        Sym::Lit(_) => return,
    };
    for child in &mut node.children {
        let Sym::Nt(nt) = child.sym else { continue };
        if cfg.base(nt) == base {
            out.push(child);
        } else if cfg.nts[nt as usize].synthetic || cfg.base(nt) == list {
            collect(cfg, child, base, out);
        }
    }
}

fn settle_values(
    cfg: &Cfg,
    root: &mut Node,
    spell: &impl Fn(NtId, &str) -> Option<Node>,
    rng: &mut ChaCha8Rng,
) -> bool {
    let Sym::Nt(nt) = root.sym else { return false };
    let mut changed = false;
    let value = |n: &mut Node| crate::verify::unsigned_integer_value(&n.render(cfg));
    // The integers to raise, by the definition holding each, and the least value each may have.
    let wants: Vec<(&str, u64)> = match cfg.base(nt) {
        "general quantifier" => through_groups(cfg, root, "lower bound")
            .map(value)
            .map(|lower| ("upper bound", lower))
            .into_iter()
            .collect(),
        "character string type" | "byte string type" => {
            let min = through_groups(cfg, root, "min length").map_or(0, value);
            vec![("max length", min.max(1)), ("fixed length", 1)]
        }
        "list value type" => vec![("max length", 1)],
        "decimal exact numeric type"
        | "signed binary exact numeric type"
        | "unsigned binary exact numeric type"
        | "verbose binary exact numeric type" => {
            let scale = through_groups(cfg, root, "scale").map_or(0, value);
            vec![("precision", scale.max(1))]
        }
        "approximate numeric type" => vec![("precision", 2)],
        // 16.6 SR 2 b ii: a literal number of paths or groups is positive.
        "number of paths" | "number of groups" => {
            vec![("non-negative integer specification", 1)]
        }
        _ => Vec::new(),
    };
    // IL018 (H2): a quantifier's bounds stay at most 255, turbolay's limit, before the upper
    // bound is raised to the lower (the thirteenth review: `{ 888 }` was printed)
    match cfg.base(nt) {
        "fixed quantifier" => changed |= lower(cfg, root, 255, spell),
        "general quantifier" => {
            for b in ["lower bound", "upper bound"] {
                if let Some(holder) = through_groups(cfg, root, b) {
                    changed |= lower(cfg, holder, 255, spell);
                }
            }
        }
        _ => {}
    }
    for (holder, least) in wants {
        if let Some(holder) = through_groups(cfg, root, holder) {
            changed |= raise(cfg, holder, least, spell, rng);
        }
    }
    // H2 asks the implementation for an exponent scale at least what S writes (18.9 SR 42, 43,
    // IL011): kept to FLOAT32's 8, which every engine with FLOAT32 has (the sixth review found
    // FLOAT ( 8 , 88 ), beyond FLOAT256).
    if cfg.base(nt) == "approximate numeric type"
        && let Some(holder) = through_groups(cfg, root, "scale")
    {
        changed |= lower(cfg, holder, 8, spell);
    }
    for child in &mut root.children {
        changed |= settle_values(cfg, child, spell, rng);
    }
    changed
}

/// Re-spells the integer under `holder` (a bound, a length, a precision) to at least `least`,
/// if it is below. Spelled under the radix's own definition, the child of <unsigned integer>, or
/// the <unsigned decimal integer> a precision is: derived from <unsigned integer> itself, `0o12`
/// reads as a decimal integer whose `o` is an <other digit>, a prose leaf that takes any
/// character. A spelling the copy cannot derive leaves the tree as it was: the checker reports
/// it.
fn raise(
    cfg: &Cfg,
    holder: &mut Node,
    least: u64,
    spell: &impl Fn(NtId, &str) -> Option<Node>,
    rng: &mut ChaCha8Rng,
) -> bool {
    let Some(int) = integer_in(cfg, holder) else {
        return false;
    };
    let text = int.render(cfg);
    if crate::verify::unsigned_integer_value(&text) >= least {
        return false;
    }
    let Sym::Nt(nt) = int.sym else { return false };
    match spell(nt, &raised_bound(&text, least, rng)) {
        Some(spelt) => {
            *int = spelt;
            true
        }
        None => false,
    }
}

/// Re-spells the integer under `holder` to `most` in its own radix, if it is above.
fn lower(
    cfg: &Cfg,
    holder: &mut Node,
    most: u64,
    spell: &impl Fn(NtId, &str) -> Option<Node>,
) -> bool {
    let Some(int) = integer_in(cfg, holder) else {
        return false;
    };
    let text = int.render(cfg);
    if crate::verify::unsigned_integer_value(&text) <= most {
        return false;
    }
    let Sym::Nt(nt) = int.sym else { return false };
    let lowered = match text.get(..2) {
        Some("0x" | "0X") => format!("{}{most:x}", &text[..2]),
        Some("0o" | "0O") => format!("{}{most:o}", &text[..2]),
        Some("0b" | "0B") => format!("{}{most:b}", &text[..2]),
        _ => most.to_string(),
    };
    match spell(nt, &lowered) {
        Some(spelt) => {
            *int = spelt;
            true
        }
        None => false,
    }
}

/// The integer subtree of `node` to re-spell: the radix child of its <unsigned integer>, or
/// its <unsigned decimal integer>, looking through synthetic groups only.
fn integer_in<'a>(cfg: &Cfg, node: &'a mut Node) -> Option<&'a mut Node> {
    for child in &mut node.children {
        let Sym::Nt(nt) = child.sym else { continue };
        match cfg.base(nt) {
            "unsigned integer" => {
                return child
                    .children
                    .iter_mut()
                    .find(|c| matches!(c.sym, Sym::Nt(_)));
            }
            "unsigned decimal integer" => return Some(child),
            _ => {}
        }
        if cfg.nts[nt as usize].synthetic
            && let Some(found) = integer_in(cfg, child)
        {
            return Some(found);
        }
    }
    None
}

/// The child of `node` whose definition is `base`, looking through synthetic groups only.
fn through_groups<'a>(cfg: &Cfg, node: &'a mut Node, base: &str) -> Option<&'a mut Node> {
    for child in &mut node.children {
        let Sym::Nt(nt) = child.sym else { continue };
        if cfg.base(nt) == base {
            return Some(child);
        }
        if cfg.nts[nt as usize].synthetic
            && let Some(found) = through_groups(cfg, child, base)
        {
            return Some(found);
        }
    }
    None
}

/// `text`, an <unsigned integer> below `lower`, with digits prefixed in its radix so that it
/// is at least `lower`: the smallest prefix, or a random one while the value stays within
/// turbolay's IL018 cap of 255. The digits of `text` (underscores included) stay as the
/// suffix.
pub fn raised_bound(text: &str, lower: u64, rng: &mut ChaCha8Rng) -> String {
    use rand::RngExt;
    let (prefix, digits, radix): (&str, &str, u64) = match text.as_bytes() {
        [b'0', b'x' | b'X', ..] => (&text[..2], &text[2..], 16),
        [b'0', b'o' | b'O', ..] => (&text[..2], &text[2..], 8),
        [b'0', b'b' | b'B', ..] => (&text[..2], &text[2..], 2),
        _ => ("", text, 10),
    };
    let value = crate::verify::unsigned_integer_value(text);
    let places = digits.chars().filter(|c| *c != '_').count() as u32;
    let unit = radix.saturating_pow(places);
    let least = lower.saturating_sub(value).div_ceil(unit);
    let most = 255u64.saturating_sub(value) / unit;
    let k = if most >= least {
        rng.random_range(least..=most)
    } else {
        least
    };
    let spelt = match radix {
        16 => format!("{k:X}"),
        8 => format!("{k:o}"),
        2 => format!("{k:b}"),
        _ => k.to_string(),
    };
    format!("{prefix}{spelt}{digits}")
}

/// 12.2 SR 5, 12.4 SR 6, 12.6 SR 5 with H1: a name a CREATE makes must name nothing that exists,
/// every other name must name something that does. The leaf provider spells every name `a`, so
/// a created name is re-spelled `ab`, `abb`, ... to the first spelling no other object name of
/// the tree has, under its own definition.
fn fresh_created_names(cfg: &Cfg, root: &mut Node, spell: &impl Fn(NtId, &str) -> Option<Node>) -> bool {
    const NAMES: [&str; 8] = [
        "graph name",
        "graph type name",
        "binding table name",
        "procedure name",
        "schema name",
        "object name or binding variable",
        "delimited graph name",
        "delimited binding table name",
    ];
    // The representative form (21.3 SR 3, 4): a delimited name without its quotes, doubled
    // quotes undoubled, so `"a"` and `a` are one name.
    fn rep(s: &str) -> String {
        match s.chars().next() {
            Some(q @ ('"' | '`')) if s.len() >= 2 && s.ends_with(q) => {
                s[1..s.len() - 1].replace(&format!("{q}{q}"), &q.to_string())
            }
            _ => s.to_string(),
        }
    }
    fn texts(cfg: &Cfg, n: &Node, out: &mut Vec<String>) {
        if let Sym::Nt(nt) = n.sym
            && NAMES.contains(&cfg.base(nt))
        {
            out.push(rep(&n.render(cfg)));
        }
        for c in &n.children {
            texts(cfg, c, out);
        }
    }
    fn made<'a>(cfg: &Cfg, n: &'a mut Node, want: &str) -> Option<&'a mut Node> {
        if let Sym::Nt(nt) = n.sym
            && cfg.base(nt) == want
        {
            return Some(n);
        }
        for c in &mut n.children {
            if let Some(m) = made(cfg, c, want) {
                return Some(m);
            }
        }
        None
    }
    fn walk(cfg: &Cfg, n: &mut Node, spell: &impl Fn(NtId, &str) -> Option<Node>, taken: &mut Vec<String>) -> bool {
        let mut changed = false;
        if let Sym::Nt(nt) = n.sym {
            let want = match cfg.base(nt) {
                "create schema statement" => Some("schema name"),
                "create graph statement" => Some("graph name"),
                "create graph type statement" => Some("graph type name"),
                _ => None,
            };
            if let Some(want) = want
                && let Some(m) = made(cfg, n, want)
                && let Sym::Nt(mnt) = m.sym
            {
                // Extend the spelling, not replace it: `b`s appended (inside the quotes of a
                // delimited name), so every production the name was found for stays.
                let old = m.render(cfg);
                // A placeholder rendering (a tree spelled without lexical leaves) is not a name
                // to extend: start from a plain one.
                let old = if old.chars().all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '"' | '`'))
                    && spell(mnt, &old).is_some()
                {
                    old
                } else {
                    String::from("a")
                };
                let quoted = old.len() >= 2
                    && (old.starts_with('"') || old.starts_with('`'))
                    && old.ends_with(&old[..1]);
                let mut extra = String::from("b");
                for _ in 0..64 {
                    let fresh = if quoted {
                        format!("{}{}{}", &old[..old.len() - 1], extra, &old[old.len() - 1..])
                    } else {
                        format!("{old}{extra}")
                    };
                    if !taken.contains(&rep(&fresh))
                        && let Some(spelt) = spell(mnt, &fresh)
                    {
                        *m = spelt;
                        taken.push(rep(&fresh));
                        changed = true;
                        break;
                    }
                    extra.push('b');
                }
            }
        }
        for c in &mut n.children {
            changed |= walk(cfg, c, spell, taken);
        }
        changed
    }
    let mut taken = Vec::new();
    texts(cfg, root, &mut taken);
    walk(cfg, root, spell, &mut taken)
}
