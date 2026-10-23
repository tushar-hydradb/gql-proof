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
        _ => Vec::new(),
    };
    for (holder, least) in wants {
        if let Some(holder) = through_groups(cfg, root, holder) {
            changed |= raise(cfg, holder, least, spell, rng);
        }
    }
    for child in &mut root.children {
        changed |= order_bounds(cfg, child, spell, rng);
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
