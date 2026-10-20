//! Derivation trees and their printers.

use crate::cfg::{Cfg, Lit, ProdId, Sym};

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
        let p = self.prod.ok_or_else(|| format!("<{}> has no production", cfg.name(nt)))?;
        let prod = cfg.prod(p);
        let syms: Vec<Sym> = self.children.iter().map(|c| c.sym).collect();
        if prod.lhs != nt || prod.rhs != syms {
            return Err(format!("<{}> children do not match production {p}", cfg.name(nt)));
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
        let Sym::Nt(nt) = self.sym else { return termtree::Tree::new(label) };
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
            Sym::Nt(nt) => format!("<{}>", cfg.name(nt)),
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
