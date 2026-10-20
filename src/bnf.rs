//! Reads the ISO/IEC 39075 grammar XML (`ISO_IEC_39075(en).bnf.xml`) into an EBNF tree.
//!
//! The XML vocabulary is described by the DTD at the top of that file. The parts we use:
//! `BNFdef` (one definition), `rhs`, `alt`, `opt` (`[...]`), `group` (`{...}`), `repeat`
//! (postfix `...` on the previous item), `BNF` (a reference), `kw`, `terminalsymbol` and
//! `seeTheRules` ("!! See the Syntax Rules", a definition given in prose).

use anyhow::{Context, Result, anyhow, bail};
use std::collections::HashSet;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ebnf {
    Seq(Vec<Ebnf>),
    Alt(Vec<Ebnf>),
    Opt(Box<Ebnf>),
    /// One or more.
    Repeat(Box<Ebnf>),
    Ref(String),
    Kw(String),
    Term(String),
    /// "!! See the Syntax Rules", carrying the name of the definition it appears in.
    Opaque(String),
}

#[derive(Debug, Clone)]
pub struct Def {
    pub name: String,
    pub rhs: Ebnf,
}

#[derive(Debug, Clone)]
pub struct Bnf {
    pub defs: Vec<Def>,
}

impl Bnf {
    pub fn get(&self, name: &str) -> Option<&Def> {
        self.defs.iter().find(|d| d.name == name)
    }
}

pub fn parse(xml: &str) -> Result<Bnf> {
    let opts = roxmltree::ParsingOptions { allow_dtd: true, ..Default::default() };
    let doc = roxmltree::Document::parse_with_options(xml, opts).context("parsing grammar xml")?;
    let mut defs = Vec::new();
    for def in doc.root_element().children().filter(|n| n.has_tag_name("BNFdef")) {
        let name = def.attribute("name").ok_or_else(|| anyhow!("BNFdef without a name"))?;
        let rhs = elements(def)
            .find(|n| n.has_tag_name("rhs"))
            .ok_or_else(|| anyhow!("<{name}> has no rhs"))?;
        let rhs = container(rhs, name).with_context(|| format!("in <{name}>"))?;
        defs.push(Def { name: name.to_string(), rhs });
    }
    let bnf = Bnf { defs };
    check_refs(&bnf)?;
    Ok(bnf)
}

fn elements<'a, 'i>(node: roxmltree::Node<'a, 'i>) -> impl Iterator<Item = roxmltree::Node<'a, 'i>> {
    node.children().filter(|n| n.is_element())
}

/// Parses the children of `rhs`, `alt`, `opt` or `group`: either a list of alternatives
/// or a sequence.
fn container(node: roxmltree::Node, def: &str) -> Result<Ebnf> {
    let mut alts = Vec::new();
    let mut seq: Vec<Ebnf> = Vec::new();
    for child in elements(node) {
        match child.tag_name().name() {
            "alt" => alts.push(container(child, def)?),
            "opt" => seq.push(Ebnf::Opt(Box::new(container(child, def)?))),
            "group" => seq.push(container(child, def)?),
            "BNF" => {
                let name = child.attribute("name").ok_or_else(|| anyhow!("BNF without a name"))?;
                seq.push(Ebnf::Ref(name.to_string()));
            }
            "kw" | "bold" => seq.push(Ebnf::Kw(child.text().unwrap_or_default().trim().to_string())),
            "terminalsymbol" => seq.push(Ebnf::Term(terminal(child)?)),
            "repeat" => {
                let last = seq.pop().ok_or_else(|| anyhow!("repeat with nothing before it"))?;
                seq.push(Ebnf::Repeat(Box::new(last)));
            }
            "seeTheRules" => seq.push(Ebnf::Opaque(def.to_string())),
            other => bail!("unsupported element <{other}>"),
        }
    }
    if alts.is_empty() {
        return Ok(simplify(seq));
    }
    // The DTD allows `alt+` followed by an optional `seeTheRules`, which reads as one more
    // alternative given in prose.
    match seq.as_slice() {
        [] => {}
        [Ebnf::Opaque(_)] => alts.push(seq.pop().unwrap()),
        _ => bail!("alternatives mixed with a sequence"),
    }
    Ok(Ebnf::Alt(alts))
}

fn simplify(mut seq: Vec<Ebnf>) -> Ebnf {
    if seq.len() == 1 { seq.pop().unwrap() } else { Ebnf::Seq(seq) }
}

/// The `unicode` attribute is exact (comma separated code points); the text is a fallback.
fn terminal(node: roxmltree::Node) -> Result<String> {
    if let Some(points) = node.attribute("unicode") {
        return points
            .split(',')
            .map(|p| {
                let cp = u32::from_str_radix(p.trim(), 16)?;
                char::from_u32(cp).ok_or_else(|| anyhow!("bad code point {p}"))
            })
            .collect();
    }
    Ok(node.text().unwrap_or_default().to_string())
}

fn check_refs(bnf: &Bnf) -> Result<()> {
    let names: HashSet<&str> = bnf.defs.iter().map(|d| d.name.as_str()).collect();
    let mut dangling = Vec::new();
    for def in &bnf.defs {
        visit_refs(&def.rhs, &mut |r| {
            if !names.contains(r) {
                dangling.push(format!("<{}> in <{}>", r, def.name));
            }
        });
    }
    if !dangling.is_empty() {
        bail!("unresolved references: {}", dangling.join(", "));
    }
    Ok(())
}

pub fn visit_refs(e: &Ebnf, f: &mut impl FnMut(&str)) {
    match e {
        Ebnf::Seq(items) | Ebnf::Alt(items) => items.iter().for_each(|i| visit_refs(i, f)),
        Ebnf::Opt(inner) | Ebnf::Repeat(inner) => visit_refs(inner, f),
        Ebnf::Ref(name) => f(name),
        Ebnf::Kw(_) | Ebnf::Term(_) | Ebnf::Opaque(_) => {}
    }
}
