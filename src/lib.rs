//! Grammar driven conformance evidence for GQL (ISO/IEC 39075).

pub mod bnf;
pub mod cfg;
pub mod leaf;
pub mod purdom;
pub mod tree;

/// The ISO grammar, vendored unmodified from https://standards.iso.org/iso-iec/39075/ed-1/en/.
pub const ISO_BNF_XML: &str = include_str!("../grammar/ISO_IEC_39075(en).bnf.xml");

use cfg::{Cfg, Lit, ProdId, Sym};

/// `<lhs> ::= ...` for a desugared production, for reports.
pub fn describe(cfg: &Cfg, p: ProdId) -> String {
    let prod = cfg.prod(p);
    let rhs: Vec<String> = prod
        .rhs
        .iter()
        .map(|sym| match *sym {
            Sym::Nt(nt) => format!("<{}>", cfg.name(nt)),
            Sym::Lit(l) => match &cfg.lits[l as usize] {
                Lit::Kw(k) => k.clone(),
                Lit::Term(t) => format!("{t:?}"),
                Lit::Opaque(_) => "!! See the Syntax Rules".to_string(),
            },
        })
        .collect();
    let rhs = if rhs.is_empty() { "ε".to_string() } else { rhs.join(" ") };
    format!("<{}> ::= {rhs}", cfg.name(prod.lhs))
}
