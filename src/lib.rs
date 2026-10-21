//! Grammar driven conformance evidence for GQL (ISO/IEC 39075).

pub mod bnf;
pub mod cfg;
pub mod context;
pub mod coverage;
pub mod features;
pub mod leaf;
pub mod parse;
pub mod purdom;
pub mod refine;
pub mod scope;
pub mod tokens;
pub mod tree;
pub mod verify;

/// The ISO grammar as ISO/IEC 39075:2024/Cor 1:2026 corrects it: `just fetch` downloads the
/// 2024 one from https://standards.iso.org/iso-iec/39075/ed-1/en/, which Cor 1 has not
/// updated, and `just grammar` applies Cor 1's grammar edits to it (`tools/corrigendum.py`).
pub const ISO_BNF_XML: &str = include_str!("../grammar/ISO_IEC_39075(en)+Cor1.bnf.xml");

/// What every grammar, rule and claim here is read against.
pub const EDITION: &str = "ISO/IEC 39075:2024 + Cor 1:2026";

use cfg::{Cfg, Lit, ProdId, Sym};

/// The match mode a `<graph pattern>` without one gets: implementation-defined (ID086,
/// 16.4 SR 10).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum MatchModeDefault {
    /// Assume nothing: only what is valid whichever default an engine picks.
    #[default]
    Portable,
    DifferentEdges,
    RepeatableElements,
}

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
    let rhs = if rhs.is_empty() {
        "ε".to_string()
    } else {
        rhs.join(" ")
    };
    format!("<{}> ::= {rhs}", cfg.name(prod.lhs))
}
