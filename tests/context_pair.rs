//! The pair combinator (`context::pair`): scope with nothing under it is scope.

use gql_proof::cfg::{Cfg, Sym};
use gql_proof::context::pair::{Typed, Unit};
use gql_proof::context::scope::{Caps, Scope};
use gql_proof::context::{Options, build};
use gql_proof::{ISO_BNF_XML, bnf};
use std::sync::LazyLock;
use std::time::Instant;

static ISO: LazyLock<bnf::Bnf> = LazyLock::new(|| bnf::parse(ISO_BNF_XML).unwrap());
static BASE: LazyLock<Cfg> = LazyLock::new(|| Cfg::from_bnf(&ISO));

/// Every production by the names of its symbols, sorted.
fn productions(cfg: &Cfg) -> Vec<String> {
    let mut out: Vec<String> = cfg
        .prods
        .iter()
        .map(|p| {
            let rhs: Vec<String> = p
                .rhs
                .iter()
                .map(|s| match s {
                    Sym::Nt(n) => cfg.nts[*n as usize].name.clone(),
                    Sym::Lit(l) => format!("{:?}", cfg.lits[*l as usize]),
                })
                .collect();
            format!("{} ::= {}", cfg.nts[p.lhs as usize].name, rhs.join(" "))
        })
        .collect();
    out.sort();
    out
}

#[test]
fn unit_under_scope_is_scope() {
    let start = BASE.require("GQL-program").unwrap();
    let scope = || Scope {
        caps: Caps {
            slots: 2,
            references: 2,
        },
    };
    let options = Options {
        progress: false,
        ..Options::default()
    };
    let t = Instant::now();
    let alone = build(&BASE, &scope(), start, "x", &options).unwrap();
    let (alone_time, t) = (t.elapsed(), Instant::now());
    let paired = build(&BASE, &Typed::new(scope(), Unit), start, "x", &options).unwrap();
    let paired_time = t.elapsed();
    eprintln!("scope {alone_time:?}, scope with nothing {paired_time:?}");
    assert_eq!(alone.stats.labels, paired.stats.labels);
    assert_eq!(productions(&alone.cfg), productions(&paired.cfg));
}
