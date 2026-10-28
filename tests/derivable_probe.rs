//! A probe for gate holes the generator can reach. A tree the generator derives is one its
//! context rules (scope and types, `context::accepts`) and its refinement automata
//! (`refine::accepts`) both accept; only such a tree can be printed, so only a derivable tree
//! that passes every checker and breaks a rule is a hole in the printed output's soundness.
//!
//! PROBES=file (one probe per line, `\n` for a newline), CLAIM (default `all`), LIMIT (parses,
//! default 2048), SLOTS (the scope rule's variable cap, default 3, at least any run's). Prints,
//! per probe: the parses, the derivable ones, and the clean ones split by derivability.

use gql_proof::bnf;
use gql_proof::cfg::Cfg;
use gql_proof::context::pair::Typed;
use gql_proof::context::scope::{Caps, Scope};
use gql_proof::context::types::Types;
use gql_proof::parse::Parser;
use gql_proof::tokens::Grammar;
use gql_proof::verify::{Verifier, scope, types};
use gql_proof::{ISO_BNF_XML, MatchModeDefault};
use std::cell::Cell;
use std::sync::LazyLock;

static ISO_BNF: LazyLock<bnf::Bnf> = LazyLock::new(|| bnf::parse(ISO_BNF_XML).unwrap());
static ISO: LazyLock<Cfg> = LazyLock::new(|| Cfg::from_bnf(&ISO_BNF));

#[test]
#[ignore]
fn derivable_probe() {
    let text = std::fs::read_to_string(std::env::var("PROBES").unwrap()).unwrap();
    let conf = gql_proof::features::Conformance::load(gql_proof::features::CONFORMANCE_JSON).unwrap();
    let claim = gql_proof::features::Claim::parse(&std::env::var("CLAIM").unwrap_or("all".into()), &conf).unwrap();
    let mode = MatchModeDefault::DifferentEdges;
    let v = Verifier::new(Grammar::new(&ISO_BNF))
        .with_syntax_rules(mode)
        .with_conformance(conf.forbidden(&claim))
        .with_key_label_sets_required(!claim.features.contains("GG22"));
    let slots = std::env::var("SLOTS").ok().and_then(|s| s.parse().ok()).unwrap_or(3);
    let typed = Typed::new(Scope { caps: Caps { slots, references: slots } }, Types::with_typed(&ISO, slots));
    let automata = gql_proof::refine::all_rules(mode);
    let tokens = Grammar::new(&ISO_BNF);
    for line in text.lines().map(str::trim).filter(|l| !l.is_empty() && !l.starts_with('#')) {
        let line = line.replace("\\n", "\n");
        let mut parser = Parser::new(&ISO, &tokens, "GQL-program").unwrap();
        parser.limit = std::env::var("LIMIT").ok().and_then(|s| s.parse().ok()).unwrap_or(2048);
        let (n, derivable, hole, unreachable) = (Cell::new(0), Cell::new(0), Cell::new(0), Cell::new(0));
        let _ = parser.parse(&line, |t| {
            n.set(n.get() + 1);
            let plain = t.export(&ISO);
            let reach = gql_proof::context::accepts(&typed, &plain).is_ok()
                && gql_proof::refine::accepts(&automata, &plain).is_ok();
            if reach {
                derivable.set(derivable.get() + 1);
            }
            let clean = v.verify(&plain, &t.render(&ISO)).is_empty()
                && scope::check(&plain).is_empty()
                && types::check(&plain).is_empty();
            if clean {
                let c = if reach { &hole } else { &unreachable };
                c.set(c.get() + 1);
            }
            false
        });
        println!(
            "== {line}\n   parses {} derivable {} clean+derivable {} clean+underivable {}",
            n.get(),
            derivable.get(),
            hole.get(),
            unreachable.get()
        );
    }
}
