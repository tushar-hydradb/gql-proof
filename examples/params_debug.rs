//! Scratch: which classes a parameter site admits, with the rules' trace.
use gql_proof::cfg::Cfg;
use gql_proof::parse::Parser;
use gql_proof::tokens::Grammar;
use gql_proof::verify::Verifier;
use gql_proof::{ISO_BNF_XML, bnf};
use tracing_subscriber::{EnvFilter, fmt, prelude::*};

fn main() {
    tracing_subscriber::registry()
        .with(fmt::layer().with_writer(std::io::stderr).with_filter(
            EnvFilter::try_from_env("GQL_TRACE").unwrap_or_else(|_| EnvFilter::new("warn")),
        ))
        .init();
    let text = std::env::args().nth(1).expect("a sentence");
    let param = std::env::args().nth(2).unwrap_or("$b".to_string());
    let bnf = bnf::parse(ISO_BNF_XML).unwrap();
    let iso = Cfg::from_bnf(&bnf);
    // With GQL_REFINE_CLAIM=<claim file>: the grammar the syntax rules and the claim refine,
    // as the context command uses it.
    let (base, start) = match std::env::var("GQL_REFINE_CLAIM") {
        Ok(claim) => {
            use gql_proof::features::{CONFORMANCE_JSON, Claim, ClaimRules, Conformance};
            use gql_proof::refine::{all_rules, refine};
            let id086 = gql_proof::MatchModeDefault::DifferentEdges;
            let conformance = Conformance::load(CONFORMANCE_JSON).unwrap();
            let claim = Claim::parse(&claim, &conformance).unwrap();
            let forbidden = conformance.forbidden(&claim);
            let iso_start = iso.require("GQL-program").unwrap();
            let mut rules = all_rules(id086);
            rules.push(Box::new(ClaimRules::new(&iso, iso_start, &forbidden, &[]).unwrap()));
            let refined = refine(&iso, &rules, iso_start).unwrap();
            (refined.cfg, refined.start)
        }
        Err(_) => (iso.clone(), iso.require("GQL-program").unwrap()),
    };
    let iso = base;
    let tokens = Grammar::new(&bnf);
    let verifier = Verifier::new(Grammar::new(&bnf));
    let parser = Parser::new(&iso, &tokens, &iso.name(start).to_string()).unwrap();
    // GQL_PARSE_FIRST=<def>:<child>: of an ambiguous sentence, take a tree where some
    // <def> has <child> as its first non-synthetic child (the generator's derivation).
    let wanted = std::env::var("GQL_PARSE_FIRST").ok();
    fn has_first(p: &gql_proof::verify::Plain, def: &str, child: &str) -> bool {
        use gql_proof::verify::Plain;
        fn first(p: &Plain) -> Option<String> {
            if let Plain::Def { children, .. } = p {
                for c in children {
                    match c {
                        Plain::Def { synthetic: true, .. } => {
                            if let Some(f) = first(c) {
                                return Some(f);
                            }
                        }
                        Plain::Def { name, .. } => return Some(name.clone()),
                        _ => return None,
                    }
                }
            }
            None
        }
        match p {
            Plain::Def { name, children, .. } => {
                (name == def && first(p).as_deref() == Some(child))
                    || children.iter().any(|c| has_first(c, def, child))
            }
            _ => false,
        }
    }
    let parsed = parser
        .parse(&text, |n| {
            let plain = n.export(&iso);
            verifier.verify(&plain, &n.render(&iso)).is_empty()
                && wanted.as_deref().is_none_or(|w| {
                    let (d, c) = w.split_once(':').unwrap();
                    has_first(&plain, d, c)
                })
        })
        .unwrap();
    let plain = parsed.tree.export(&iso);
    let scope = gql_proof::context::scope::Scope {
        caps: gql_proof::context::scope::Caps { slots: 2, references: 2 },
    };
    let mut types = gql_proof::context::types::Types::with_typed(&iso, 2);
    types.fold = true;
    let pair = gql_proof::context::pair::Typed::new(scope, types);
    println!("accepts as is: {:?}", gql_proof::context::accepts(&pair, &plain));
    println!("classes: {:?}", gql_proof::context::parameter_classes(&pair, &plain, &param));
}
