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
    let tokens = Grammar::new(&bnf);
    let verifier = Verifier::new(Grammar::new(&bnf));
    let parser = Parser::new(&iso, &tokens, "GQL-program").unwrap();
    let parsed = parser
        .parse(&text, |n| verifier.verify(&n.export(&iso), &n.render(&iso)).is_empty())
        .unwrap();
    let plain = parsed.tree.export(&iso);
    let scope = gql_proof::context::scope::Scope {
        caps: gql_proof::context::scope::Caps { slots: 2, references: 2 },
    };
    let mut types = gql_proof::context::types::Types::new(&iso);
    types.fold = true;
    let pair = gql_proof::context::pair::Typed::new(scope, types);
    println!("accepts as is: {:?}", gql_proof::context::accepts(&pair, &plain));
    println!("classes: {:?}", gql_proof::context::parameter_classes(&pair, &plain, &param));
}
