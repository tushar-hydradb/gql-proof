use gql_proof::ISO_BNF_XML;
use gql_proof::bnf;
use gql_proof::cfg::Cfg;
use gql_proof::leaf::StubProvider;
use gql_proof::parse::Parser;
use gql_proof::purdom::{Analysis, Config, Generator, Length};
use gql_proof::tokens::Grammar;
use gql_proof::tree::Node;
use gql_proof::verify::Verifier;
use std::sync::LazyLock;

static ISO_BNF: LazyLock<bnf::Bnf> = LazyLock::new(|| bnf::parse(ISO_BNF_XML).unwrap());
static ISO: LazyLock<Cfg> = LazyLock::new(|| Cfg::from_bnf(&ISO_BNF));

fn parse(text: &str) -> anyhow::Result<Node> {
    let tokens = Grammar::new(&ISO_BNF);
    let verifier = Verifier::new(Grammar::new(&ISO_BNF));
    let parser = Parser::new(&ISO, &tokens, "GQL-program")?;
    let parsed = parser.parse(text, |n| {
        verifier.verify(&n.export(&ISO), &n.render(&ISO)).is_empty()
    })?;
    assert!(parsed.accepted, "{text:?} parses but fails the verifier");
    Ok(parsed.tree)
}

#[test]
fn every_sentence_purdom_generates_reads_back() {
    let analysis = Analysis::new(&ISO, &StubProvider);
    let config = Config {
        seed: 0,
        max_depth: 46,
        length: Length::Reference,
    };
    let outcome = Generator::new(&analysis, config, StubProvider)
        .run(ISO.require("GQL-program").unwrap())
        .unwrap();
    for generated in &outcome.trees {
        let sentence = generated.root.render(&ISO);
        let tree = parse(&sentence).unwrap_or_else(|e| panic!("{sentence:?}: {e}"));
        // The same characters, not always the same tokens: `8.M` is a decimal literal or
        // property M of 8 until types decide (20.11).
        let squash = |s: &str| s.split_whitespace().collect::<String>();
        assert_eq!(squash(&tree.render(&ISO)), squash(&sentence));
    }
}

#[test]
fn tokens_follow_21_3() {
    // SR 25: keywords in either case.
    assert_eq!(
        parse("return 1 as v").unwrap().render(&ISO),
        "RETURN 1 AS v"
    );
    // SR 14: a non-delimiter token needs a delimiter or a separator after it.
    assert!(parse("RETURN1").is_err());
    assert!(parse("RETURN(1)").is_ok());
    // A separator is any run of whitespace and comments, and may end the text.
    assert!(parse("RETURN /* c */ 1 -- d\n").is_ok());
    // Lexing leaves `->` against `-` `>` to the syntax.
    assert!(parse("MATCH (a)->(b) RETURN a").is_ok());
    assert!(parse("RETURN 1 - -1 > 0").is_ok());
}

#[test]
fn reserved_words_are_no_identifiers() {
    // 21.3 SR 18, TYPE reserved since Cor 1. A label may be delimited, a binding variable
    // is a <regular identifier> only.
    assert!(parse("MATCH (type) RETURN 1").is_err());
    assert!(parse("MATCH (a:\"type\") RETURN 1").is_ok());
    assert!(parse("MATCH (\"a\") RETURN 1").is_err());
}
