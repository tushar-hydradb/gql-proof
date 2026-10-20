//! The independent checkers must reject what is wrong, not just accept what the generator
//! makes. Every test here builds or mutates a tree so that exactly one rule breaks, and checks
//! that rule is the one reported.

use gql_proof::ISO_BNF_XML;
use gql_proof::bnf::{self, Bnf};
use gql_proof::cfg::Cfg;
use gql_proof::leaf::StubProvider;
use gql_proof::purdom::{Analysis, Config, Generator, Length};
use gql_proof::tokens::Grammar;
use gql_proof::verify::{Plain, Verifier, Violation};
use std::sync::LazyLock;

static ISO: LazyLock<Bnf> = LazyLock::new(|| bnf::parse(ISO_BNF_XML).unwrap());

fn verifier() -> Verifier<'static> {
    Verifier::new(Grammar::new(&ISO))
}

fn def(name: &str, children: Vec<Plain>) -> Plain {
    Plain::Def {
        name: name.into(),
        synthetic: false,
        children,
    }
}

fn leaf(def_name: &str, text: &str) -> Plain {
    def(
        def_name,
        vec![Plain::Leaf {
            def: def_name.into(),
            text: text.into(),
        }],
    )
}

fn term_def(name: &str, t: &str) -> Plain {
    def(name, vec![Plain::Term(t.into())])
}

/// Verifies with the checker's own rendering, so only tree rules are under test.
fn check(tree: &Plain) -> Vec<Violation> {
    let v = verifier();
    let rendered = v.render(tree);
    v.verify(tree, &rendered)
}

fn rules(violations: &[Violation]) -> Vec<&'static str> {
    violations.iter().map(|v| v.rule).collect()
}

fn generated(seed: u64) -> Vec<(Plain, String)> {
    let cfg = Cfg::from_bnf(&ISO);
    let config = Config {
        seed,
        max_depth: 46,
        length: Length::Cap(60),
    };
    let analysis = Analysis::new(&cfg, &StubProvider);
    let outcome = Generator::new(&analysis, config, StubProvider)
        .run(cfg.require("GQL-program").unwrap())
        .unwrap();
    outcome
        .trees
        .iter()
        .map(|t| (t.root.export(&cfg), t.root.render(&cfg)))
        .collect()
}

/// The biggest tree for seed 1, so mutations have plenty to work on.
fn largest() -> (Plain, String) {
    generated(1)
        .into_iter()
        .max_by_key(|(_, rendered)| rendered.len())
        .unwrap()
}

/// The first real node, in preorder, for which `f` returns a changed copy.
fn mutate_first(node: &Plain, f: &dyn Fn(&Plain) -> Option<Plain>) -> Option<Plain> {
    if let Some(changed) = f(node) {
        return Some(changed);
    }
    let Plain::Def {
        name,
        synthetic,
        children,
    } = node
    else {
        return None;
    };
    for (i, child) in children.iter().enumerate() {
        if let Some(changed) = mutate_first(child, f) {
            let mut children = children.clone();
            children[i] = changed;
            return Some(Plain::Def {
                name: name.clone(),
                synthetic: *synthetic,
                children,
            });
        }
    }
    None
}

// --- the ISO grammar passes, with exactly the stated assumptions -------------------------

#[test]
fn iso_token_boundaries_hold() {
    let report = Grammar::new(&ISO).check("GQL-program");
    assert!(report.passed(), "{:?}", report.failures);
    let assumed: Vec<&str> = report.assumptions.iter().map(|(d, _)| *d).collect();
    assert_eq!(
        assumed,
        [
            "SQL-datetime literal",
            "SQL-interval literal",
            "external object reference"
        ]
    );
    let excluded: Vec<&str> = report.excluded.iter().map(|(d, _)| *d).collect();
    assert_eq!(excluded, ["implementation-defined access mode"]);
}

#[test]
fn generated_trees_verify() {
    for seed in [1, 2, 3] {
        for (tree, rendered) in generated(seed) {
            let v = verifier().verify(&tree, &rendered);
            assert!(v.is_empty(), "seed {seed}: {v:?}\n{rendered}");
        }
    }
}

// --- static check on toy grammars ----------------------------------------------------------

fn toy(defs: &str) -> Bnf {
    bnf::parse(&format!("<grammar>{defs}</grammar>")).unwrap()
}

const TOY_TOKENS: &str = r#"
<BNFdef name="token"><rhs><alt><BNF name="word"/></alt><alt><BNF name="float"/></alt></rhs></BNFdef>
<BNFdef name="word"><rhs><alt><kw>GO</kw></alt><alt><kw>STOP</kw></alt></rhs></BNFdef>
<BNFdef name="float"><rhs><BNF name="num"/><terminalsymbol>.</terminalsymbol><BNF name="num"/></rhs></BNFdef>
<BNFdef name="num"><rhs><terminalsymbol>1</terminalsymbol><opt><terminalsymbol>1</terminalsymbol><repeat/></opt></rhs></BNFdef>
<BNFdef name="reserved word"><rhs><kw>GO</kw></rhs></BNFdef>
<BNFdef name="pre-reserved word"><rhs><kw>STOP</kw></rhs></BNFdef>"#;

fn toy_failures(syntactic: &str) -> Vec<String> {
    let bnf = toy(&format!("{TOY_TOKENS}{syntactic}"));
    Grammar::new(&bnf).check("s").failures
}

#[test]
fn static_check_accepts_a_sound_toy() {
    let failures = toy_failures(
        r#"<BNFdef name="s"><rhs><BNF name="word"/><BNF name="float"/><kw>GO</kw></rhs></BNFdef>"#,
    );
    assert!(failures.is_empty(), "{failures:?}");
}

#[test]
fn static_check_flags_a_lexical_non_token() {
    // <num> is lexical (inside <float>) but is never a whole token on its own.
    let failures = toy_failures(r#"<BNFdef name="s"><rhs><BNF name="num"/></rhs></BNFdef>"#);
    assert_eq!(failures.len(), 1);
    assert!(failures[0].contains("<num>"), "{failures:?}");
}

#[test]
fn static_check_flags_a_literal_that_is_not_a_token() {
    let failures = toy_failures(r#"<BNFdef name="s"><rhs><kw>JUMP</kw></rhs></BNFdef>"#);
    assert_eq!(failures, ["keyword JUMP in <s> is not a token"]);
}

#[test]
fn static_check_flags_an_unjustified_prose_leaf() {
    let failures = toy_failures(
        r#"<BNFdef name="s"><rhs><BNF name="p"/></rhs></BNFdef>
           <BNFdef name="p"><rhs><seeTheRules/></rhs></BNFdef>"#,
    );
    assert_eq!(failures.len(), 1);
    assert!(failures[0].contains("<p>"), "{failures:?}");
}

#[test]
fn static_check_flags_an_empty_token() {
    let bnf = toy(r#"<BNFdef name="token"><rhs><BNF name="w"/></rhs></BNFdef>
           <BNFdef name="w"><rhs><opt><kw>A</kw></opt></rhs></BNFdef>
           <BNFdef name="reserved word"><rhs><kw>A</kw></rhs></BNFdef>
           <BNFdef name="pre-reserved word"><rhs><kw>A</kw></rhs></BNFdef>
           <BNFdef name="s"><rhs><BNF name="w"/></rhs></BNFdef>"#);
    let failures = Grammar::new(&bnf).check("s").failures;
    assert!(
        failures.iter().any(|f| f.contains("empty string")),
        "{failures:?}"
    );
}

// --- ISO EBNF conformance, on mutated real trees -----------------------------------------

#[test]
fn rejects_swapped_children() {
    let (tree, _) = largest();
    let swapped = mutate_first(&tree, &|n| match n {
        Plain::Def {
            name,
            synthetic: false,
            children,
        } if children.len() >= 2 => {
            // Two real children with different names; grouping nodes may be empty, and
            // swapping two empty groups changes nothing.
            let real = |p: &Plain| match p {
                Plain::Def {
                    name,
                    synthetic: false,
                    ..
                } => Some(name.clone()),
                _ => None,
            };
            let differ =
                matches!((real(&children[0]), real(&children[1])), (Some(a), Some(b)) if a != b);
            differ.then(|| {
                let mut children = children.clone();
                children.swap(0, 1);
                Plain::Def {
                    name: name.clone(),
                    synthetic: false,
                    children,
                }
            })
        }
        _ => None,
    })
    .expect("a node with two different children");
    assert!(rules(&check(&swapped)).contains(&"ISO BNF"));
}

#[test]
fn rejects_a_wrong_keyword() {
    let (tree, _) = largest();
    let changed = mutate_first(&tree, &|n| match n {
        Plain::Kw(_) => Some(Plain::Kw("BOGUS".into())),
        _ => None,
    })
    .expect("a keyword");
    assert!(rules(&check(&changed)).contains(&"ISO BNF"));
}

#[test]
fn rejects_a_dropped_child() {
    let (tree, _) = largest();
    let dropped = mutate_first(&tree, &|n| match n {
        Plain::Def {
            name,
            synthetic: false,
            children,
        } if children.len() >= 2 => Some(Plain::Def {
            name: name.clone(),
            synthetic: false,
            children: children[1..].to_vec(),
        }),
        _ => None,
    })
    .unwrap();
    assert!(rules(&check(&dropped)).contains(&"ISO BNF"));
}

#[test]
fn rejects_tampered_rendering() {
    let (tree, rendered) = largest();
    let v = verifier().verify(&tree, &format!("{rendered} ;"));
    assert_eq!(rules(&v), ["21.3 SR 13, 14"]);
}

// --- prose leaves and token-internal Syntax Rules ----------------------------------------

fn regular_identifier(start: &str, extend: &[&str]) -> Plain {
    let mut children = vec![leaf("identifier start", start)];
    children.extend(extend.iter().map(|c| leaf("identifier extend", c)));
    def("regular identifier", children)
}

#[test]
fn accepts_a_plain_identifier() {
    assert_eq!(check(&regular_identifier("a", &["b"])), []);
}

#[test]
fn rejects_an_identifier_starting_with_a_digit() {
    assert_eq!(
        rules(&check(&regular_identifier("1", &["b"]))),
        ["21.3 SR 1"]
    );
}

#[test]
fn rejects_a_reserved_word_as_identifier() {
    let id = regular_identifier("m", &["a", "t", "c", "h"]);
    assert_eq!(rules(&check(&id)), ["21.3 SR 18"]);
}

fn quote() -> Plain {
    term_def("quote", "'")
}

fn byte_string(separator: Plain) -> Plain {
    let x = Plain::Term("X".into());
    def(
        "byte string literal",
        vec![
            x,
            quote(),
            quote(),
            def("separator", vec![separator]),
            quote(),
            quote(),
        ],
    )
}

#[test]
fn accepts_a_byte_string_continued_after_a_newline() {
    assert_eq!(check(&byte_string(leaf("whitespace", "\n"))), []);
}

#[test]
fn rejects_a_byte_string_continued_without_a_newline() {
    assert_eq!(
        rules(&check(&byte_string(leaf("whitespace", " ")))),
        ["21.2 SR 57"]
    );
}

fn quoted_string(def_name: &str, content: &str) -> Plain {
    let mut inner = vec![quote()];
    inner.extend(content.chars().map(|c| {
        def(
            "single quoted character representation",
            vec![leaf("character representation", &c.to_string())],
        )
    }));
    inner.push(quote());
    let unbroken = def("unbroken single quoted character sequence", inner);
    let sequence = def("single quoted character sequence", vec![unbroken]);
    def(
        def_name,
        vec![def("character string literal", vec![sequence])],
    )
}

#[test]
fn accepts_iso8601_strings() {
    assert_eq!(check(&quoted_string("duration string", "P1Y2M")), []);
    assert_eq!(check(&quoted_string("duration string", "PT3H")), []);
    assert_eq!(check(&quoted_string("date string", "2024-02-29")), []);
}

#[test]
fn rejects_non_iso8601_strings() {
    assert_eq!(
        rules(&check(&quoted_string("duration string", "x"))),
        ["21.2 SR 68"]
    );
    assert_eq!(
        rules(&check(&quoted_string("date string", "2023-02-29"))),
        ["21.2 SR 59"]
    );
    assert_eq!(
        rules(&check(&quoted_string("time string", "25:00:00"))),
        ["21.2 SR 62"]
    );
}

#[test]
fn rejects_an_excluded_leaf() {
    let mode = leaf("implementation-defined access mode", "FAST");
    assert_eq!(rules(&check(&mode)), ["excluded"]);
}
