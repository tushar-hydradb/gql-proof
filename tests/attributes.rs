//! Refinement with state flowing left to right, rules that choose, and copies whose text a
//! rule fixes, on a toy language: `LET x` binds a name, `USE x` needs it bound before.

use gql_proof::bnf;
use gql_proof::cfg::Cfg;
use gql_proof::leaf::StubProvider;
use gql_proof::purdom::{Analysis, Config, Generator, Length};
use gql_proof::refine::{Fact, Item, Node, Rule, State, accepts, refine};
use gql_proof::verify::Plain;
use std::collections::BTreeSet;

const TOY: &str = r#"<grammar>
<BNFdef name="s"><rhs><BNF name="stmt"/><repeat/></rhs></BNFdef>
<BNFdef name="stmt"><rhs>
  <alt><kw>LET</kw><BNF name="var"/></alt>
  <alt><kw>USE</kw><BNF name="var"/></alt>
</rhs></BNFdef>
<BNFdef name="var"><rhs><BNF name="letter"/></rhs></BNFdef>
<BNFdef name="letter"><rhs><alt><kw>x</kw></alt><alt><kw>y</kw></alt><alt><kw>z</kw></alt></rhs></BNFdef>
</grammar>"#;

/// Names the rule knows; `z` is not one, so no tree may spell it.
const NAMES: [&str; 2] = ["x", "y"];

fn named(i: usize) -> Fact {
    i as Fact
}

fn bound(i: usize) -> Fact {
    (NAMES.len() + i) as Fact
}

struct LetBeforeUse;

impl Rule for LetBeforeUse {
    fn name(&self) -> &str {
        "let before use"
    }

    fn cite(&self) -> &str {
        "toy: a name is used only after a LET binds it"
    }

    fn labels(&self) -> Vec<(Fact, String)> {
        (0..NAMES.len())
            .flat_map(|i| {
                [
                    (named(i), NAMES[i].to_string()),
                    (bound(i), format!("bound-{}", NAMES[i])),
                ]
            })
            .collect()
    }

    fn down(&self, _node: &Node, inh: &State, _pos: usize, left: &[State], out: &mut State) {
        for i in 0..NAMES.len() {
            if inh.has(bound(i)) || left.iter().any(|s| s.has(bound(i))) {
                out.set(bound(i), true);
            }
        }
    }

    fn steps(&self, node: &Node, inh: &State, _children: &[State], syn: State) -> Vec<State> {
        if node.group {
            return vec![syn];
        }
        match node.def {
            "var" => (0..NAMES.len())
                .filter(|&i| node.text.is_none_or(|t| t == NAMES[i]))
                .map(|i| syn.clone().with(named(i)))
                .collect(),
            "stmt" => {
                let Some(i) = (0..NAMES.len()).find(|&i| syn.has(named(i))) else {
                    return vec![];
                };
                let syn = syn.without(named(i));
                match node.items[0] {
                    Item::Token("LET") => vec![syn.with(bound(i))],
                    _ if inh.has(bound(i)) => vec![syn],
                    _ => vec![],
                }
            }
            _ => vec![syn],
        }
    }

    fn text(&self, def: &str, syn: &State) -> Option<String> {
        (def == "var")
            .then(|| (0..NAMES.len()).find(|&i| syn.has(named(i))))
            .flatten()
            .map(|i| NAMES[i].to_string())
    }
}

fn toy() -> Cfg {
    Cfg::from_bnf(&bnf::parse(TOY).unwrap())
}

fn sentences(cfg: &Cfg, start: u32) -> Vec<String> {
    let analysis = Analysis::new(cfg, &StubProvider);
    let mut out = Vec::new();
    for seed in 0..8 {
        let config = Config {
            seed,
            max_depth: 12,
            length: Length::Unbounded,
        };
        let outcome = Generator::new(&analysis, config, StubProvider)
            .run(start)
            .unwrap();
        out.extend(outcome.trees.iter().map(|t| t.root.render(cfg)));
    }
    out
}

/// The toy rule read directly from a sentence.
fn valid(sentence: &str) -> bool {
    let words: Vec<&str> = sentence.split_whitespace().collect();
    let mut bound = BTreeSet::new();
    for pair in words.chunks(2) {
        let [stmt, name] = pair else { return false };
        if !NAMES.contains(name) {
            return false;
        }
        match *stmt {
            "LET" => {
                bound.insert(*name);
            }
            _ if bound.contains(name) => {}
            _ => return false,
        }
    }
    true
}

#[test]
fn refined_sentences_use_only_bound_names() {
    let cfg = toy();
    let rules: Vec<Box<dyn Rule>> = vec![Box::new(LetBeforeUse)];
    let refined = refine(&cfg, &rules, cfg.require("s").unwrap()).unwrap();
    let all = sentences(&refined.cfg, refined.start);
    assert!(!all.is_empty());
    for s in &all {
        assert!(valid(s), "{s:?}");
    }
    // Not vacuous: uses survive, after their LET, with both names.
    assert!(all.iter().any(|s| s.contains("USE x")), "{all:?}");
    assert!(all.iter().any(|s| s.contains("USE y")), "{all:?}");
}

#[test]
fn copies_spell_only_the_names_the_rule_knows() {
    // Like `<binding variable>` over a lexical `<regular identifier>`: the rule picks the
    // name of each `var` copy and fixes its text, the letters below stay a plain grammar.
    let cfg = toy();
    let rules: Vec<Box<dyn Rule>> = vec![Box::new(LetBeforeUse)];
    let refined = refine(&cfg, &rules, cfg.require("s").unwrap()).unwrap();
    let spelled: Vec<(&str, &str)> = refined
        .cfg
        .nts
        .iter()
        .filter_map(|n| n.text.as_deref().map(|t| (n.base.as_str(), t)))
        .collect();
    let names: BTreeSet<&str> = spelled.iter().map(|&(_, t)| t).collect();
    assert!(
        spelled.iter().all(|&(base, _)| base == "var"),
        "{spelled:?}"
    );
    assert_eq!(names, BTreeSet::from(["x", "y"]));
    let all = sentences(&refined.cfg, refined.start);
    assert!(all.iter().all(|s| !s.contains('z')), "{all:?}");
}

#[test]
fn checking_a_given_tree_reads_its_names() {
    let cfg = toy();
    let rules: Vec<Box<dyn Rule>> = vec![Box::new(LetBeforeUse)];
    // Trees of the unrefined grammar break the rule as often as not; the automaton run on a
    // given tree must agree with the direct reading.
    let analysis = Analysis::new(&cfg, &StubProvider);
    let mut seen = BTreeSet::new();
    for seed in 0..32 {
        let config = Config {
            seed,
            max_depth: 12,
            length: Length::Unbounded,
        };
        let outcome = Generator::new(&analysis, config, StubProvider)
            .run(cfg.require("s").unwrap())
            .unwrap();
        for t in &outcome.trees {
            let sentence = t.root.render(&cfg);
            let tree: Plain = t.root.export(&cfg);
            assert_eq!(
                accepts(&rules, &tree).is_ok(),
                valid(&sentence),
                "{sentence:?}"
            );
            seen.insert(valid(&sentence));
        }
    }
    assert_eq!(seen.len(), 2, "both verdicts occur");
}
