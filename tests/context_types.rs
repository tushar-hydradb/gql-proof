//! Types under scope (`context::types`): the rule's verdict on sentences read with the ISO
//! parser, and every generated tree passing the independent checkers.

use gql_proof::cfg::Cfg;
use gql_proof::context::pair::Typed;
use gql_proof::context::scope::Scope;
use gql_proof::context::types::Types;
use gql_proof::context::{Options, accepts, build};
use gql_proof::leaf::StubProvider;
use gql_proof::parse::Parser;
use gql_proof::purdom::{Analysis, Config, Generator, Length};
use gql_proof::tokens::Grammar;
use gql_proof::verify::Verifier;
use gql_proof::{ISO_BNF_XML, bnf};
use std::collections::BTreeSet;
use std::sync::LazyLock;

static ISO: LazyLock<bnf::Bnf> = LazyLock::new(|| bnf::parse(ISO_BNF_XML).unwrap());
static BASE: LazyLock<Cfg> = LazyLock::new(|| Cfg::from_bnf(&ISO));

fn rule() -> Typed<Scope, Types> {
    Typed::new(Scope::default(), Types::new(&BASE))
}

/// The verdict on every tree the verifier takes: some tree is typed exactly when the sentence
/// is, the ambiguity of the expression grammar being the types' choice.
fn verdict(text: &str) -> Result<(), String> {
    let tokens = Grammar::new(&ISO);
    let verifier = Verifier::new(Grammar::new(&ISO));
    let mut parser = Parser::new(&BASE, &tokens, "GQL-program").unwrap();
    parser.limit = 8192;
    let trees = std::cell::RefCell::new(Vec::new());
    let _ = parser.parse(text, |n| {
        if verifier
            .verify(&n.export(&BASE), &n.render(&BASE))
            .is_empty()
        {
            trees.borrow_mut().push(n.export(&BASE));
        }
        false
    });
    let trees = trees.into_inner();
    assert!(!trees.is_empty(), "{text:?} has no verified tree");
    let rule = rule();
    let verdicts: Vec<Result<(), String>> = trees.iter().map(|t| accepts(&rule, t)).collect();
    if verdicts.iter().any(Result::is_ok) {
        return Ok(());
    }
    let errors: BTreeSet<String> = verdicts.into_iter().filter_map(Result::err).collect();
    Err(format!(
        "{} trees: {}",
        trees.len(),
        errors.into_iter().collect::<Vec<_>>().join("; ")
    ))
}

/// The labels at every node of one sentence: `GQL_TEXT='...' cargo test --release --test
/// context_types explain -- --ignored --nocapture`.
#[test]
#[ignore]
fn explain() {
    tracing_subscriber::fmt()
        .with_env_filter("gql_proof::context=trace")
        .with_writer(std::io::stderr)
        .init();
    let text = std::env::var("GQL_TEXT").unwrap();
    eprintln!("{:?}", verdict(&text));
}

#[test]
fn typed_sentences_pass() {
    let refused: Vec<String> = [
        "RETURN 1 + 2 AS x",
        "RETURN 1 + 2.5E0 AS x",
        "RETURN 'a' || 'b' AS x",
        "FILTER true FINISH",
        "MATCH (x) FILTER x.k > 1 RETURN x",
        // 21.2 SR 68: a day-time duration has its T even with no time (`P1D` is not one).
        "RETURN CURRENT_DATE + DURATION 'P1DT' AS x",
        "RETURN [] || [] AS x",
        "FOR x IN [1] RETURN x",
        "MATCH (x)-[y]->() RETURN x, y",
        "MATCH (x)-[y]->() FILTER x IS SOURCE OF y RETURN x",
        "RETURN CASE WHEN true THEN 1 ELSE 2 END AS x",
        "RETURN COALESCE(NULL, 1) AS x",
        "RETURN CAST('1' AS INT) AS x",
        "RETURN 1 = 1.0 AS x",
        "RETURN CHAR_LENGTH('ab') AS x",
        "MATCH (x) RETURN count(*) AS y",
        "MATCH (x) RETURN sum(x.k) AS y",
        "RETURN DURATION_BETWEEN(CURRENT_DATE, CURRENT_DATE) AS x",
        "RETURN NOT true AS x",
        "RETURN 1 IS NULL AS x",
        // A value variable keeps its definition's class.
        "LET x = 1 RETURN x + 1 AS y",
        "LET x = true FILTER x RETURN 1 AS y",
        "LET x = 'a' RETURN x || 'b' AS y",
        "MATCH (x) LET y = x.k RETURN y + 1 AS z",
        "MATCH (x), (y) FILTER x = y RETURN x",
        "RETURN 1 AS x NEXT RETURN x + 1 AS y",
        "MATCH (x) RETURN x ORDER BY x.k",
    ]
    .into_iter()
    .filter_map(|ok| verdict(ok).err().map(|e| format!("{ok:?}: {e:.300}")))
    .collect();
    assert!(refused.is_empty(), "{}", refused.join("\n"));
}

#[test]
fn untyped_sentences_are_refused() {
    let accepted: Vec<&str> = [
        "FILTER '' FINISH",
        "RETURN SESSION_USER / SESSION_USER AS x",
        "RETURN LOCAL_TIME + SESSION_USER AS x",
        "RETURN true OR 1 AS x",
        "RETURN CASE WHEN 1 THEN 2 END AS x",
        "RETURN CARDINALITY('a') AS x",
        "FOR x IN 1 RETURN x",
        "RETURN DURATION_BETWEEN(CURRENT_DATE, LOCAL_TIME) AS x",
        "RETURN +'a' AS x",
        "RETURN 'a' = 1 AS x",
        "RETURN CASE WHEN true THEN 1 ELSE 'a' END AS x",
        "RETURN CAST(true AS INT) AS x",
        "MATCH (x)-[y]->() FILTER y IS SOURCE OF x RETURN x",
        "LET x = 'a' RETURN x * 2 AS y",
        "MATCH (x) RETURN sum('a') AS y",
        // A variable's uses meet its binder.
        "MATCH (x) RETURN x + 1 AS y",
        "FOR x IN [1] RETURN x * 2 AS y",
        "LET x = 1 FILTER x RETURN 1 AS y",
        "MATCH (x)-[y]->() FILTER x = y RETURN x",
        "LET x = 1 RETURN x.k AS y",
        "MATCH (x) RETURN x ORDER BY x",
        "RETURN 'a' AS x NEXT RETURN x + 1 AS y",
    ]
    .into_iter()
    .filter(|bad| verdict(bad).is_ok())
    .collect();
    assert!(accepted.is_empty(), "accepted: {accepted:?}");
}

/// What the labels of the widest nonterminals differ in, at one variable: scope's label, the
/// class, the entries. `cargo test --release --test context_types census -- --ignored
/// --nocapture`.
#[test]
#[ignore]
fn census() {
    use gql_proof::context::scope::Caps;
    use std::collections::BTreeMap;
    let rule = Typed::new(
        Scope {
            caps: Caps {
                slots: 1,
                references: 1,
            },
        },
        Types::new(&BASE),
    );
    let options = Options {
        progress: false,
        ..Options::default()
    };
    let analyzed = gql_proof::context::analyze(&BASE, &rule, &options).unwrap();
    let mut widest: Vec<(usize, u32)> = (0..BASE.nts.len() as u32)
        .map(|nt| (analyzed.labels(nt).count(), nt))
        .collect();
    widest.sort_unstable_by(|a, b| b.cmp(a));
    for &(n, nt) in widest.iter().take(12) {
        let mut scope = BTreeSet::new();
        let mut classes: BTreeMap<String, usize> = BTreeMap::new();
        let mut entries: BTreeMap<String, usize> = BTreeMap::new();
        for (a, b) in analyzed.labels(nt) {
            scope.insert(a);
            *classes.entry(format!("{:?}", b.class())).or_default() += 1;
            *entries.entry(format!("{:?}", b.vars())).or_default() += 1;
        }
        eprintln!(
            "{n:>6} <{}>: {} scope labels, {} classes, {} entry lists",
            BASE.nts[nt as usize].name,
            scope.len(),
            classes.len(),
            entries.len()
        );
        let mut top: Vec<(&usize, &String)> = entries.iter().map(|(k, v)| (v, k)).collect();
        top.sort_unstable_by(|a, b| b.cmp(a));
        eprintln!("    entries: {top:?}");
        let mut top: Vec<(&usize, &String)> = classes.iter().map(|(k, v)| (v, k)).collect();
        top.sort_unstable_by(|a, b| b.cmp(a));
        eprintln!("    classes: {:?}", &top[..top.len().min(12)]);
    }
}

/// Every tree generated at one variable passes both checkers.
#[test]
fn generated_trees_pass_the_checkers() {
    use gql_proof::context::scope::Caps;
    let start = BASE.require("GQL-program").unwrap();
    let rule = Typed::new(
        Scope {
            caps: Caps {
                slots: 1,
                references: 1,
            },
        },
        Types::new(&BASE),
    );
    let options = Options {
        progress: false,
        ..Options::default()
    };
    let built = build(&BASE, &rule, start, "x", &options).unwrap();
    eprintln!(
        "{} nonterminals, {} productions, {} labels",
        built.cfg.nts.len(),
        built.cfg.prods.len(),
        built.stats.labels.values().sum::<usize>()
    );
    let names: Vec<String> = ["x", "y", "z"].iter().map(|s| s.to_string()).collect();
    let analysis = Analysis::new(&built.cfg, &StubProvider);
    let height = analysis.reference_height(built.start);
    let mut failed = Vec::new();
    let mut count = 0;
    for seed in 0..2 {
        let config = Config {
            seed,
            max_depth: height,
            length: Length::Reference,
        };
        let outcome = Generator::new(&analysis, config, StubProvider)
            .run(built.start)
            .unwrap();
        for t in outcome.trees {
            let mut root = t.root;
            built
                .name(&mut root, &names, |nt, s| analysis.spell(nt, s))
                .unwrap();
            count += 1;
            let plain = root.export(&built.cfg);
            let mut violations = gql_proof::verify::scope::check(&plain);
            violations.extend(gql_proof::verify::types::check(&plain));
            if !violations.is_empty() {
                failed.push(format!("{}\n  {violations:?}", root.render(&built.cfg)));
            }
        }
    }
    eprintln!("{count} trees, {} fail", failed.len());
    for f in failed.iter().take(12) {
        eprintln!("{f}");
    }
    assert!(failed.is_empty());
}
