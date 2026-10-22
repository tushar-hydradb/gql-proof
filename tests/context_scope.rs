//! Scoping as a context (`context::scope`): every generated tree references only variables in
//! scope and declares only new names, and the grammar it emits stays small.

use gql_proof::cfg::Cfg;
use gql_proof::context::scope::Scope;
use gql_proof::context::{Options, accepts, build};
use gql_proof::leaf::StubProvider;
use gql_proof::purdom::{Analysis, Config, Generator, Length};
use gql_proof::{ISO_BNF_XML, bnf};
use std::sync::LazyLock;
use std::time::Instant;

static ISO: LazyLock<bnf::Bnf> = LazyLock::new(|| bnf::parse(ISO_BNF_XML).unwrap());
static BASE: LazyLock<Cfg> = LazyLock::new(|| Cfg::from_bnf(&ISO));

const NAMES: [&str; 4] = ["x", "y", "z", "w"];

/// The context's verdict on a sentence, read with the ISO parser.
fn verdict(text: &str) -> Result<(), String> {
    use gql_proof::parse::Parser;
    use gql_proof::tokens::Grammar;
    use gql_proof::verify::Verifier;
    let tokens = Grammar::new(&ISO);
    let verifier = Verifier::new(Grammar::new(&ISO));
    let parser = Parser::new(&BASE, &tokens, "GQL-program").unwrap();
    let parsed = parser
        .parse(text, |n| {
            verifier
                .verify(&n.export(&BASE), &n.render(&BASE))
                .is_empty()
        })
        .unwrap_or_else(|e| panic!("{text:?}: {e}"));
    accepts(&Scope::default(), &parsed.tree.export(&BASE))
}

#[test]
fn probes() {
    for ok in [
        "MATCH (x) RETURN x",
        "MATCH (x) RETURN count(*) AS y",
        "MATCH (x)-[y]->() RETURN x, y",
        "MATCH (x) CALL (x) { RETURN 1 AS y } RETURN y",
        "LET x = 1 RETURN x",
        "FOR x IN [1] RETURN x AS y",
        "MATCH (x) RETURN x AS y NEXT RETURN y",
        "RETURN 1 AS x UNION RETURN 2 AS x",
        "MATCH (x) MATCH (x)-[y]->() RETURN y",
        "MATCH (x) RETURN x, count(*) AS y GROUP BY x",
        "MATCH (x) RETURN x ORDER BY x",
        "LET x = 1 RETURN LET y = x IN y END AS z",
    ] {
        assert_eq!(verdict(ok), Ok(()), "{ok:?}");
    }
    for bad in [
        "RETURN x",
        "MATCH (x) LET x = 1 RETURN x",
        "MATCH (x)-[x]->() RETURN x",
        "MATCH (x) RETURN x NEXT RETURN y",
        "RETURN 1 AS x UNION RETURN 2 AS y",
        "FILTER count(*) > 0 RETURN 1 AS x",
        "MATCH (x) RETURN x, count(*) AS y GROUP BY y",
        "MATCH (x) RETURN x + 1",
        "MATCH (x) RETURN x, x",
    ] {
        assert!(verdict(bad).is_err(), "{bad:?} accepted");
    }
}

/// Every generated tree passes the independent checker.
#[test]
fn generated_trees_pass_the_checker() {
    let start = BASE.require("GQL-program").unwrap();
    let t = Instant::now();
    let built = build(&BASE, &Scope::default(), start, "x", &Options::default()).unwrap();
    eprintln!(
        "built in {:?}: {} nonterminals, {} productions (base {} / {})",
        t.elapsed(),
        built.cfg.nts.len(),
        built.cfg.prods.len(),
        BASE.nts.len(),
        BASE.prods.len()
    );
    let names: Vec<String> = NAMES.iter().map(|s| s.to_string()).collect();
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
            let violations = gql_proof::verify::scope::check(&root.export(&built.cfg));
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

/// The labels at every node of one sentence: `GQL_TEXT='...' cargo test --release --test
/// context_scope explain -- --ignored --nocapture`.
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

/// What a set of trees uses: productions, (occurrence, production) pairs, and two-step
/// chains (occurrence, production, occurrence, production), all by base id.
#[derive(Default)]
struct Uses {
    prods: std::collections::BTreeSet<u32>,
    pairs: std::collections::BTreeSet<(u32, u32)>,
    chains: std::collections::BTreeSet<(u32, u32, u32, u32)>,
}

fn tree_uses(cfg: &Cfg, t: &gql_proof::tree::Node, u: &mut Uses) {
    let Some(q) = t.prod else { return };
    let qp = &cfg.prods[q as usize];
    u.prods.insert(qp.unrefined);
    for (i, c) in t.children.iter().enumerate() {
        let Some(p) = c.prod else { continue };
        let pp = &cfg.prods[p as usize];
        u.pairs.insert((qp.occ[i], pp.unrefined));
        for (j, g) in c.children.iter().enumerate() {
            if let Some(r) = g.prod {
                u.chains.insert((
                    qp.occ[i],
                    pp.unrefined,
                    pp.occ[j],
                    cfg.prods[r as usize].unrefined,
                ));
            }
        }
        tree_uses(cfg, c, u);
    }
}

/// What a grammar can derive: the same three, read off its productions.
fn grammar_uses(cfg: &Cfg) -> Uses {
    use gql_proof::cfg::Sym;
    let mut u = Uses::default();
    for q in &cfg.prods {
        u.prods.insert(q.unrefined);
        for (i, sym) in q.rhs.iter().enumerate() {
            let Sym::Nt(c) = sym else { continue };
            for &p in &cfg.nts[*c as usize].prods {
                let pp = &cfg.prods[p as usize];
                u.pairs.insert((q.occ[i], pp.unrefined));
                for (j, s2) in pp.rhs.iter().enumerate() {
                    let Sym::Nt(g) = s2 else { continue };
                    for &r in &cfg.nts[*g as usize].prods {
                        u.chains.insert((
                            q.occ[i],
                            pp.unrefined,
                            pp.occ[j],
                            cfg.prods[r as usize].unrefined,
                        ));
                    }
                }
            }
        }
    }
    u
}

/// The totality claim against real queries: every turbolay#261 query the rule accepts at 3
/// variables is a valid tree, so what it uses must be in the emitted grammar. Productions
/// and cdrc pairs are proven to be (research/totality); two-step chains are not, and this
/// measures how many go missing. `just corpus-261 <worktree>` writes the corpus first.
#[test]
#[ignore]
fn corpus_uses_are_emitted() {
    use gql_proof::parse::Parser;
    use gql_proof::tokens::Grammar;
    use gql_proof::verify::Verifier;
    use rayon::prelude::*;
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/engines/corpus-261.jsonl");
    let text = std::fs::read_to_string(&path).expect("run `just corpus-261 <worktree>` first");
    let sentences: std::collections::BTreeSet<String> = text
        .lines()
        .filter_map(|l| serde_json::from_str::<serde_json::Value>(l).ok())
        .filter_map(|v| {
            v.get("query")
                .or(v.get("sentence"))
                .and_then(|q| q.as_str())
                .map(String::from)
        })
        .collect();
    let scope = Scope::default();
    // Deep parse trees need more stack than rayon's default.
    let pool = rayon::ThreadPoolBuilder::new()
        .stack_size(256 << 20)
        .build()
        .unwrap();
    let trees: Vec<gql_proof::tree::Node> = pool.install(|| {
        sentences
            .par_iter()
            .map_init(
                || {
                    let tokens = Grammar::new(&ISO);
                    let verifier = Verifier::new(Grammar::new(&ISO));
                    (
                        Parser::new(&BASE, &tokens, "GQL-program").unwrap(),
                        verifier,
                    )
                },
                |(parser, verifier), s| {
                    let parsed = parser
                        .parse(s, |n| {
                            verifier
                                .verify(&n.export(&BASE), &n.render(&BASE))
                                .is_empty()
                        })
                        .ok()?;
                    accepts(&scope, &parsed.tree.export(&BASE)).ok()?;
                    Some(parsed.tree)
                },
            )
            .flatten()
            .collect()
    });
    let mut used = Uses::default();
    for t in &trees {
        tree_uses(&BASE, t, &mut used);
    }
    let start = BASE.require("GQL-program").unwrap();
    let built = build(
        &BASE,
        &scope,
        start,
        "x",
        &Options {
            progress: false,
            ..Options::default()
        },
    )
    .unwrap();
    let have = grammar_uses(&built.cfg);
    let mp: Vec<_> = used.prods.difference(&have.prods).collect();
    let mq: Vec<_> = used.pairs.difference(&have.pairs).collect();
    let mc: Vec<_> = used.chains.difference(&have.chains).collect();
    eprintln!(
        "{} distinct queries, {} accepted at 3 variables\nproductions: {} used, {} missing\npairs: {} used, {} missing\nchains: {} used, {} missing",
        sentences.len(),
        trees.len(),
        used.prods.len(),
        mp.len(),
        used.pairs.len(),
        mq.len(),
        used.chains.len(),
        mc.len()
    );
    for (o1, p2, o2, p3) in mc.iter().take(10) {
        eprintln!(
            "  chain missing: in <{}> {} then in <{}> {}",
            BASE.occs[*o1 as usize].owner,
            gql_proof::describe(&BASE, *p2),
            BASE.occs[*o2 as usize].owner,
            gql_proof::describe(&BASE, *p3)
        );
    }
    assert!(mp.is_empty(), "productions missing: {mp:?}");
    assert!(mq.is_empty(), "pairs missing: {mq:?}");
}

/// What the emitted grammar covers at caps 1 to `GQL_MAX_SLOTS` (default 3): productions,
/// cdrc pairs and two-step chains, and what each cap adds over the one before. Where a cap
/// adds nothing, raising it covers nothing more of these.
#[test]
#[ignore]
fn coverage_by_cap() {
    use gql_proof::context::scope::Caps;
    let start = BASE.require("GQL-program").unwrap();
    let max: usize = std::env::var("GQL_MAX_SLOTS").map_or(3, |s| s.parse().unwrap());
    let mut before: Option<Uses> = None;
    for slots in 1..=max {
        let t = Instant::now();
        let scope = Scope {
            caps: Caps {
                slots,
                references: slots,
            },
        };
        let built = build(
            &BASE,
            &scope,
            start,
            "x",
            &Options {
                progress: false,
                ..Options::default()
            },
        )
        .unwrap();
        let u = grammar_uses(&built.cfg);
        let added = |a: usize, b: Option<usize>| b.map_or(a as i64, |b| a as i64 - b as i64);
        eprintln!(
            "slots {slots}: productions {} (+{}), pairs {} (+{}), chains {} (+{}), {:?}",
            u.prods.len(),
            added(u.prods.len(), before.as_ref().map(|b| b.prods.len())),
            u.pairs.len(),
            added(u.pairs.len(), before.as_ref().map(|b| b.pairs.len())),
            u.chains.len(),
            added(u.chains.len(), before.as_ref().map(|b| b.chains.len())),
            t.elapsed()
        );
        if let Some(b) = &before {
            for p in u.prods.difference(&b.prods).take(5) {
                eprintln!("  new production: {}", gql_proof::describe(&BASE, *p));
            }
            for (o, p) in u.pairs.difference(&b.pairs).take(5) {
                eprintln!(
                    "  new pair: in <{}> {}",
                    BASE.occs[*o as usize].owner,
                    gql_proof::describe(&BASE, *p)
                );
            }
            assert!(
                b.prods.is_subset(&u.prods) && b.pairs.is_subset(&u.pairs),
                "a larger cap lost something"
            );
        }
        before = Some(u);
    }
}

/// The scope rule's verdict on one sentence at a cap: `GQL_TEXT='...' GQL_SLOTS=2 cargo test
/// --release --test context_scope explain_at -- --ignored --nocapture`, with every node's
/// labels traced.
#[test]
#[ignore]
fn explain_at() {
    use gql_proof::context::scope::{Caps, Scope};
    use gql_proof::parse::Parser;
    use gql_proof::tokens::Grammar;
    use gql_proof::verify::Verifier;
    tracing_subscriber::fmt()
        .with_env_filter("gql_proof::context=trace")
        .with_writer(std::io::stderr)
        .init();
    let text = std::env::var("GQL_TEXT").unwrap();
    let slots: usize = std::env::var("GQL_SLOTS").ok().and_then(|s| s.parse().ok()).unwrap_or(2);
    let rule = Scope {
        caps: Caps {
            slots,
            references: slots,
        },
    };
    let tokens = Grammar::new(&ISO);
    let verifier = Verifier::new(Grammar::new(&ISO));
    let mut parser = Parser::new(&BASE, &tokens, "GQL-program").unwrap();
    parser.limit = 8192;
    let trees = std::cell::RefCell::new(Vec::new());
    let _ = parser.parse(&text, |n| {
        if verifier.verify(&n.export(&BASE), &n.render(&BASE)).is_empty() {
            trees.borrow_mut().push(n.export(&BASE));
        }
        false
    });
    for t in trees.borrow().iter() {
        eprintln!("verdict: {:?}", gql_proof::context::accepts(&rule, t));
    }
}

/// Per-target extraction covers exactly the productions and cdrc pairs the emitted grammar
/// can derive, outside the lexical layer, at a cap (`GQL_SLOTS`, 1 by default): the same
/// fixed point read two ways. Also every extracted sentence passes the scope checker and
/// the rule itself.
#[test]
#[ignore]
fn extraction_matches_emission() {
    use gql_proof::cfg::Sym;
    use gql_proof::context::scope::Caps;
    use gql_proof::coverage::Criteria;
    use std::collections::BTreeSet;
    let slots: usize = std::env::var("GQL_SLOTS").ok().and_then(|s| s.parse().ok()).unwrap_or(1);
    let start = BASE.require("GQL-program").unwrap();
    let rule = Scope {
        caps: Caps {
            slots,
            references: slots,
        },
    };
    let options = Options {
        progress: false,
        ..Options::default()
    };
    // Productions and (occurrence, production) pairs the emitted grammar derives, outside
    // the lexical layer (the generators fix those tokens' text, so trees never vary there).
    let analyzed = gql_proof::context::analyze(&BASE, &rule, &options).unwrap();
    let built = analyzed.emit(start, "x").unwrap();
    let lexical = |p: u32| BASE.nts[BASE.prods[p as usize].lhs as usize].lexical;
    // A spelled name is derived from its text in both paths, never chosen: pairs below one
    // are not something a sentence can cover either way.
    let spelled = |base: &str| matches!(base, "identifier" | "binding variable");
    // A production with a prose leaf the provider cannot fill, or a child no production
    // fills, is never generated either way.
    let mut fillable: Vec<bool> = BASE
        .prods
        .iter()
        .map(|prod| {
            prod.rhs.iter().all(|s| match s {
                Sym::Lit(l) => match &BASE.lits[*l as usize] {
                    gql_proof::cfg::Lit::Opaque(name) => {
                        gql_proof::leaf::LeafProvider::supports(&StubProvider, name)
                    }
                    _ => true,
                },
                Sym::Nt(_) => true,
            })
        })
        .collect();
    loop {
        let before = fillable.clone();
        for (p, prod) in BASE.prods.iter().enumerate() {
            if fillable[p]
                && prod.rhs.iter().any(|s| {
                    matches!(s, Sym::Nt(c) if BASE.nts[*c as usize].prods.iter().all(|&q| !fillable[q as usize]))
                })
            {
                fillable[p] = false;
            }
        }
        if fillable == before {
            break;
        }
    }
    let fillable = |p: u32| fillable[p as usize];
    let (mut e_prods, mut e_pairs) = (BTreeSet::new(), BTreeSet::new());
    for q in &built.cfg.prods {
        if lexical(q.unrefined) || !fillable(q.unrefined) {
            continue;
        }
        e_prods.insert(q.unrefined);
        for (i, sym) in q.rhs.iter().enumerate() {
            let Sym::Nt(c) = sym else { continue };
            if spelled(built.cfg.base(*c)) {
                continue;
            }
            for &p in &built.cfg.nts[*c as usize].prods {
                let pp = &built.cfg.prods[p as usize];
                if !lexical(pp.unrefined) && fillable(pp.unrefined) {
                    e_pairs.insert((q.occ[i], pp.unrefined));
                }
            }
        }
    }
    // The same from the extracted trees.
    let analysis = Analysis::new(&BASE, &StubProvider);
    let names: Vec<String> = ["x", "y", "z", "w"].iter().map(|s| s.to_string()).collect();
    let template = |nt: u32| {
        gql_proof::leaf::LeafProvider::token(&StubProvider, BASE.base(nt))
            .and_then(|t| analysis.spell(nt, t))
    };
    let extractor = analyzed.extractor(start, &StubProvider);
    let covered = extractor.cover(
        Criteria {
            cdrc: true,
            k: 0,
            lexical: false,
        },
        &names,
        |nt, s| analysis.spell(nt, s),
        &template,
        &mut StubProvider,
        1,
        false,
    );
    let (mut x_prods, mut x_pairs) = (BTreeSet::new(), BTreeSet::new());
    fn walk(cfg: &Cfg, n: &gql_proof::tree::Node, prods: &mut BTreeSet<u32>, pairs: &mut BTreeSet<(u32, u32)>) {
        let Some(p) = n.prod else { return };
        let lexical = |p: u32| cfg.nts[cfg.prods[p as usize].lhs as usize].lexical;
        if lexical(p) {
            return;
        }
        prods.insert(p);
        let prod = &cfg.prods[p as usize];
        for (i, c) in n.children.iter().enumerate() {
            let spelled = matches!(c.sym, Sym::Nt(nt) if matches!(cfg.base(nt), "identifier" | "binding variable"));
            if let Some(cp) = c.prod
                && !lexical(cp)
                && !spelled
            {
                pairs.insert((prod.occ[i], cp));
            }
            walk(cfg, c, prods, pairs);
        }
    }
    let mut bad = 0;
    for (root, _) in &covered.trees {
        walk(&BASE, root, &mut x_prods, &mut x_pairs);
        let plain = root.export(&BASE);
        let scope = gql_proof::verify::scope::check(&plain);
        let rule_says = accepts(&rule, &plain);
        if !scope.is_empty() || rule_says.is_err() {
            bad += 1;
            if bad <= 5 {
                eprintln!("{}\n  checker: {scope:?}\n  rule: {rule_says:?}", root.render(&BASE));
            }
        }
    }
    eprintln!(
        "cap {slots}: emission {} productions, {} pairs; extraction {} trees, {} productions, {} pairs; {bad} bad trees",
        e_prods.len(),
        e_pairs.len(),
        covered.trees.len(),
        x_prods.len(),
        x_pairs.len()
    );
    for p in e_prods.difference(&x_prods).take(10) {
        eprintln!("  only emission: {}", gql_proof::describe(&BASE, *p));
    }
    for p in x_prods.difference(&e_prods).take(10) {
        eprintln!("  only extraction: {}", gql_proof::describe(&BASE, *p));
    }
    for (o, p) in e_pairs.difference(&x_pairs).take(10) {
        eprintln!("  pair only emission: occ {o} {}", gql_proof::describe(&BASE, *p));
    }
    for (o, p) in x_pairs.difference(&e_pairs).take(10) {
        eprintln!("  pair only extraction: occ {o} {}", gql_proof::describe(&BASE, *p));
    }
    assert_eq!(e_prods, x_prods);
    assert_eq!(e_pairs, x_pairs);
    assert_eq!(bad, 0);
}
