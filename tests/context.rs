//! The context engine on a toy language: `LET x` binds a name, `USE x` needs it bound
//! before. Variables are slots up to renaming, so the grammar it emits does not depend on
//! how many names there are.

use gql_proof::bnf;
use gql_proof::cfg::Cfg;
use gql_proof::context::{Context, Link, Nothing, Options, accepts, build};
use gql_proof::leaf::StubProvider;
use gql_proof::purdom::{Analysis, Config, Generator, Length};
use gql_proof::refine::{Item, Node};
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

/// Variables live at once, at most.
const SLOTS: u8 = 3;

/// A subtree's variables: those it needs bound before it (slots `0..need`), those it binds
/// (`need..need + bind`), or the one a `var` spells.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum L {
    Seq { need: u8, bind: u8 },
    Var,
}

struct LetBeforeUse;

impl Context for LetBeforeUse {
    type Label = L;

    fn name(&self) -> &str {
        "let before use"
    }

    fn slots(&self, l: &L) -> usize {
        match l {
            L::Seq { need, bind } => (need + bind) as usize,
            L::Var => 1,
        }
    }

    fn empty(&self, _node: &Node) -> L {
        L::Seq { need: 0, bind: 0 }
    }

    fn push(&self, node: &Node, _pos: usize, partial: &L, child: Option<&L>) -> Vec<(L, Link)> {
        let L::Seq { need, bind } = *partial else {
            return vec![];
        };
        match (node.def, child) {
            (_, None) => vec![(partial.clone(), Link((0..need + bind).map(Some).collect()))],
            // The statement's variable, still undecided.
            ("stmt", Some(L::Var)) => vec![(L::Var, Link(vec![Some(0)]))],
            (_, Some(L::Var)) => vec![],
            (_, Some(&L::Seq { need: cn, bind: cb })) => {
                // Each variable the child needs is one the sequence binds, one it already
                // needs, or a new need. Its bindings are new variables.
                let mut out = Vec::new();
                let mut choose = |picks: &[Pick]| {
                    let extra = picks.iter().filter(|p| matches!(p, Pick::New)).count() as u8;
                    let (n2, b2) = (need + extra, bind + cb);
                    if n2 + b2 > SLOTS {
                        return;
                    }
                    // Old needs, then new needs, then old binds, then the child's binds.
                    let mut link: Vec<Option<u8>> = (0..need).map(Some).collect();
                    link.extend((0..bind).map(|b| Some(n2 + b)));
                    let mut fresh = need;
                    for p in picks {
                        link.push(Some(match *p {
                            Pick::Need(i) => i,
                            Pick::Bound(i) => n2 + i,
                            Pick::New => {
                                fresh += 1;
                                fresh - 1
                            }
                        }));
                    }
                    link.extend((0..cb).map(|b| Some(n2 + bind + b)));
                    // Two of the child's needs are two variables.
                    let used: Vec<u8> = link[(need + bind) as usize..][..cn as usize]
                        .iter()
                        .flatten()
                        .copied()
                        .collect();
                    if used.iter().collect::<BTreeSet<_>>().len() == used.len() {
                        out.push((L::Seq { need: n2, bind: b2 }, Link(link)));
                    }
                };
                for picks in all_picks(cn, need, bind) {
                    choose(&picks);
                }
                out
            }
        }
    }

    fn finish(&self, node: &Node, partial: &L) -> Vec<(L, Link)> {
        match (node.def, partial) {
            ("var", _) => vec![(L::Var, Link(vec![]))],
            ("stmt", L::Var) => {
                let l = if node.items[0] == Item::Token("LET") {
                    L::Seq { need: 0, bind: 1 }
                } else {
                    L::Seq { need: 1, bind: 0 }
                };
                vec![(l, Link(vec![Some(0)]))]
            }
            ("stmt", _) => vec![],
            // The whole program: what it binds is never read.
            ("s", &L::Seq { need, bind }) if !node.group => {
                let mut link: Vec<Option<u8>> = (0..need).map(Some).collect();
                link.extend((0..bind).map(|_| None));
                vec![(L::Seq { need, bind: 0 }, Link(link))]
            }
            (_, l) => vec![(
                l.clone(),
                Link((0..self.slots(l) as u8).map(Some).collect()),
            )],
        }
    }

    fn top(&self, l: &L) -> bool {
        *l == L::Seq { need: 0, bind: 0 }
    }

    fn spells(&self, def: &str, _: &L) -> bool {
        def == "var"
    }

    fn show(&self, l: &L) -> String {
        match l {
            L::Seq { need: 0, bind: 0 } => String::new(),
            L::Seq { need, bind } => format!("need{need}bind{bind}"),
            L::Var => "var".into(),
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum Pick {
    Need(u8),
    Bound(u8),
    New,
}

fn all_picks(n: u8, need: u8, bind: u8) -> Vec<Vec<Pick>> {
    let mut out = vec![Vec::new()];
    for _ in 0..n {
        let mut next = Vec::new();
        for p in &out {
            let options = (0..need)
                .map(Pick::Need)
                .chain((0..bind).map(Pick::Bound))
                .chain([Pick::New]);
            for o in options {
                let mut q = p.clone();
                q.push(o);
                next.push(q);
            }
        }
        out = next;
    }
    out
}

fn toy() -> Cfg {
    Cfg::from_bnf(&bnf::parse(TOY).unwrap())
}

/// The toy rule read directly from a sentence, any names. A LET binds a new name, as GQL's
/// does (10.3 SR 7).
fn valid(sentence: &str) -> bool {
    let words: Vec<&str> = sentence.split_whitespace().collect();
    let mut bound = BTreeSet::new();
    for pair in words.chunks(2) {
        let [stmt, name] = pair else { return false };
        match *stmt {
            "LET" if !bound.insert(*name) => return false,
            "LET" => {}
            _ if bound.contains(name) => {}
            _ => return false,
        }
    }
    true
}

fn names(n: &[&str]) -> Vec<String> {
    n.iter().map(|s| s.to_string()).collect()
}

#[test]
fn generated_sentences_use_only_bound_names() {
    let cfg = toy();
    let built = build(
        &cfg,
        &LetBeforeUse,
        cfg.require("s").unwrap(),
        "x",
        &Options::default(),
    )
    .unwrap();
    let analysis = Analysis::new(&built.cfg, &StubProvider);
    let mut all = Vec::new();
    for seed in 0..8 {
        let config = Config {
            seed,
            max_depth: 14,
            length: Length::Unbounded,
        };
        let outcome = Generator::new(&analysis, config, StubProvider)
            .run(built.start)
            .unwrap();
        for t in outcome.trees {
            let mut root = t.root;
            built
                .name(&mut root, &names(&["x", "y", "z"]), |nt, s| {
                    analysis.spell(nt, s)
                })
                .unwrap();
            all.push(root.render(&built.cfg));
        }
    }
    assert!(!all.is_empty());
    for s in &all {
        assert!(valid(s), "{s:?}");
    }
    // Not vacuous: a use after its LET, and two variables at once.
    assert!(all.iter().any(|s| s.contains("USE")), "{all:?}");
    assert!(all.iter().any(|s| s.contains('y')), "{all:?}");
}

#[test]
fn the_grammar_does_not_grow_with_names() {
    // The product construction makes a copy of every nonterminal per name; here a variable
    // is a slot and names come last, so any pool gives one grammar.
    let cfg = toy();
    let built = build(
        &cfg,
        &LetBeforeUse,
        cfg.require("s").unwrap(),
        "x",
        &Options::default(),
    )
    .unwrap();
    let vars = built.cfg.nts.iter().filter(|n| n.base == "var").count();
    assert_eq!(vars, 1, "one `var`, whatever its name");
    assert!(
        built.cfg.prods.len() < 60,
        "{} productions",
        built.cfg.prods.len()
    );
}

#[test]
fn checking_a_given_tree_reads_its_names() {
    let cfg = toy();
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
                accepts(&LetBeforeUse, &tree).is_ok(),
                valid(&sentence),
                "{sentence:?}"
            );
            seen.insert(valid(&sentence));
        }
    }
    assert_eq!(seen.len(), 2, "both verdicts occur");
}

#[test]
fn no_context_on_iso_keeps_the_grammar() {
    let base = Cfg::from_bnf(&bnf::parse(gql_proof::ISO_BNF_XML).unwrap());
    let start = base.require("GQL-program").unwrap();
    let began = std::time::Instant::now();
    let built = build(&base, &Nothing, start, "a", &Options::default()).unwrap();
    eprintln!(
        "{} of {} productions, {} of {} nonterminals, {:?}",
        built.cfg.prods.len(),
        base.prods.len(),
        built.cfg.nts.len(),
        base.nts.len(),
        began.elapsed()
    );
    assert!(built.cfg.prods.len() <= base.prods.len());
}

#[test]
#[ignore]
fn show_definitions() {
    // GQL_SHOW="a,b": the desugared productions of each definition, for writing rules.
    let base = Cfg::from_bnf(&bnf::parse(gql_proof::ISO_BNF_XML).unwrap());
    let want = std::env::var("GQL_SHOW").unwrap_or_default();
    for name in want.split(',') {
        for (p, prod) in base.prods.iter().enumerate() {
            let owner = base.base(prod.lhs);
            if owner.split('/').next() == Some(name) {
                eprintln!("{}", gql_proof::describe(&base, p as u32));
            }
        }
    }
}

#[test]
#[ignore]
fn show_users() {
    // GQL_USES="a": the definitions whose productions use each one.
    let base = Cfg::from_bnf(&bnf::parse(gql_proof::ISO_BNF_XML).unwrap());
    let want = std::env::var("GQL_USES").unwrap_or_default();
    for name in want.split(',') {
        let mut users = std::collections::BTreeSet::new();
        for prod in &base.prods {
            if prod
                .rhs
                .iter()
                .any(|s| matches!(*s, gql_proof::cfg::Sym::Nt(c) if base.base(c) == name))
            {
                users.insert(base.base(prod.lhs).to_string());
            }
        }
        eprintln!("{name}: {users:?}");
    }
}

/// Every derivation tree of `nt` of height at most `height`.
fn every_tree(cfg: &Cfg, nt: u32, height: u32) -> Vec<gql_proof::tree::Node> {
    use gql_proof::cfg::{Lit, Sym};
    use gql_proof::tree::Node as T;
    if height == 0 {
        return Vec::new();
    }
    let mut out = Vec::new();
    for &p in &cfg.nts[nt as usize].prods {
        let mut partial: Vec<Vec<T>> = vec![Vec::new()];
        for &sym in &cfg.prods[p as usize].rhs {
            let options: Vec<T> = match sym {
                Sym::Nt(c) => every_tree(cfg, c, height - 1),
                Sym::Lit(l) => {
                    let text = match &cfg.lits[l as usize] {
                        Lit::Kw(t) | Lit::Term(t) => t.clone(),
                        Lit::Opaque(_) => unreachable!("the toy has no prose"),
                    };
                    vec![T {
                        sym,
                        prod: None,
                        text: Some(text),
                        children: Vec::new(),
                    }]
                }
            };
            partial = partial
                .into_iter()
                .flat_map(|kids| {
                    options.iter().map(move |o| {
                        let mut k = kids.clone();
                        k.push(o.clone());
                        k
                    })
                })
                .collect();
        }
        out.extend(partial.into_iter().map(|children| T {
            sym: Sym::Nt(nt),
            prod: Some(p),
            text: None,
            children,
        }));
    }
    out
}

/// The productions and the (occurrence, production) pairs a tree uses, by unrefined id.
fn uses(
    cfg: &Cfg,
    t: &gql_proof::tree::Node,
    prods: &mut BTreeSet<u32>,
    pairs: &mut BTreeSet<(u32, u32)>,
) {
    let Some(q) = t.prod else { return };
    prods.insert(cfg.prods[q as usize].unrefined);
    for (i, c) in t.children.iter().enumerate() {
        if let Some(p) = c.prod {
            pairs.insert((
                cfg.prods[q as usize].occ[i],
                cfg.prods[p as usize].unrefined,
            ));
        }
        uses(cfg, c, prods, pairs);
    }
}

#[test]
fn bounded_exhaustive_completeness() {
    // Every tree up to a height, judged by the rule: whatever production or cdrc pair an
    // accepted tree uses, the emitted grammar has (the totality claim, on the toy).
    let cfg = toy();
    let start = cfg.require("s").unwrap();
    let built = build(&cfg, &LetBeforeUse, start, "x", &Options::default()).unwrap();
    let (mut want_prods, mut want_pairs) = (BTreeSet::new(), BTreeSet::new());
    let mut valid = 0;
    let all = every_tree(&cfg, start, 9);
    for t in &all {
        if accepts(&LetBeforeUse, &t.export(&cfg)).is_ok() {
            valid += 1;
            uses(&cfg, t, &mut want_prods, &mut want_pairs);
        }
    }
    let mut have_prods = BTreeSet::new();
    let mut have_pairs = BTreeSet::new();
    let b = &built.cfg;
    for q in &b.prods {
        have_prods.insert(q.unrefined);
        for (i, sym) in q.rhs.iter().enumerate() {
            if let gql_proof::cfg::Sym::Nt(c) = sym {
                for &p in &b.nts[*c as usize].prods {
                    have_pairs.insert((q.occ[i], b.prods[p as usize].unrefined));
                }
            }
        }
    }
    eprintln!(
        "{} trees, {valid} valid; {} productions and {} pairs used, {} and {} emitted",
        all.len(),
        want_prods.len(),
        want_pairs.len(),
        have_prods.len(),
        have_pairs.len()
    );
    assert!(valid > 0);
    let missing: Vec<_> = want_prods.difference(&have_prods).collect();
    assert!(missing.is_empty(), "productions missing: {missing:?}");
    let missing: Vec<_> = want_pairs.difference(&have_pairs).collect();
    assert!(missing.is_empty(), "pairs missing: {missing:?}");
    // And nothing emitted that no valid tree uses: the emitted grammar is exact here.
    assert!(
        have_prods.is_subset(&want_prods),
        "{:?}",
        have_prods.difference(&want_prods).collect::<Vec<_>>()
    );
    assert!(
        have_pairs.is_subset(&want_pairs),
        "{:?}",
        have_pairs.difference(&want_pairs).collect::<Vec<_>>()
    );
}
