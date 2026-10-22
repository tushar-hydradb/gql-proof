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
use gql_proof::{ISO_BNF_XML, MatchModeDefault, bnf};
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
    let verifier = Verifier::new(Grammar::new(&ISO)).with_syntax_rules(MatchModeDefault::Portable);
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
        // Past the typed cap the definitions' classes are forgotten, not the sentence.
        "LET x = 1, y = 2, z = 3 RETURN x AS w",
        "LET x = 1, y = 'a' RETURN x + 1 AS w",
        // 13.5 SR 5: DELETE takes a node or an edge (`LET y = x DELETE y` is a documented
        // narrowing: a value variable defined by another variable is opaque).
        "MATCH (x) DELETE x",
        "MATCH (x)-[y]->() DETACH DELETE y",
        // 19.4 SR 5, 20.6 SR 8: a body that returns is a binding table.
        "RETURN EXISTS { RETURN 1 AS y } AS x",
        "RETURN EXISTS { MATCH (y) RETURN y } AS x",
        "RETURN EXISTS { FINISH NEXT RETURN 1 AS y } AS x",
        "RETURN VALUE { RETURN 1 AS y } AS x",
        "{ FINISH } NEXT RETURN 1 AS x",
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
        // 13.5 SR 5: not a value of another type, nor a path.
        "LET x = true DELETE x",
        "MATCH (x) DELETE CURRENT_DATE",
        "MATCH x = () DELETE x",
        // 19.4 SR 5, 20.6 SR 8: FINISH is the empty type, not a binding table.
        "RETURN EXISTS { FINISH } AS x",
        "RETURN EXISTS { { FINISH } } AS x",
        "RETURN EXISTS { RETURN 1 AS y NEXT FINISH } AS x",
        "RETURN EXISTS { MATCH (y) FINISH } AS x",
        "RETURN VALUE { FINISH } AS x",
        // 13.1 SR 3: a data-modifying body without a result statement finishes implicitly.
        "RETURN EXISTS { INSERT (y) } AS x",
        "RETURN EXISTS { CALL { FINISH } } AS x",
        // 12.1 SR 4: a catalog-modifying statement has the empty type.
        "RETURN EXISTS { CREATE SCHEMA /s } AS x",
        // 20.6 SR 3: one column.
        "RETURN VALUE { RETURN NO BINDINGS } AS x",
        "RETURN VALUE { RETURN 1 AS y, 2 AS z } AS x",
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
    let slots = env_num("GQL_SLOTS", 1);
    let rule = Typed::new(
        Scope {
            caps: Caps {
                slots,
                references: slots,
            },
        },
        Types::new(&BASE),
    );
    let options = Options {
        progress: false,
        join: std::env::var("GQL_JOIN").is_ok(),
        ..Options::default()
    };
    let analyzed = gql_proof::context::analyze(&BASE, &rule, &options).unwrap();
    let mut widest: Vec<(usize, u32)> = (0..BASE.nts.len() as u32)
        .map(|nt| (analyzed.labels(nt).count(), nt))
        .collect();
    widest.sort_unstable_by(|a, b| b.cmp(a));
    // Over every nonterminal: labels against distinct scope parts, distinct view shapes of
    // those (what types reads of scope), and distinct type parts.
    let (mut all, mut all_scope, mut all_views, mut all_types) = (0, 0, 0, 0);
    let shape = |a: &gql_proof::context::scope::Label| -> String {
        (0..a.width())
            .map(|s| format!("{:?}", a.view(s)))
            .collect::<Vec<_>>()
            .join("|")
    };
    for &(n, nt) in &widest {
        let mut scope = BTreeSet::new();
        let mut views = BTreeSet::new();
        let mut types = BTreeSet::new();
        for (a, b) in analyzed.labels(nt) {
            scope.insert(a);
            views.insert(shape(a));
            types.insert(b);
        }
        all += n;
        all_scope += scope.len();
        all_views += views.len();
        all_types += types.len();
    }
    eprintln!(
        "all nonterminals: {all} labels, {all_scope} scope parts, {all_views} view shapes, {all_types} type parts"
    );
    for &(n, nt) in widest.iter().take(12) {
        let mut scope = BTreeSet::new();
        let mut views: BTreeMap<String, BTreeSet<&gql_proof::context::scope::Label>> =
            BTreeMap::new();
        let mut per_scope: BTreeMap<&gql_proof::context::scope::Label, usize> = BTreeMap::new();
        let mut types = BTreeSet::new();
        let mut classes: BTreeMap<String, usize> = BTreeMap::new();
        let mut entries: BTreeMap<String, usize> = BTreeMap::new();
        for (a, b) in analyzed.labels(nt) {
            scope.insert(a);
            views.entry(shape(a)).or_default().insert(a);
            *per_scope.entry(a).or_default() += 1;
            types.insert(b);
            *classes.entry(format!("{:?}", b.class())).or_default() += 1;
            *entries.entry(format!("{:?}", b.vars())).or_default() += 1;
        }
        let max_per_scope = per_scope.values().copied().max().unwrap_or(0);
        let max_per_view = views.values().map(BTreeSet::len).max().unwrap_or(0);
        eprintln!(
            "{n:>6} <{}>: {} scope labels ({} view shapes, up to {} scope labels per shape), {} type parts (up to {} per scope label), {} classes, {} entry lists",
            BASE.nts[nt as usize].name,
            scope.len(),
            views.len(),
            max_per_view,
            types.len(),
            max_per_scope,
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

/// How much of a production scan a sideways filter could skip, at one variable. One full scan
/// per production with two or more child nonterminals, over the fixed point's labels: pairs
/// tried (partial label, child label), pairs the push keeps, and pairs that lead to some
/// finished label (what a perfect filter would keep). For the comparison, also the pairs a
/// comparability-family key keeps, and whether it ever drops a useful one. `cargo test
/// --release --test context_types pair_waste -- --ignored --nocapture`.
#[test]
#[ignore]
fn pair_waste() {
    use gql_proof::cfg::Sym;
    use gql_proof::context::Context;
    use gql_proof::context::scope::Caps;
    use gql_proof::context::types::{Class, Ty};
    use gql_proof::refine::{Node, items_of};
    use std::collections::BTreeMap;
    type L = <Typed<Scope, Types> as Context>::Label;
    let slots = env_num("GQL_SLOTS", 1);
    // Only productions whose description holds this text, if given.
    let only = std::env::var("GQL_PRODS").ok();
    let rule = Typed::new(
        Scope {
            caps: Caps {
                slots,
                references: slots,
            },
        },
        Types::new(&BASE),
    );
    let options = Options {
        progress: false,
        join: std::env::var("GQL_JOIN").is_ok(),
        ..Options::default()
    };
    let analyzed = gql_proof::context::analyze(&BASE, &rule, &options).unwrap();
    let labels: Vec<Vec<L>> = (0..BASE.nts.len() as u32)
        .map(|nt| analyzed.labels(nt).cloned().collect())
        .collect();
    // Comparability family of a class; `None` for a wildcard (null, dynamic, deferred).
    let family = |t: Option<Ty>| -> Option<u8> {
        match t? {
            Ty::Slot(..) => None,
            Ty::Is(c) => match c {
                Class::Null | Class::Dynamic => None,
                Class::Exact | Class::Approx => Some(0),
                Class::List | Class::Record | Class::Path => Some(1),
                c => Some(10 + c as u8),
            },
        }
    };
    struct Row {
        name: String,
        tried: u64,
        kept: u64,
        useful: u64,
    }
    let mut rows = Vec::new();
    let (mut keyed, mut keyed_dropped_useful) = (0u64, 0u64);
    for (p, prod) in BASE.prods.iter().enumerate() {
        let children = prod.rhs.iter().filter(|s| matches!(s, Sym::Nt(_))).count();
        if children < 2 {
            continue;
        }
        if let Some(only) = &only
            && !gql_proof::describe(&BASE, p as u32).contains(only.as_str())
        {
            continue;
        }
        let items = items_of(&BASE, prod);
        let lhs = &BASE.nts[prod.lhs as usize];
        let node = Node {
            def: &lhs.base,
            group: lhs.synthetic,
            items: &items,
            text: None,
        };
        let comparison = lhs.base == "comparison predicate";
        // Layers of partial labels, and per position each push: (partial, child, outputs).
        let mut layer: Vec<L> = vec![rule.empty(&node)];
        let mut pushes: Vec<Vec<(usize, usize, Vec<usize>)>> = Vec::new();
        let mut layers: Vec<Vec<L>> = Vec::new();
        for (pos, sym) in prod.rhs.iter().enumerate() {
            let mut next: BTreeMap<L, usize> = BTreeMap::new();
            let mut here = Vec::new();
            for (i, partial) in layer.iter().enumerate() {
                let opts: Vec<Option<&L>> = match sym {
                    Sym::Nt(c) => labels[*c as usize].iter().map(Some).collect(),
                    Sym::Lit(_) => vec![None],
                };
                for (ci, opt) in opts.into_iter().enumerate() {
                    let outs: Vec<usize> = rule
                        .push(&node, pos, partial, opt)
                        .into_iter()
                        .map(|(q, _)| {
                            let n = next.len();
                            *next.entry(q).or_insert(n)
                        })
                        .collect();
                    here.push((i, ci, outs));
                }
            }
            let mut ordered: Vec<(L, usize)> = next.into_iter().collect();
            ordered.sort_by_key(|(_, i)| *i);
            layers.push(std::mem::take(&mut layer));
            layer = ordered.into_iter().map(|(l, _)| l).collect();
            pushes.push(here);
        }
        // Live partials, backward from the ones that finish.
        let mut live: Vec<bool> = layer
            .iter()
            .map(|l| !rule.finish(&node, l).is_empty())
            .collect();
        let (mut tried, mut kept, mut useful) = (0u64, 0u64, 0u64);
        for pos in (0..prod.rhs.len()).rev() {
            let nt_pos = matches!(prod.rhs[pos], Sym::Nt(_));
            let mut before = vec![false; layers[pos].len()];
            for (i, ci, outs) in &pushes[pos] {
                let good = outs.iter().any(|&j| live[j]);
                if good {
                    before[*i] = true;
                }
                if nt_pos && pos > 0 {
                    tried += 1;
                    kept += !outs.is_empty() as u64;
                    useful += good as u64;
                    if comparison {
                        let left = layers[pos][*i].1.kids().first().copied().flatten();
                        let Sym::Nt(c) = prod.rhs[pos] else {
                            unreachable!()
                        };
                        let right = labels[c as usize][*ci].1.class();
                        let pass = match (family(left), family(right)) {
                            (Some(a), Some(b)) => a == b,
                            _ => true,
                        };
                        keyed += pass as u64;
                        keyed_dropped_useful += (!pass && good) as u64;
                    }
                }
            }
            live = before;
        }
        if tried > 0 {
            let name = format!(
                "<{}> ::= {}",
                lhs.name,
                prod.rhs
                    .iter()
                    .map(|s| match s {
                        Sym::Nt(n) => format!("<{}>", BASE.nts[*n as usize].name),
                        Sym::Lit(_) => "tok".into(),
                    })
                    .collect::<Vec<_>>()
                    .join(" ")
            );
            rows.push(Row {
                name,
                tried,
                kept,
                useful,
            });
            let _ = p;
        }
    }
    rows.sort_by(|a, b| b.tried.cmp(&a.tried));
    let total: u64 = rows.iter().map(|r| r.tried).sum();
    let kept: u64 = rows.iter().map(|r| r.kept).sum();
    let useful: u64 = rows.iter().map(|r| r.useful).sum();
    eprintln!(
        "all productions: {total} pairs tried, {kept} kept by the push ({:.1}%), {useful} useful ({:.2}%)",
        100.0 * kept as f64 / total as f64,
        100.0 * useful as f64 / total as f64
    );
    eprintln!("     tried       kept     useful  useful%  production");
    for r in rows.iter().take(25) {
        eprintln!(
            "{:>10} {:>10} {:>10} {:>7.2}%  {}",
            r.tried,
            r.kept,
            r.useful,
            100.0 * r.useful as f64 / r.tried.max(1) as f64,
            r.name
        );
    }
    eprintln!(
        "comparison with a family key: {keyed} pairs tried, {keyed_dropped_useful} useful pairs dropped"
    );
}

/// An estimate of entries as principal typings, without building them: at one variable,
/// labels that differ only in what they ask of the variable are merged after the fact (a
/// typing would hold them as one), and every production is scanned once more counting the
/// distinct merged pairs (partial, child) it would try. `cargo test --release --test
/// context_types typing_estimate -- --ignored --nocapture`.
#[test]
#[ignore]
fn typing_estimate() {
    use gql_proof::cfg::Sym;
    use gql_proof::context::Context;
    use gql_proof::context::scope::Caps;
    use gql_proof::refine::{Node, items_of};
    use std::collections::{BTreeMap, HashMap, HashSet};
    type L = <Typed<Scope, Types> as Context>::Label;
    let merged = |l: &L| (l.0.clone(), l.1.without_needs());
    let slots: usize = std::env::var("GQL_SLOTS").map_or(1, |s| s.parse().unwrap());
    let rule = Typed::new(
        Scope {
            caps: Caps {
                slots,
                references: slots,
            },
        },
        Types::new(&BASE),
    );
    let options = Options {
        progress: false,
        ..Options::default()
    };
    let analyzed = gql_proof::context::analyze(&BASE, &rule, &options).unwrap();
    let labels: Vec<Vec<L>> = (0..BASE.nts.len() as u32)
        .map(|nt| analyzed.labels(nt).cloned().collect())
        .collect();
    // Labels per nonterminal, before and after the merge, and each label's merged id.
    let mut ids: Vec<Vec<u32>> = Vec::new();
    let (mut before, mut after, mut safe) = (0usize, 0usize, 0usize);
    let mut widest: Vec<(usize, usize, usize, String)> = Vec::new();
    for (nt, ls) in labels.iter().enumerate() {
        let mut seen: HashMap<_, u32> = HashMap::new();
        let mut rows: Vec<Vec<Vec<gql_proof::context::types::Entry>>> = Vec::new();
        let id: Vec<u32> = ls
            .iter()
            .map(|l| {
                let n = seen.len() as u32;
                let i = *seen.entry(merged(l)).or_insert(n);
                if i as usize == rows.len() {
                    rows.push(Vec::new());
                }
                rows[i as usize].push(l.1.vars().to_vec());
                i
            })
            .collect();
        // A merged group one typing holds exactly: per-slot sets (a rectangle), or one set
        // shared by every slot (an equality group). Any other keeps all its labels.
        let exact: usize = rows
            .iter()
            .map(|group| {
                let width = group[0].len();
                let columns: Vec<HashSet<_>> = (0..width)
                    .map(|s| group.iter().map(|r| r[s]).collect())
                    .collect();
                let rectangle = columns.iter().map(HashSet::len).product::<usize>()
                    == group.iter().collect::<HashSet<_>>().len();
                let diagonal = group.iter().all(|r| r.iter().all(|e| *e == r[0]));
                if rectangle || diagonal {
                    1
                } else {
                    group.len()
                }
            })
            .sum();
        before += ls.len();
        after += seen.len();
        safe += exact;
        widest.push((ls.len(), seen.len(), exact, BASE.nts[nt].name.clone()));
        ids.push(id);
    }
    widest.sort_unstable_by(|a, b| b.cmp(a));
    eprintln!(
        "{slots} variable(s), labels: {before} -> {after} with every need forgotten, {safe} \
         counting only groups one typing holds exactly"
    );
    for (b, a, s, name) in widest.iter().take(10) {
        eprintln!("  {b:>7} -> {a:>6} / {s:>6}  <{name}>");
    }
    // Pairs a scan tries, and distinct merged pairs.
    let mut rows: Vec<(u64, u64, String)> = Vec::new();
    for prod in &BASE.prods {
        if prod.rhs.iter().filter(|s| matches!(s, Sym::Nt(_))).count() < 2 {
            continue;
        }
        let items = items_of(&BASE, prod);
        let lhs = &BASE.nts[prod.lhs as usize];
        let node = Node {
            def: &lhs.base,
            group: lhs.synthetic,
            items: &items,
            text: None,
        };
        let mut layer: Vec<L> = vec![rule.empty(&node)];
        let (mut tried, mut distinct) = (0u64, 0u64);
        for (pos, sym) in prod.rhs.iter().enumerate() {
            let mut next: BTreeMap<L, ()> = BTreeMap::new();
            let mut pids: HashMap<_, u32> = HashMap::new();
            let mut pairs: HashSet<(u32, u32)> = HashSet::new();
            for partial in &layer {
                let n = pids.len() as u32;
                let p = *pids.entry(merged(partial)).or_insert(n);
                match sym {
                    Sym::Nt(c) => {
                        for (ci, child) in labels[*c as usize].iter().enumerate() {
                            if pos > 0 {
                                tried += 1;
                                pairs.insert((p, ids[*c as usize][ci]));
                            }
                            for (q, _) in rule.push(&node, pos, partial, Some(child)) {
                                next.insert(q, ());
                            }
                        }
                    }
                    Sym::Lit(_) => {
                        for (q, _) in rule.push(&node, pos, partial, None) {
                            next.insert(q, ());
                        }
                    }
                }
            }
            distinct += pairs.len() as u64;
            layer = next.into_keys().collect();
        }
        if tried > 0 {
            rows.push((tried, distinct, format!("<{}>", lhs.name)));
        }
    }
    rows.sort_unstable_by(|a, b| b.cmp(a));
    let t: u64 = rows.iter().map(|r| r.0).sum();
    let d: u64 = rows.iter().map(|r| r.1).sum();
    eprintln!(
        "pairs tried: {t} -> {d} merged ({:.1}x fewer)",
        t as f64 / d as f64
    );
    for (t, d, name) in rows.iter().take(12) {
        eprintln!(
            "  {t:>9} -> {d:>8}  {:>5.1}x  {name}",
            *t as f64 / *d as f64
        );
    }
}

/// What an emitted grammar can derive, by base id: productions, cdrc pairs (occurrence,
/// production) and two-step chains.
fn uses(cfg: &Cfg) -> [BTreeSet<(u32, u32, u32, u32)>; 3] {
    use gql_proof::cfg::Sym;
    let mut out: [BTreeSet<(u32, u32, u32, u32)>; 3] = Default::default();
    for q in &cfg.prods {
        out[0].insert((q.unrefined, 0, 0, 0));
        for (i, sym) in q.rhs.iter().enumerate() {
            let Sym::Nt(c) = sym else { continue };
            for &p in &cfg.nts[*c as usize].prods {
                let pp = &cfg.prods[p as usize];
                out[1].insert((q.occ[i], pp.unrefined, 0, 0));
                for (j, s2) in pp.rhs.iter().enumerate() {
                    let Sym::Nt(g) = s2 else { continue };
                    for &r in &cfg.nts[*g as usize].prods {
                        out[2].insert((
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
    out
}

/// Joins change how the fixed point counts, not what the emitted grammar can derive: the same
/// productions, cdrc pairs and two-step chains at one variable, with and without.
/// `cargo test --release --test context_types joins_keep_coverage -- --ignored --nocapture`.
#[test]
#[ignore]
fn joins_keep_coverage() {
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
    let run = |join: bool, keys: bool| {
        let options = Options {
            progress: false,
            join,
            keys,
            ..Options::default()
        };
        let built = build(&BASE, &rule, start, "x", &options).unwrap();
        eprintln!(
            "join {join}, keys {keys}: {} labels, {} nonterminals, {} productions",
            built.stats.total_labels(),
            built.cfg.nts.len(),
            built.cfg.prods.len()
        );
        uses(&built.cfg)
    };
    let plain = run(false, false);
    for (join, keys) in [(true, false), (true, true)] {
        let other = run(join, keys);
        for &(p, ..) in plain[0].difference(&other[0]) {
            eprintln!("  only without: {}", gql_proof::describe(&BASE, p));
        }
        for (what, (a, b)) in ["productions", "cdrc pairs", "two-step chains"]
            .iter()
            .zip(plain.iter().zip(&other))
        {
            eprintln!(
                "  {what}: {} without, {} with; {} only without, {} only with",
                a.len(),
                b.len(),
                a.difference(b).count(),
                b.difference(a).count()
            );
        }
        assert_eq!(plain[0], other[0]);
        assert_eq!(plain[1], other[1]);
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

/// A number from the environment, for the measuring tests.
fn env_num(name: &str, default: usize) -> usize {
    std::env::var(name)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(default)
}

/// Each pruning of the types rule gives every nonterminal exactly the labels the rule gives
/// without it: `fold` (an expression node evaluated at its last push) and `keys` (child
/// labels paired by key). `GQL_OFF` names the prunings the plain run turns off (`fold`,
/// `keys`, or `fold,keys`); `GQL_SLOTS` sets the cap; joins off, so the sets are canonical.
#[test]
#[ignore]
fn pruning_is_exact() {
    use gql_proof::context::scope::Caps;
    let slots = env_num("GQL_SLOTS", 1);
    let off = std::env::var("GQL_OFF").unwrap_or_else(|_| "fold".into());
    let run = |pruned: bool| {
        let mut types = Types::new(&BASE);
        if !pruned {
            types.fold = !off.contains("fold");
        }
        let rule = Typed::new(
            Scope {
                caps: Caps {
                    slots,
                    references: slots,
                },
            },
            types,
        );
        let options = Options {
            progress: false,
            keys: pruned || !off.contains("keys"),
            ..Options::default()
        };
        let began = std::time::Instant::now();
        let analyzed = gql_proof::context::analyze(&BASE, &rule, &options).unwrap();
        let sets: Vec<BTreeSet<String>> = (0..BASE.nts.len() as u32)
            .map(|nt| analyzed.labels(nt).map(|l| format!("{l:?}")).collect())
            .collect();
        eprintln!(
            "pruned {pruned}: {} labels, {:?}",
            sets.iter().map(BTreeSet::len).sum::<usize>(),
            began.elapsed()
        );
        sets
    };
    let (plain, folded) = (run(false), run(true));
    let mut differ = 0;
    for (nt, (a, b)) in plain.iter().zip(&folded).enumerate() {
        if a != b {
            differ += 1;
            if differ <= 8 {
                let only_a: Vec<&String> = a.difference(b).take(3).collect();
                let only_b: Vec<&String> = b.difference(a).take(3).collect();
                eprintln!(
                    "<{}>: {} vs {} labels\n  only plain: {only_a:?}\n  only pruned: {only_b:?}",
                    BASE.nts[nt].name,
                    a.len(),
                    b.len()
                );
            }
        }
    }
    assert_eq!(differ, 0, "{differ} nonterminals differ");
}

/// With joins, a label a join replaced keeps its made labels: kept layers still hold it as
/// the option it was when scanned, and grounding reads its parts (`Engine::add`).
#[test]
fn subsumed_options_keep_their_parts() {
    use gql_proof::context::scope::Caps;
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
        join: true,
        keys: true,
        ..Options::default()
    };
    let analyzed = gql_proof::context::analyze(&BASE, &rule, &options).unwrap();
    let (subsumed, orphaned) = analyzed.orphaned_options();
    eprintln!("{subsumed} subsumed options in kept layers, {orphaned} without parts");
    assert!(subsumed > 0, "the census found nothing to check");
    assert_eq!(orphaned, 0);
}

/// Per-target extraction against the emitted grammar, typed, without joins, at a cap
/// (`GQL_SLOTS`, 1 by default): see `common::extraction_matches_emission`.
#[test]
#[ignore]
fn extraction_matches_emission() {
    use gql_proof::context::scope::Caps;
    let slots: usize = std::env::var("GQL_SLOTS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(1);
    let rule = Typed::new(
        Scope {
            caps: Caps {
                slots,
                references: slots,
            },
        },
        Types::new(&BASE),
    );
    let options = Options {
        progress: false,
        keys: true,
        ..Options::default()
    };
    // `GQL_JOIN`: the extraction reads the joined fixed point; the oracle stays unjoined.
    let extract = Options {
        join: std::env::var("GQL_JOIN").is_ok(),
        ..options.clone()
    };
    common::extraction_matches_emission(&BASE, &rule, &options, &extract, true);
}

mod common;

/// With joins, every ground of every made label is a ground of some label of the exact
/// (unjoined) fixed point: a joined label never stands for a tree that does not exist. One
/// variable; prints the phantoms per nonterminal, worst first. `GQL_NT` narrows the print to
/// one nonterminal and lists its phantoms with the made labels they come from.
#[test]
#[ignore]
fn joined_grounds_are_exact() {
    use gql_proof::context::Context;
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
    let run = |join: bool| {
        gql_proof::context::analyze(
            &BASE,
            &rule,
            &Options {
                progress: false,
                join,
                keys: true,
                ..Options::default()
            },
        )
        .unwrap()
    };
    let (exact, joined) = (run(false), run(true));
    let only = std::env::var("GQL_NT").ok();
    let mut rows: Vec<(usize, usize, String)> = Vec::new();
    let mut total = 0;
    for nt in 0..BASE.nts.len() as u32 {
        let truth: BTreeSet<<Typed<Scope, Types> as Context>::Label> =
            exact.labels(nt).flat_map(|l| rule.grounds(l)).collect();
        let mut phantoms: BTreeMap<_, Vec<String>> = BTreeMap::new();
        for m in joined.made(nt) {
            for g in rule.grounds(m) {
                if !truth.contains(&g) {
                    phantoms.entry(g).or_default().push(rule.show(m));
                }
            }
        }
        if phantoms.is_empty() {
            continue;
        }
        total += phantoms.len();
        rows.push((
            phantoms.len(),
            truth.len(),
            BASE.nts[nt as usize].name.clone(),
        ));
        if only.as_deref() == Some(BASE.nts[nt as usize].name.as_str()) {
            for (g, from) in phantoms.iter().take(12) {
                eprintln!("  phantom [{}] from {:?}", rule.show(g), from);
            }
        }
    }
    rows.sort_unstable_by(|a, b| b.cmp(a));
    eprintln!("{total} phantom grounds over {} nonterminals", rows.len());
    for (n, truth, name) in rows.iter().take(20) {
        eprintln!("  {n:>6} phantoms, {truth:>6} true grounds  <{name}>");
    }
    assert_eq!(total, 0);
}
