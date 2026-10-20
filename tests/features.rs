//! The conformance rules compiled into the grammar (`features::ClaimRules`) against their
//! direct reading (`verify`), claims against 24.2, 24.3 and table 10, and generation under a
//! claim. Needs `grammar/conformance.json` (`just features`).

use gql_proof::bnf;
use gql_proof::cfg::Cfg;
use gql_proof::coverage::Criteria;
use gql_proof::features::{
    CONFORMANCE_JSON, Claim, ClaimRules, Conformance, Negative, Pattern, negative, witness,
};
use gql_proof::leaf::StubProvider;
use gql_proof::purdom::{Analysis, Config, Generator, Length};
use gql_proof::refine::{Rule, accepts, all_rules, refine};
use gql_proof::tokens::Grammar;
use gql_proof::verify::{Plain, Verifier};
use gql_proof::{ISO_BNF_XML, MatchModeDefault};
use std::collections::BTreeSet;
use std::sync::LazyLock;

static ISO: LazyLock<bnf::Bnf> = LazyLock::new(|| bnf::parse(ISO_BNF_XML).unwrap());
static BASE: LazyLock<Cfg> = LazyLock::new(|| Cfg::from_bnf(&ISO));
static CONF: LazyLock<Conformance> = LazyLock::new(|| Conformance::load(CONFORMANCE_JSON).unwrap());

fn claim(codes: &[&str]) -> Result<Claim, String> {
    Claim::closed(codes.iter().map(|c| c.to_string()).collect(), &CONF).map_err(|e| e.to_string())
}

#[test]
fn claims_close_under_table_10() {
    // G061 (unbounded quantifiers) implies G060 (bounded ones), GQ07 (INTERSECT ALL) GQ06.
    let c = claim(&["GG01", "G061", "GQ07"]).unwrap();
    for f in ["G060", "GQ06"] {
        assert!(c.features.contains(f), "{f} missing from {:?}", c.features);
    }
}

#[test]
fn claims_follow_24_2_and_24_3() {
    // 24.2, as cor 1 has it: automatic graph population or graph management.
    assert!(claim(&[]).unwrap_err().contains("24.2"));
    // 24.3: exact numbers need an exact numeric type, inline procedures a variable scope kind.
    assert!(claim(&["GC00", "GL04"]).unwrap_err().contains("24.3"));
    assert!(claim(&["GC00", "GP01"]).unwrap_err().contains("24.3"));
    claim(&["GC00", "GL04", "GV07", "GP01", "GP02"]).unwrap();
    assert_eq!(
        Claim::parse("none", &CONF).unwrap().features,
        BTreeSet::from(["GC00".to_string()])
    );
    // cor 1's "at least one of" rows in table 10: explicit WALK needs a path prefix, graph
    // management a graph type. GG01 implies GC04, which then holds.
    assert!(claim(&["GC00", "G010"]).unwrap_err().contains("table 10"));
    claim(&["GC00", "G010", "G005"]).unwrap();
    assert!(claim(&["GC04"]).unwrap_err().contains("table 10"));
    assert!(claim(&["GG01"]).unwrap().features.contains("GC04"));
}

fn trees(cfg: &Cfg, start: u32, seed: u64, criteria: Criteria) -> Vec<Plain> {
    let analysis = Analysis::new(cfg, &StubProvider);
    let config = Config {
        seed,
        max_depth: analysis.reference_height(start),
        length: Length::Reference,
    };
    Generator::new(&analysis, config, StubProvider)
        .run_with(start, &BASE, criteria)
        .unwrap()
        .trees
        .iter()
        .map(|t| t.root.export(cfg))
        .collect()
}

/// Unrefined trees covering every production in every context: they break many rules.
static UNREFINED: LazyLock<Vec<Plain>> = LazyLock::new(|| {
    let criteria = Criteria {
        cdrc: true,
        k: 2,
        lexical: false,
    };
    trees(&BASE, BASE.require("GQL-program").unwrap(), 1, criteria)
});

#[test]
fn automaton_and_verifier_agree_per_statement() {
    // Each rule judged by both implementations on its own.
    let start = BASE.require("GQL-program").unwrap();
    let trees = &*UNREFINED;
    let forbidden = CONF.forbidden(&Claim::parse("none", &CONF).unwrap());
    let verifier = Verifier::new(Grammar::new(&ISO)).with_conformance(forbidden.clone());
    let broken: Vec<Vec<usize>> = trees
        .iter()
        .map(|t| {
            verifier
                .broken_conformance(t)
                .into_iter()
                .map(|f| {
                    forbidden
                        .iter()
                        .position(|g| g.label == f.label && g.patterns == f.patterns)
                        .unwrap()
                })
                .collect()
        })
        .collect();
    let mut mismatches = Vec::new();
    let mut caught = 0;
    let mut unbroken = Vec::new();
    for (i, f) in forbidden.iter().enumerate() {
        let rule: Vec<Box<dyn Rule>> = vec![Box::new(
            ClaimRules::new(&BASE, start, std::slice::from_ref(f), &[]).unwrap(),
        )];
        let mut any = false;
        for (t, tree) in trees.iter().enumerate() {
            let automaton = accepts(&rule, tree).is_err();
            let direct = broken[t].contains(&i);
            any |= direct;
            if automaton != direct {
                mismatches.push(format!(
                    "{}: automaton {automaton}, verifier {direct}: {}",
                    f.label,
                    verifier.render(tree)
                ));
            }
        }
        caught += usize::from(any);
        if !any {
            unbroken.push(f.label.clone());
        }
    }
    eprintln!(
        "{} trees, {caught} of {} rules broken by some tree; not: {unbroken:?}",
        trees.len(),
        forbidden.len()
    );
    // The order rules and the rules read through single-item rules are among those tested.
    for cite in ["G047 16.7 CR 15)", "GQ14 14.10 CR 1)", "GF10 20.9 CR 1)"] {
        assert!(
            !unbroken.contains(&cite.to_string()),
            "{cite} broken by no tree"
        );
    }
    assert!(
        mismatches.is_empty(),
        "{} mismatches:\n{}",
        mismatches.len(),
        mismatches[..mismatches.len().min(20)].join("\n")
    );
    assert!(caught > forbidden.len() / 2);
}

#[test]
fn automaton_and_verifier_agree_on_a_whole_claim() {
    // Every rule of the smallest claim at once, where rules that forbid a whole definition
    // rewrite the others.
    let start = BASE.require("GQL-program").unwrap();
    let forbidden = CONF.forbidden(&Claim::parse("none", &CONF).unwrap());
    let rule: Vec<Box<dyn Rule>> = vec![Box::new(
        ClaimRules::new(&BASE, start, &forbidden, &[]).unwrap(),
    )];
    let verifier = Verifier::new(Grammar::new(&ISO)).with_conformance(forbidden);
    for tree in UNREFINED.iter() {
        let automaton = accepts(&rule, tree).is_err();
        let direct = !verifier.broken_conformance(tree).is_empty();
        assert_eq!(automaton, direct, "{}", verifier.render(tree));
    }
}

#[test]
fn negatives_break_only_their_own_feature() {
    let start = BASE.require("GQL-program").unwrap();
    let none = Claim::parse("none", &CONF).unwrap();
    let verifier = Verifier::new(Grammar::new(&ISO))
        .with_syntax_rules(MatchModeDefault::Portable)
        .with_conformance(CONF.forbidden(&none));
    // Not G061: an unbounded quantifier needs a guard (16.4 SR 14), and every guard is an
    // optional feature of its own.
    // GS09, GS18 and GQ27 are cor 1's.
    for code in [
        "G002", "GQ09", "GQ04", "GS05", "GL01", "GQ12", "GE07", "GS09", "GS18", "GQ27",
    ] {
        let s = CONF
            .statements
            .iter()
            .find(|s| s.feature == code && s.kind == "pattern")
            .unwrap();
        let found = negative(
            &BASE,
            start,
            MatchModeDefault::Portable,
            0,
            &CONF,
            &none,
            &verifier,
            s,
            &s.forbid[0],
        )
        .unwrap();
        let Negative::Query(tree, sentence) = found else {
            panic!("no negative for {code}");
        };
        let own: BTreeSet<String> = CONF
            .statements
            .iter()
            .filter(|t| t.feature == code)
            .map(|t| t.cite())
            .collect();
        let violations = verifier.verify(&tree, &sentence);
        assert!(
            violations.iter().any(|v| v.detail == s.cite()),
            "{code}: {sentence}"
        );
        for v in &violations {
            assert!(
                v.rule == "conformance rule" && own.contains(&v.detail),
                "{code}: {v} in {sentence}"
            );
        }
    }
}

#[test]
fn every_claim_keeps_the_devices_out() {
    // Under `all` only the rules every claim is under remain, and generated trees satisfy
    // them as read directly.
    let start = BASE.require("GQL-program").unwrap();
    let forbidden = CONF.forbidden(&Claim::parse("all", &CONF).unwrap());
    assert_eq!(forbidden.len(), CONF.devices.len());
    let mut rules = all_rules(MatchModeDefault::Portable);
    rules.push(Box::new(
        ClaimRules::new(&BASE, start, &forbidden, &[]).unwrap(),
    ));
    let refined = refine(&BASE, &rules, start).unwrap();
    let verifier = Verifier::new(Grammar::new(&ISO))
        .with_syntax_rules(MatchModeDefault::Portable)
        .with_conformance(forbidden);
    let criteria = Criteria {
        cdrc: true,
        k: 0,
        lexical: false,
    };
    for tree in trees(&refined.cfg, refined.start, 3, criteria) {
        let violations = verifier.verify(&tree, &verifier.render(&tree));
        assert!(violations.is_empty(), "{violations:?}");
    }
}

#[test]
fn rules_no_unrefined_tree_breaks_have_witnesses() {
    // Two node patterns side by side (g046) and an aggregate in a sort key (gf20) are in none
    // of the unrefined trees: build the shortest tree breaking each, and have both
    // implementations agree it does.
    let start = BASE.require("GQL-program").unwrap();
    let forbidden = CONF.forbidden(&Claim::parse("none", &CONF).unwrap());
    for cite in ["G046 16.7 CR 14)", "GF20 14.10 CR 3)"] {
        let f = forbidden.iter().find(|f| f.label == cite).unwrap();
        let (tree, sentence) = witness(
            &BASE,
            start,
            MatchModeDefault::Portable,
            0,
            &[],
            &f.patterns[0],
        )
        .unwrap()
        .unwrap_or_else(|| panic!("{cite}: no tree breaks it"));
        let verifier = Verifier::new(Grammar::new(&ISO)).with_conformance(vec![f.clone()]);
        assert_eq!(
            verifier.broken_conformance(&tree).len(),
            1,
            "{cite}: {sentence}"
        );
        let rule: Vec<Box<dyn Rule>> = vec![Box::new(
            ClaimRules::new(&BASE, start, std::slice::from_ref(f), &[]).unwrap(),
        )];
        assert!(accepts(&rule, &tree).is_err(), "{cite}: {sentence}");
        eprintln!("{cite}: {sentence}");
    }
}

#[test]
fn the_grammar_is_cor_1s() {
    // Cor 1 17.1: a relative directory path ends in a solidus, so `..` alone is gone. 18.9: a
    // component type list has at least two components.
    let start = BASE.require("GQL-program").unwrap();
    for (nt, needs) in [
        ("relative directory path", ".. /"),
        ("component type list", "|"),
    ] {
        let pattern = Pattern {
            nt: Some(nt.to_string()),
            words: None,
            conds: Vec::new(),
        };
        let (_, sentence) = witness(&BASE, start, MatchModeDefault::Portable, 0, &[], &pattern)
            .unwrap()
            .unwrap();
        assert!(sentence.contains(needs), "<{nt}>: {sentence}");
    }
    // 21.3: TYPE is reserved, |+| a delimiter token.
    let grammar = Grammar::new(&ISO);
    assert!(grammar.reserved_words().contains("TYPE"));
    assert!(CONF.notes.iter().any(|n| n.contains("TYPE")));
}

#[test]
fn cor_1_leaves_the_compiled_syntax_rules_alone() {
    // 16.4 SR 6 and 14, and 13.1 SR 5, are compiled into the grammar from the 2024 text.
    for it in &CONF.corrigendum {
        assert!(
            !(it.kind == "syntax rule" && ["16.4", "13.1"].contains(&it.subclause.as_str())),
            "cor 1 edits {} syntax rules: {}",
            it.subclause,
            it.instruction
        );
    }
}

fn claim_file(text: &str) -> String {
    let dir = std::env::temp_dir().join(format!("gql-proof-claim-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{}.claim", text.len()));
    std::fs::write(&path, text).unwrap();
    path.to_string_lossy().into_owned()
}

#[test]
fn deviations_are_kept_out_and_checked() {
    let start = BASE.require("GQL-program").unwrap();
    let claim = Claim::parse(
        &claim_file(
            "GG01\n-<session close command>  # sessions are the driver's\n-'CURRENT_GRAPH'\n",
        ),
        &CONF,
    )
    .unwrap();
    assert_eq!(claim.deviations.len(), 2);
    let forbidden = CONF.forbidden(&claim);
    let deviations: Vec<_> = forbidden
        .iter()
        .filter(|f| f.label.starts_with("deviation "))
        .cloned()
        .collect();
    assert_eq!(deviations.len(), 2);
    // A tree with each is flagged by the verifier and refused by the automaton.
    let verifier = Verifier::new(Grammar::new(&ISO)).with_conformance(deviations.clone());
    for d in &deviations {
        let (tree, sentence) = witness(
            &BASE,
            start,
            MatchModeDefault::Portable,
            0,
            &[],
            &d.patterns[0],
        )
        .unwrap()
        .unwrap();
        assert_eq!(verifier.broken_conformance(&tree).len(), 1, "{sentence}");
        let rule: Vec<Box<dyn Rule>> = vec![Box::new(
            ClaimRules::new(&BASE, start, &deviations, &[]).unwrap(),
        )];
        assert!(accepts(&rule, &tree).is_err(), "{sentence}");
    }
    // A name the grammar does not have is an error when the claim is compiled.
    let bad = Claim::parse(&claim_file("GG01\n-<no such definition>\n"), &CONF).unwrap();
    assert!(ClaimRules::new(&BASE, start, &CONF.forbidden(&bad), &[]).is_err());
    assert!(Claim::parse(&claim_file("GG01\n-CURRENT_GRAPH\n"), &CONF).is_err());
}

#[test]
fn short_sentences_cover_what_packed_ones_do() {
    let start = BASE.require("GQL-program").unwrap();
    let forbidden = CONF.forbidden(&Claim::parse("all", &CONF).unwrap());
    let mut rules = all_rules(MatchModeDefault::Portable);
    rules.push(Box::new(
        ClaimRules::new(&BASE, start, &forbidden, &[]).unwrap(),
    ));
    let refined = refine(&BASE, &rules, start).unwrap();
    let analysis = Analysis::new(&refined.cfg, &StubProvider);
    let config = || Config {
        seed: 1,
        max_depth: analysis.reference_height(refined.start),
        length: Length::Reference,
    };
    let iso = |o: &gql_proof::purdom::Outcome| -> BTreeSet<u32> {
        o.covered
            .ones()
            .map(|p| refined.cfg.prods[p].unrefined)
            .collect()
    };
    let packed = Generator::new(&analysis, config(), StubProvider)
        .run(refined.start)
        .unwrap();
    let short = Generator::new(&analysis, config(), StubProvider)
        .run_short(refined.start, &BASE, Criteria::default())
        .unwrap();
    assert_eq!(iso(&short), iso(&packed));
    let tokens = |o: &gql_proof::purdom::Outcome| -> Vec<usize> {
        let mut l: Vec<usize> = o
            .trees
            .iter()
            .map(|t| t.root.render(&refined.cfg).split(' ').count())
            .collect();
        l.sort();
        l
    };
    let (s, p) = (tokens(&short), tokens(&packed));
    assert!(
        s[s.len() / 2] < p[p.len() / 2],
        "median {} vs {}",
        s[s.len() / 2],
        p[p.len() / 2]
    );
}

#[test]
fn engine_claims_generate_verified_trees() {
    // A claim forbids many definitions outright, which changes the grammar the rules are
    // compiled against: every tree under each committed claim still has to pass the verifier.
    let start = BASE.require("GQL-program").unwrap();
    for file in ["claims/neo4j.claim", "claims/turbolay.claim"] {
        let claim = Claim::parse(file, &CONF).unwrap();
        let forbidden = CONF.forbidden(&claim);
        let mut rules = all_rules(MatchModeDefault::Portable);
        rules.push(Box::new(
            ClaimRules::new(&BASE, start, &forbidden, &[]).unwrap(),
        ));
        let refined = refine(&BASE, &rules, start).unwrap();
        let analysis = Analysis::new(&refined.cfg, &StubProvider);
        let config = Config {
            seed: 1,
            max_depth: analysis.reference_height(refined.start),
            length: Length::Reference,
        };
        let outcome = Generator::new(&analysis, config, StubProvider)
            .run_short(refined.start, &BASE, Criteria::default())
            .unwrap();
        let verifier = Verifier::new(Grammar::new(&ISO))
            .with_syntax_rules(MatchModeDefault::Portable)
            .with_conformance(forbidden);
        for t in &outcome.trees {
            let tree = t.root.export(&refined.cfg);
            let violations = verifier.verify(&tree, &verifier.render(&tree));
            assert!(
                violations.is_empty(),
                "{file}: {violations:?} in {}",
                verifier.render(&tree)
            );
        }
    }
}
