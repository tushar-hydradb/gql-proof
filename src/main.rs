use anyhow::{Result, bail};
use clap::{Parser, Subcommand, ValueEnum};
use gql_proof::cfg::Cfg;
use gql_proof::coverage::{Criteria, Target, describe_target};
use gql_proof::features::{
    CONFORMANCE_JSON, Claim, ClaimRules, Conformance, Forbidden, Negative, Pattern, Statement,
    collapse, negative, witness,
};
use gql_proof::leaf::StubProvider;
use gql_proof::purdom::{Analysis, Config, Generator, Length, Reason, TargetReason};
use gql_proof::refine::{all_rules, refine};
use gql_proof::scope::Scope;
use gql_proof::tokens::{Grammar, Report};
use gql_proof::verify::Verifier;
use gql_proof::{EDITION, MatchModeDefault};
use gql_proof::{ISO_BNF_XML, bnf, describe};
use rayon::prelude::*;
use std::collections::{BTreeMap, BTreeSet};
use std::io::{self, Write};
use std::path::PathBuf;

#[derive(Parser)]
#[command(about = "grammar driven conformance evidence for GQL (ISO/IEC 39075)")]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// Generate a set of derivation trees that together use every production (Purdom 1972).
    Purdom(PurdomArgs),
    /// Check, once for the whole grammar, that rendering tokens joined by spaces is valid
    /// GQL source text (ISO/IEC 39075 21.3 SR 13, 14), and list what is assumed.
    CheckGrammar(CheckArgs),
    /// For every conformance rule of an unclaimed feature, the shortest query that breaks it
    /// and uses no other unclaimed feature: a query the engine must reject.
    Negatives(NegativesArgs),
    /// The conformance map from `just features`, and what a claim leaves in force.
    Features(FeaturesArgs),
    /// Parse sentences from elsewhere (another suite, an engine's tests) with the ISO grammar,
    /// verify them, and measure their coverage like ours. Two files are also compared.
    Cover(CoverArgs),
    /// Run the context engine alone on a part of the grammar and report where its time and
    /// labels went (`GQL_TRACE` filters logs, `--trace` writes a chrome trace).
    Context(ContextArgs),
}

#[derive(Parser)]
struct ContextArgs {
    /// The nonterminal to start from; below the program every label of it counts as whole.
    #[arg(long, default_value = "GQL-program")]
    start: String,
    #[arg(long, value_enum, default_value_t = ContextRule::Scope)]
    rule: ContextRule,
    /// The most variables one label holds.
    #[arg(long, default_value_t = 3)]
    slots: usize,
    /// The most variables a label of references alone holds; `--slots` if not given.
    #[arg(long)]
    references: Option<usize>,
    /// With `--rule types`: the most variables one label holds a type constraint on.
    #[arg(long, default_value_t = 2)]
    typed: usize,
    #[arg(long, value_enum, default_value_t = ContextPhase::Emit)]
    phase: ContextPhase,
    /// Stop after this many seconds in a phase, printing what was spent.
    #[arg(long)]
    deadline: Option<u64>,
    /// Write a chrome trace (open in perfetto) of every span.
    #[arg(long)]
    trace: Option<PathBuf>,
    /// Write every counter as json.
    #[arg(long)]
    stats: Option<PathBuf>,
    /// After the fixed point, measure one production alone: its id, or text of its
    /// description.
    #[arg(long)]
    production: Option<String>,
    /// Rows per table in the summary.
    #[arg(long, default_value_t = 12)]
    top: usize,
    /// Seeds to generate with, for `--phase generate`.
    #[arg(long, default_value_t = 2)]
    seeds: u64,
    /// Keep every fact in every label, even ones nothing above reads.
    #[arg(long)]
    no_live: bool,
    /// Emit with a backward pass per parent label, as before.
    #[arg(long)]
    no_single_pass: bool,
    /// Join labels the rule can join in the fixed point; emission makes them ground.
    #[arg(long)]
    join: bool,
    /// Skip pairs the rule's join keys rule out.
    #[arg(long)]
    keys: bool,
}

#[derive(Clone, Copy, PartialEq, ValueEnum)]
enum ContextRule {
    /// No context: what the engine costs by itself.
    None,
    Scope,
    /// Scope with value expression types under it.
    Types,
}

#[derive(Clone, Copy, PartialEq, PartialOrd, ValueEnum)]
enum ContextPhase {
    Fixpoint,
    Emit,
    Generate,
}

#[derive(Parser)]
struct CoverArgs {
    /// Sentence files: jsonl with a `query` or `sentence` field, or one sentence per line.
    files: Vec<PathBuf>,
    /// Cover every chain of up to this many symbol occurrences (k-path coverage).
    #[arg(long, default_value_t = 3)]
    k: u32,
    #[arg(long, default_value = "GQL-program")]
    start: String,
    /// Print every sentence that has no ISO parse.
    #[arg(long)]
    failures: bool,
    /// Targets to list per difference between two files.
    #[arg(long, default_value_t = 10)]
    show: usize,
    /// Also judge scoping twice, by the automaton `refine` compiles (`scope`, with the
    /// sentence's own names) and by the independent checker (`verify::scope`), and report
    /// where they disagree.
    #[arg(long)]
    scope: bool,
}

#[derive(Parser)]
struct NegativesArgs {
    /// The optional features claimed, as for `purdom`.
    #[arg(long, default_value = "none")]
    claim: String,
    /// Only this feature's rules.
    #[arg(long)]
    feature: Option<String>,
    /// The status an engine reports for language outside its claim. ISO leaves nonconforming
    /// language to the implementation (IE005), so this is declared, like ID086.
    #[arg(long, default_value = "42000")]
    unsupported_status: String,
    #[arg(long, value_enum, default_value_t = Id086::Portable)]
    match_mode_default: Id086,
    #[arg(long, default_value_t = 0)]
    seed: u64,
    /// `sentence` or `jsonl`.
    #[arg(long, value_enum, default_value_t = Format::Sentence)]
    format: Format,
}

#[derive(Parser)]
struct FeaturesArgs {
    /// Show what this claim leaves in force.
    #[arg(long, default_value = "all")]
    claim: String,
}

#[derive(Parser)]
struct CheckArgs {
    /// Start symbol.
    #[arg(long, default_value = "GQL-program")]
    start: String,
    /// Grammar XML. Defaults to the ISO file `just fetch` downloads.
    #[arg(long)]
    grammar: Option<PathBuf>,
}

#[derive(Parser)]
struct PurdomArgs {
    /// Compile the Syntax Rules a grammar can express (16.4 SR 6, 16.4 SR 14, 13.1 SR 5) into
    /// the grammar, so every query satisfies them.
    #[arg(long, value_enum, default_value_t = Rules::All)]
    rules: Rules,
    /// The names variables are spelled from, in the order they are given out, comma
    /// separated; numbered ones follow (`scope`).
    #[arg(long, default_value = "x,y,z,w")]
    names: String,
    /// The most variables one subtree's label holds (`scope`): every tree with at most this
    /// many variables live at once is generated.
    #[arg(long, default_value_t = 3)]
    slots: usize,
    /// The match mode a graph pattern without one gets (ID086). `portable` assumes neither,
    /// so queries are valid on any engine.
    #[arg(long, value_enum, default_value_t = Id086::Portable)]
    match_mode_default: Id086,
    /// The optional features claimed: `all`, `none` (only what 24.2 requires), or a file of
    /// feature codes. The conformance rules of every other feature are compiled into the
    /// grammar. Needs `grammar/conformance.json` (`just features`).
    #[arg(long, default_value = "all")]
    claim: String,
    /// Breaks ties between equally cheap choices. Same seed, same trees.
    #[arg(long, default_value_t = 0)]
    seed: u64,
    /// Maximum tree height. Productions that need more are reported, not dropped. Defaults
    /// to the reference height, the smallest cap under which every production fits.
    #[arg(long)]
    max_depth: Option<u32>,
    /// Start symbol.
    #[arg(long, default_value = "GQL-program")]
    start: String,
    /// Print only this tree (1-based). The summary still covers the whole set.
    #[arg(long)]
    tree: Option<usize>,
    #[arg(long, value_enum, default_value_t = Format::Both)]
    format: Format,
    /// Longest sentence, in Purdom's length (nodes in the derivation tree): `reference`, the
    /// smallest cap any covering set needs; `unbounded`; or a number. Productions whose
    /// shortest covering sentence is over a number are reported.
    #[arg(long, default_value = "reference", value_parser = parse_length)]
    length: Length,
    /// After Purdom's trees, cover every production at every place its nonterminal occurs
    /// (context-dependent rule coverage, Lämmel 2001).
    #[arg(long)]
    cdrc: bool,
    /// After Purdom's trees, cover every chain of up to this many symbol occurrences along a
    /// root path (k-path coverage, Havrikov & Zeller).
    #[arg(long, default_value_t = 0)]
    k: u32,
    /// Let CDRC and k-paths look inside token-level definitions.
    #[arg(long)]
    k_lexical: bool,
    /// No packing: only the shortest tree for each target not covered yet, so one construct
    /// an engine cannot handle hides little else. Covers CDRC unless `--k` is given.
    #[arg(long)]
    short: bool,
    /// Show lexical rules (identifiers, literals, ...) down to single characters.
    #[arg(long)]
    expand_lexical: bool,
    /// Print the coverage summary after the trees.
    #[arg(long)]
    summary: bool,
    /// Grammar XML. Defaults to the ISO file `just fetch` downloads.
    #[arg(long)]
    grammar: Option<PathBuf>,
}

#[derive(Clone, Copy, PartialEq, Eq, ValueEnum)]
enum Rules {
    /// The syntax rules, the claim's conformance rules and scoping.
    All,
    /// The syntax rules and the claim's conformance rules, without scoping.
    Syntax,
    None,
}

#[derive(Clone, Copy, PartialEq, Eq, ValueEnum)]
enum Id086 {
    Portable,
    DifferentEdges,
    RepeatableElements,
}

impl From<Id086> for MatchModeDefault {
    fn from(v: Id086) -> Self {
        match v {
            Id086::Portable => MatchModeDefault::Portable,
            Id086::DifferentEdges => MatchModeDefault::DifferentEdges,
            Id086::RepeatableElements => MatchModeDefault::RepeatableElements,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, ValueEnum)]
enum Format {
    Tree,
    Sentence,
    Both,
    /// Only the coverage summary, same as `--summary` with no trees.
    Summary,
    /// One JSON object per tree (`tree`, `length`, `height`, `new`, `sentence`), no summary. Sentences
    /// can contain newlines from comments and whitespace, so this is the format for tooling.
    Jsonl,
}

fn parse_length(s: &str) -> Result<Length, String> {
    match s {
        "reference" => Ok(Length::Reference),
        "unbounded" => Ok(Length::Unbounded),
        n => n
            .parse()
            .map(Length::Cap)
            .map_err(|_| format!("expected reference, unbounded or a number, got {n:?}")),
    }
}

fn main() -> Result<()> {
    let result = match Cli::parse().cmd {
        Cmd::Purdom(args) => purdom(args),
        Cmd::CheckGrammar(args) => check_grammar(args),
        Cmd::Negatives(args) => negatives(args),
        Cmd::Features(args) => features(args),
        Cmd::Cover(args) => cover(args),
        Cmd::Context(args) => context(args),
    };
    // A closed pipe (`| head`) is the reader being done, not an error.
    match result {
        Err(e)
            if e.downcast_ref::<io::Error>()
                .is_some_and(|e| e.kind() == io::ErrorKind::BrokenPipe) =>
        {
            Ok(())
        }
        other => other,
    }
}

fn context(args: ContextArgs) -> Result<()> {
    use tracing_subscriber::prelude::*;
    use tracing_subscriber::{EnvFilter, fmt};
    // Logs as `GQL_TRACE` says (off unless asked), the chrome trace with every span the
    // engine opens at debug and above.
    let logs = fmt::layer().with_writer(io::stderr).with_filter(
        EnvFilter::try_from_env("GQL_TRACE").unwrap_or_else(|_| EnvFilter::new("warn")),
    );
    let (chrome, _guard) = match &args.trace {
        Some(path) => {
            let (layer, guard) = tracing_chrome::ChromeLayerBuilder::new()
                .file(path)
                .include_args(true)
                .build();
            (
                Some(layer.with_filter(EnvFilter::new("gql_proof=debug"))),
                Some(guard),
            )
        }
        None => (None, None),
    };
    tracing_subscriber::registry()
        .with(logs)
        .with(chrome)
        .init();

    let bnf = bnf::parse(ISO_BNF_XML)?;
    let base = Cfg::from_bnf(&bnf);
    let start = base.require(&args.start)?;
    let options = gql_proof::context::Options {
        progress: true,
        deadline: args.deadline.map(std::time::Duration::from_secs),
        any_top: args.start != "GQL-program",
        reads_all: (args.start != "GQL-program").then_some(start),
        live: !args.no_live,
        single_pass: !args.no_single_pass,
        join: args.join,
        keys: args.keys,
    };
    let scope = gql_proof::context::scope::Scope {
        caps: gql_proof::context::scope::Caps {
            slots: args.slots,
            references: args.references.unwrap_or(args.slots),
        },
    };
    match args.rule {
        ContextRule::None => {
            context_run(&base, start, &gql_proof::context::Nothing, &options, &args)
        }
        ContextRule::Scope => context_run(&base, start, &scope, &options, &args),
        ContextRule::Types => {
            let types = gql_proof::context::types::Types::with_typed(&base, args.typed);
            let pair = gql_proof::context::pair::Typed::new(scope, types);
            context_run(&base, start, &pair, &options, &args)
        }
    }
}

fn context_run<C: gql_proof::context::Context>(
    base: &Cfg,
    start: u32,
    ctx: &C,
    options: &gql_proof::context::Options,
    args: &ContextArgs,
) -> Result<()> {
    let analyzed = gql_proof::context::analyze(base, ctx, options)?;
    if let Some(which) = &args.production {
        let p = match which.parse::<u32>() {
            Ok(p) => p,
            Err(_) => (0..base.prods.len() as u32)
                .find(|&p| describe(base, p).contains(which.as_str()))
                .ok_or_else(|| anyhow::anyhow!("no production like {which:?}"))?,
        };
        let profile = analyzed.profile(p);
        eprintln!("{}", describe(base, p));
        eprintln!("  labels per position: {:?}", profile.children);
        eprintln!(
            "  partial labels after each position: {:?}",
            profile.partials
        );
        eprint!("{}", profile.stats.summary(args.top));
    }
    let mut stats = analyzed.stats();
    if args.phase >= ContextPhase::Emit {
        let built = analyzed.emit(start, "x")?;
        stats = built.stats.clone();
        eprintln!(
            "emitted {} nonterminals, {} productions",
            built.cfg.nts.len(),
            built.cfg.prods.len()
        );
        if args.phase == ContextPhase::Generate {
            let began = std::time::Instant::now();
            let names: Vec<String> = ["x", "y", "z", "w"].iter().map(|s| s.to_string()).collect();
            let analysis = Analysis::new(&built.cfg, &StubProvider);
            let height = analysis.reference_height(built.start);
            let (mut trees, mut failed, mut untyped) = (0, 0, 0);
            // The smallest failing tree, with its labels, for `GQL_SHOW_FAIL`.
            let mut smallest: Option<(usize, String)> = None;
            for seed in 0..args.seeds {
                let config = Config {
                    seed,
                    max_depth: height,
                    length: Length::Reference,
                };
                let outcome = Generator::new(&analysis, config, StubProvider).run(built.start)?;
                for t in outcome.trees {
                    let mut root = t.root;
                    built.name(&mut root, &names, |nt, s| analysis.spell(nt, s))?;
                    trees += 1;
                    let plain = root.export(&built.cfg);
                    let mut violations = gql_proof::verify::scope::check(&plain);
                    let scoped = violations.is_empty();
                    if args.rule == ContextRule::Types {
                        violations.extend(gql_proof::verify::types::check(&plain));
                    }
                    if !violations.is_empty() {
                        if scoped {
                            untyped += 1;
                        } else {
                            failed += 1;
                        }
                        if failed + untyped <= 5 {
                            eprintln!("{}\n  {violations:?}", root.render(&built.cfg));
                        }
                        let sentence = root.render(&built.cfg);
                        if std::env::var("GQL_SHOW_FAIL").is_ok()
                            && smallest.as_ref().is_none_or(|(n, _)| sentence.len() < *n)
                        {
                            let shown = format!(
                                "{sentence}\n{violations:?}\n{}",
                                root.display(&built.cfg, false)
                            );
                            smallest = Some((sentence.len(), shown));
                        }
                    }
                }
            }
            stats
                .phases
                .insert("generate".into(), began.elapsed().as_nanos() as u64);
            eprintln!(
                "generated {trees} trees, {failed} fail the scope checker, {untyped} only the \
                 types checker"
            );
            if let Some((_, shown)) = smallest {
                eprintln!("smallest failing tree:\n{shown}");
            }
        }
    }
    eprint!("{}", stats.summary(args.top));
    if let Some(path) = &args.stats {
        std::fs::write(path, serde_json::to_string_pretty(&stats)?)?;
    }
    Ok(())
}

fn read_grammar(path: &Option<PathBuf>) -> Result<bnf::Bnf> {
    let xml = match path {
        Some(path) => std::fs::read_to_string(path)?,
        None => ISO_BNF_XML.to_string(),
    };
    bnf::parse(&xml)
}

fn check_grammar(args: CheckArgs) -> Result<()> {
    let bnf = read_grammar(&args.grammar)?;
    let grammar = Grammar::new(&bnf);
    if grammar.rhs(&args.start).is_none() {
        bail!("no definition named <{}>", args.start);
    }
    let report = grammar.check(&args.start);
    write_report(&mut io::stdout().lock(), &report)?;
    if !report.passed() {
        bail!("{} failed obligations", report.failures.len());
    }
    Ok(())
}

fn write_report(out: &mut impl Write, report: &Report) -> io::Result<()> {
    writeln!(out, "# token boundaries from <{}>", report.start)?;
    writeln!(out, "syntactic definitions: {}", report.syntactic)?;
    writeln!(
        out,
        "lexical definitions printed as one token: {}",
        report.boundary
    )?;
    writeln!(
        out,
        "definitions provably single tokens: {}",
        report.token_defs
    )?;
    if report.passed() {
        writeln!(out, "obligations: all hold")?;
    } else {
        writeln!(out, "failed obligations: {}", report.failures.len())?;
        for f in &report.failures {
            writeln!(out, "  {f}")?;
        }
    }
    writeln!(out, "assumed tokens: {}", report.assumptions.len())?;
    for (def, why) in &report.assumptions {
        writeln!(out, "  <{def}>: {why}")?;
    }
    writeln!(out, "excluded, never generated: {}", report.excluded.len())?;
    for (def, why) in &report.excluded {
        writeln!(out, "  <{def}>: {why}")?;
    }
    Ok(())
}

fn purdom(args: PurdomArgs) -> Result<()> {
    let bnf = read_grammar(&args.grammar)?;
    let grammar = Grammar::new(&bnf);
    let report = grammar.check(&args.start);
    if !report.passed() {
        write_report(&mut io::stderr().lock(), &report)?;
        bail!("the grammar fails the token boundary check, refusing to generate");
    }
    let id086 = MatchModeDefault::from(args.match_mode_default);
    let base = Cfg::from_bnf(&bnf);
    let conformance = Conformance::load(CONFORMANCE_JSON)?;
    let claim = Claim::parse(&args.claim, &conformance)?;
    let forbidden = conformance.forbidden(&claim);
    let names: Vec<&str> = args.names.split(',').collect();
    let mut rules = match args.rules {
        Rules::All | Rules::Syntax => all_rules(id086),
        Rules::None => Vec::new(),
    };
    let mut verifier = match args.rules {
        Rules::All | Rules::Syntax => Verifier::new(grammar).with_syntax_rules(id086),
        Rules::None => Verifier::new(grammar),
    };
    let start = base.require(&args.start)?;
    if args.rules != Rules::None {
        rules.push(Box::new(ClaimRules::new(&base, start, &forbidden, &[])?));
        verifier = verifier.with_conformance(forbidden.clone());
    }
    if args.rules == Rules::All {
        verifier = verifier.with_scope();
    }
    // What the grammar allows under every claim, to tell productions the claim excludes from
    // ones nothing allows.
    let everything = if args.rules != Rules::None && claim != Claim::parse("all", &conformance)? {
        let mut all = all_rules(id086);
        let devices = conformance.forbidden(&Claim::parse("all", &conformance)?);
        all.push(Box::new(ClaimRules::new(&base, start, &devices, &[])?));
        Some(refine(&base, &all, start)?)
    } else {
        None
    };
    let claimable = everything
        .as_ref()
        .map(|r| reachable_copies(&r.cfg, r.start));
    let refined = refine(&base, &rules, start)?;
    // Scoping: the context engine over the grammar the syntax rules and the claim refined.
    let built = if args.rules == Rules::All {
        let scope = gql_proof::context::scope::Scope {
            caps: gql_proof::context::scope::Caps {
                slots: args.slots,
                references: args.slots,
            },
        };
        let options = gql_proof::context::Options {
            progress: false,
            ..Default::default()
        };
        Some(gql_proof::context::build(
            &refined.cfg,
            &scope,
            refined.start,
            names[0],
            &options,
        )?)
    } else {
        None
    };
    let (cfg, start) = match &built {
        Some(b) => (b.cfg.clone(), b.start),
        None => (refined.cfg, refined.start),
    };
    let analysis = Analysis::new(&cfg, &StubProvider);
    let reference_height = analysis.reference_height(start);
    let max_depth = args.max_depth.unwrap_or(reference_height);
    let config = Config {
        seed: args.seed,
        max_depth,
        length: args.length,
    };
    let criteria = Criteria {
        cdrc: args.cdrc,
        k: args.k,
        lexical: args.k_lexical,
    };
    let generator = Generator::new(&analysis, config, StubProvider);
    let mut outcome = if args.short {
        generator.run_short(start, &base, criteria)?
    } else {
        generator.run_with(start, &base, criteria)?
    };
    // Variables get their names once each tree is built.
    if let Some(built) = &built {
        let names: Vec<String> = names.iter().map(|s| s.to_string()).collect();
        for generated in &mut outcome.trees {
            built.name(&mut generated.root, &names, |nt, s| analysis.spell(nt, s))?;
        }
    }

    // Nothing is printed unless every tree passes the independent checker.
    let mut failed = 0;
    for (i, generated) in outcome.trees.iter().enumerate() {
        let root = &generated.root;
        let violations = verifier.verify(&root.export(&cfg), &root.render(&cfg));
        if !violations.is_empty() {
            failed += 1;
            eprintln!("# tree {} fails verification", i + 1);
            for v in &violations {
                eprintln!("  {v}");
            }
            eprintln!("  sentence: {}", root.render(&cfg));
        }
    }
    if failed > 0 {
        bail!(
            "{failed} of {} trees failed verification",
            outcome.trees.len()
        );
    }

    let mut out = std::io::stdout().lock();

    for (i, generated) in outcome.trees.iter().enumerate() {
        let n = i + 1;
        if args.format == Format::Summary || args.tree.is_some_and(|t| t != n) {
            continue;
        }
        let root = &generated.root;
        if args.format == Format::Jsonl {
            let record = serde_json::json!({
                "tree": n,
                "length": generated.length,
                "height": root.height(),
                "new": generated.new,
                "sentence": root.render(&cfg),
            });
            writeln!(out, "{record}")?;
            continue;
        }
        writeln!(
            out,
            "# tree {n}: length {}, height {}, {} new productions{}",
            generated.length,
            root.height(),
            generated.new,
            generated
                .covers
                .as_ref()
                .map_or(String::new(), |c| format!(", covers {c}"))
        )?;
        if matches!(args.format, Format::Tree | Format::Both) {
            write!(out, "{}", root.display(&cfg, args.expand_lexical))?;
        }
        if matches!(args.format, Format::Sentence | Format::Both) {
            writeln!(out, "{}", root.render(&cfg))?;
        }
        writeln!(out)?;
    }

    // jsonl stays machine readable, so it never gets the summary.
    let summary = (args.summary && args.format != Format::Jsonl) || args.format == Format::Summary;
    if !summary {
        return Ok(());
    }
    // Coverage of the ISO productions: covered when any refined copy is.
    let mut iso_covered = vec![false; base.prods.len()];
    // A copy counts when a tree from the start can use it: refinement also keeps copies in
    // contexts no tree reaches.
    let has_copy = reachable_copies(&cfg, start);
    let mut base_reach = vec![false; base.nts.len()];
    for nt in base.reachable(base.require(&args.start)?) {
        base_reach[nt as usize] = true;
    }
    for p in outcome.covered.ones() {
        iso_covered[cfg.prods[p].unrefined as usize] = true;
    }
    let total = base.prods.len();
    let covered = iso_covered.iter().filter(|&&c| c).count();
    writeln!(out, "# summary")?;
    let depth_note = match args.max_depth {
        None => " (reference height)".to_string(),
        Some(_) => format!(" (reference height {reference_height})"),
    };
    writeln!(
        out,
        "seed {}, max depth {max_depth}{depth_note}, start <{}>",
        args.seed, args.start
    )?;
    let cap = match (args.length, outcome.length_cap) {
        (Length::Unbounded, _) => "unbounded".to_string(),
        (Length::Reference, Some(c)) => format!("{c} (reference length)"),
        (_, Some(c)) => format!("{c} (reference length {})", outcome.reference_length),
        (_, None) => "unbounded".to_string(),
    };
    writeln!(out, "length cap: {cap}")?;
    writeln!(
        out,
        "trees: {}, all verified (iso ebnf, prose leaves, token rules, rendering{})",
        outcome.trees.len(),
        if rules.is_empty() {
            ""
        } else {
            ", syntax rules"
        }
    )?;
    let lengths: Vec<u32> = outcome.trees.iter().map(|t| t.length).collect();
    if let (Some(min), Some(max)) = (lengths.iter().min(), lengths.iter().max()) {
        let avg = lengths.iter().sum::<u32>() as f64 / lengths.len() as f64;
        writeln!(out, "sentence length: min {min}, avg {avg:.1}, max {max}")?;
    }
    writeln!(
        out,
        "productions covered: {covered} of {total} (desugared: every [..] both ways, every ... once and repeated)"
    )?;
    if !rules.is_empty() {
        writeln!(
            out,
            "in context: {} of {} (each production in each state the rules tell apart, bookkeeping states not counted)",
            outcome
                .covered
                .ones()
                .map(|p| cfg.prods[p].context)
                .collect::<BTreeSet<_>>()
                .len(),
            cfg.prods
                .iter()
                .map(|p| p.context)
                .collect::<BTreeSet<_>>()
                .len()
        )?;
    }

    // One reason per uncovered ISO production, from its first uncovered copy.
    let mut iso_reason: Vec<Option<Reason>> = vec![None; total];
    for &(p, reason) in &outcome.uncovered {
        let u = cfg.prods[p as usize].unrefined as usize;
        if !iso_covered[u] && iso_reason[u].is_none() {
            iso_reason[u] = Some(reason);
        }
    }
    // What the plain grammar cannot reach is unreachable, whatever the rules did to the copies
    // refinement keeps of it.
    for u in 0..total {
        if !iso_covered[u] && !base_reach[base.prod(u as u32).lhs as usize] {
            iso_reason[u] = Some(Reason::Unreachable);
        }
    }
    let mut by_reason: BTreeMap<&str, Vec<String>> = BTreeMap::new();
    for u in (0..total).filter(|&u| !iso_covered[u]) {
        let p = u as u32;
        if !has_copy[u] && base_reach[base.prod(p).lhs as usize] {
            let key = match &claimable {
                Some(has) if has[u] => "outside the claim",
                _ => {
                    "forbidden in every context (syntax rules, or conformance rules every claim keeps)"
                }
            };
            by_reason.entry(key).or_default().push(describe(&base, p));
            continue;
        }
        let Some(reason) = iso_reason[u] else {
            continue;
        };
        let cfg = &base;
        let (key, line) = match reason {
            Reason::Unreachable => ("unreachable from start", describe(cfg, p)),
            Reason::Unproductive => ("no finite derivation", describe(cfg, p)),
            Reason::NoLeaf => ("needs a prose leaf with no portable form", describe(cfg, p)),
            Reason::NeedsDepth(d) => (
                "needs a deeper tree",
                format!("{} (depth {d})", describe(cfg, p)),
            ),
            Reason::NeedsLength(l) => (
                "needs a longer sentence",
                format!("{} (length {l})", describe(cfg, p)),
            ),
        };
        by_reason.entry(key).or_default().push(line);
    }
    for (reason, lines) in by_reason {
        writeln!(out, "{reason}: {}", lines.len())?;
        // Unreachable productions are mostly the lexical layer (whitespace, comments), which
        // is reachable from <token> instead. Group those by ISO definition to keep it short;
        // the same for what the claim excludes, which can be most of the grammar.
        if reason == "outside the claim" {
            let mut defs: BTreeMap<&str, usize> = BTreeMap::new();
            for l in &lines {
                let def = l.split(" ::=").next().unwrap_or(l);
                *defs.entry(def).or_default() += 1;
            }
            writeln!(out, "  in {} definitions", defs.len())?;
        } else if reason == "unreachable from start" {
            let mut defs: BTreeMap<String, usize> = BTreeMap::new();
            for u in (0..total).filter(|&u| !iso_covered[u]) {
                if iso_reason[u] == Some(Reason::Unreachable) {
                    let origin = &base.nts[base.prod(u as u32).lhs as usize].origin;
                    *defs.entry(origin.clone()).or_default() += 1;
                }
            }
            let names: Vec<String> = defs.keys().map(|d| format!("<{d}>")).collect();
            writeln!(
                out,
                "  in {} definitions: {}",
                names.len(),
                names.join(", ")
            )?;
        } else {
            for l in lines {
                writeln!(out, "  {l}")?;
            }
        }
    }
    for report in &outcome.targets {
        let reference = report
            .reference_length
            .map_or(String::new(), |r| format!(", reference length {r}"));
        writeln!(
            out,
            "{}: covered {} of {}, {} targeted trees{reference}",
            report.kind, report.covered, report.total, report.trees
        )?;
        // Targets no tree under this claim holds: outside the claim when one under every claim
        // does.
        let never: Vec<Target> = report
            .uncovered
            .iter()
            .filter(|(_, r)| *r == TargetReason::Never)
            .map(|(t, _)| t.clone())
            .collect();
        let outside: BTreeSet<&Target> = match &everything {
            Some(all) if !never.is_empty() => {
                let analysis = Analysis::new(&all.cfg, &StubProvider);
                let config = Config {
                    seed: args.seed,
                    max_depth,
                    length: args.length,
                };
                let generator = Generator::new(&analysis, config, StubProvider);
                never
                    .iter()
                    .zip(generator.realizable(all.start, &never))
                    .filter(|(_, ok)| *ok)
                    .map(|(t, _)| {
                        report
                            .uncovered
                            .iter()
                            .map(|(u, _)| u)
                            .find(|u| *u == t)
                            .unwrap()
                    })
                    .collect()
            }
            _ => BTreeSet::new(),
        };
        let mut by_reason: BTreeMap<String, Vec<&Target>> = BTreeMap::new();
        for (t, reason) in &report.uncovered {
            let key = match reason {
                TargetReason::NeedsDepth => "needs a deeper tree".to_string(),
                TargetReason::NeedsLength(_) => "needs a longer sentence".to_string(),
                TargetReason::Never if outside.contains(t) => "outside the claim".to_string(),
                TargetReason::Never => "in no tree the grammar and its rules allow".to_string(),
                TargetReason::FixedToken => "inside a token the leaf provider fixes".to_string(),
            };
            by_reason.entry(key).or_default().push(t);
        }
        for (reason, targets) in by_reason {
            writeln!(out, "  {reason}: {}", targets.len())?;
            for t in targets.iter().take(5) {
                writeln!(out, "    {}", describe_target(&base, t))?;
            }
            if targets.len() > 5 {
                writeln!(out, "    ...")?;
            }
        }
    }
    if !rules.is_empty() {
        writeln!(
            out,
            "syntax rules compiled into the grammar: {}",
            rules.len()
        )?;
        for rule in &rules {
            writeln!(out, "  {}", rule.cite())?;
        }
        writeln!(out, "  ID086 (default match mode): {:?}", id086)?;
        let unenforced = conformance.unenforced(&claim);
        writeln!(
            out,
            "claim: {} of {} features (closed under table 10), {} conformance rules in force, {} more not enforced by the grammar (`features --claim`)",
            claim.features.len(),
            conformance.features.len(),
            forbidden.len(),
            unenforced.len()
        )?;
        write_claim_notes(&mut out, &forbidden)?;
    }
    writeln!(out)?;
    write_report(&mut out, &report)?;
    Ok(())
}

/// The deviations a claim states and the readings its rules in force rely on.
fn write_claim_notes(out: &mut impl Write, forbidden: &[Forbidden]) -> io::Result<()> {
    writeln!(out, "edition: {EDITION}")?;
    let deviations: Vec<&str> = forbidden
        .iter()
        .filter_map(|f| f.label.strip_prefix("deviation "))
        .collect();
    if !deviations.is_empty() {
        writeln!(
            out,
            "deviations, mandatory syntax left out: {}",
            deviations.join(", ")
        )?;
    }
    let readings: Vec<String> = forbidden
        .iter()
        .flat_map(|f| f.readings.iter().map(move |r| format!("{}: {r}", f.label)))
        .collect();
    if !readings.is_empty() {
        writeln!(
            out,
            "rules in force read through single-item rules: {}",
            readings.len()
        )?;
        for r in readings {
            writeln!(out, "  {r}")?;
        }
    }
    Ok(())
}

/// Per unrefined production, whether some copy of it is in a tree from `start`.
fn reachable_copies(cfg: &Cfg, start: u32) -> Vec<bool> {
    let base_len = cfg
        .prods
        .iter()
        .map(|p| p.unrefined as usize + 1)
        .max()
        .unwrap_or(0);
    let mut has = vec![false; base_len];
    for nt in cfg.reachable(start) {
        for &p in &cfg.nts[nt as usize].prods {
            has[cfg.prods[p as usize].unrefined as usize] = true;
        }
    }
    has
}

fn negatives(args: NegativesArgs) -> Result<()> {
    let bnf = read_grammar(&None)?;
    let base = Cfg::from_bnf(&bnf);
    let start = base.require("GQL-program")?;
    let id086 = MatchModeDefault::from(args.match_mode_default);
    let conformance = Conformance::load(CONFORMANCE_JSON)?;
    let claim = Claim::parse(&args.claim, &conformance)?;
    let verifier = Verifier::new(Grammar::new(&bnf))
        .with_syntax_rules(id086)
        .with_conformance(conformance.forbidden(&claim));
    let names: BTreeMap<&str, &str> = conformance
        .features
        .iter()
        .map(|f| (f.code.as_str(), f.name.as_str()))
        .collect();
    let mut out = io::stdout().lock();
    let wanted: Vec<_> = conformance
        .statements
        .iter()
        .filter(|s| {
            s.kind == "pattern"
                && !claim.features.contains(&s.feature)
                && args.feature.as_ref().is_none_or(|f| *f == s.feature)
        })
        .flat_map(|s| s.forbid.iter().map(move |p| (s, p)))
        .collect();
    // Each search refines the grammar on its own, so they run in parallel; results keep the
    // statements' order.
    let found: Vec<Negative> = wanted
        .par_iter()
        .map(|&(s, pattern)| {
            negative(
                &base,
                start,
                id086,
                args.seed,
                &conformance,
                &claim,
                &verifier,
                s,
                pattern,
            )
        })
        .collect::<Result<_>>()?;
    let (mut made, tried, mut without) = (0, wanted.len(), Vec::new());
    for (&(s, _), found) in wanted.iter().zip(found) {
        {
            let sentence = match found {
                Negative::Query(_, sentence) => sentence,
                Negative::Needs(also) => {
                    let why = if also.is_empty() {
                        "no query has it".to_string()
                    } else {
                        let also: Vec<String> = also.into_iter().collect();
                        format!("its shortest query also needs {}", also.join(", "))
                    };
                    without.push(format!("{}: {why}", s.cite()));
                    continue;
                }
            };
            made += 1;
            let name = names.get(s.feature.as_str()).copied().unwrap_or("");
            match args.format {
                Format::Jsonl => {
                    let record = serde_json::json!({
                        "negative": made,
                        "phase": "feature",
                        "feature": s.feature,
                        "rule": s.cite(),
                        "expect": args.unsupported_status,
                        "sentence": sentence,
                    });
                    writeln!(out, "{record}")?;
                }
                _ => {
                    writeln!(
                        out,
                        "# negative {made}: {} ({name}), expect {}",
                        s.cite(),
                        args.unsupported_status
                    )?;
                    writeln!(out, "{sentence}\n")?;
                }
            }
        }
    }
    if args.format != Format::Jsonl {
        writeln!(out, "# summary")?;
        writeln!(
            out,
            "claim: {} features, negatives: {made} for {tried} patterns of unclaimed features",
            claim.features.len()
        )?;
        write_claim_notes(&mut out, &conformance.forbidden(&claim))?;
        if !without.is_empty() {
            writeln!(
                out,
                "no query breaks only its own feature: {}",
                without.len()
            )?;
            for w in &without {
                writeln!(out, "  {w}")?;
            }
        }
    }
    Ok(())
}

fn features(args: FeaturesArgs) -> Result<()> {
    let bnf = read_grammar(&None)?;
    let base = Cfg::from_bnf(&bnf);
    let start = base.require("GQL-program")?;
    let conformance = Conformance::load(CONFORMANCE_JSON)?;
    let claim = Claim::parse(&args.claim, &conformance)?;
    let mut out = io::stdout().lock();
    let mut kinds: BTreeMap<&str, usize> = BTreeMap::new();
    for s in &conformance.statements {
        *kinds.entry(s.kind.as_str()).or_default() += 1;
    }
    let kinds: Vec<String> = kinds.iter().map(|(k, n)| format!("{n} {k}")).collect();
    writeln!(out, "# conformance map ({CONFORMANCE_JSON})")?;
    writeln!(
        out,
        "features: {}, statements: {} ({}), unconditional: {}, implications: {}, claim rules: {}",
        conformance.features.len(),
        conformance.statements.len(),
        kinds.join(", "),
        conformance.devices.len(),
        conformance.implies.len(),
        conformance.claim_rules.len()
    )?;
    let mut applied: BTreeMap<&str, usize> = BTreeMap::new();
    for it in &conformance.corrigendum {
        *applied
            .entry(it.applied.as_deref().unwrap_or("recorded only"))
            .or_default() += 1;
    }
    let applied: Vec<String> = applied.iter().map(|(k, n)| format!("{n} {k}")).collect();
    writeln!(
        out,
        "edition: {EDITION}, cor 1 items: {} ({}), statements from cor 1: {}",
        conformance.corrigendum.len(),
        applied.join(", "),
        conformance
            .statements
            .iter()
            .filter(|s| s.source != "2024")
            .count()
    )?;
    for f in conformance.features.iter().filter(|f| f.cor1.is_some()) {
        writeln!(
            out,
            "  {} {} by cor 1: {}",
            f.code,
            f.cor1.as_deref().unwrap_or(""),
            f.name
        )?;
    }
    for n in &conformance.notes {
        writeln!(out, "  {n}")?;
    }
    let forbidden = conformance.forbidden(&claim);
    let patterns: Vec<Pattern> = forbidden.iter().flat_map(|f| f.patterns.clone()).collect();
    let (_, notes) = collapse(&base, start, &patterns)?;
    // Compiling checks every name against the grammar.
    let compiled = ClaimRules::new(&base, start, &forbidden, &[])?;
    for s in compiled.order_scopes() {
        writeln!(out, "order rule {s}")?;
    }
    writeln!(
        out,
        "claim {}: {} features after table 10, {} rules in force, all names resolve in the grammar",
        args.claim,
        claim.features.len(),
        forbidden.len()
    )?;
    if !notes.is_empty() {
        writeln!(out, "rules that forbid a whole definition: {}", notes.len())?;
        for n in &notes {
            writeln!(out, "  {n}")?;
        }
    }
    // Readings: "immediately contains" that can match nothing as written, read through
    // single-item rules, for every claim.
    let read: Vec<&Statement> = conformance
        .statements
        .iter()
        .filter(|s| !s.readings.is_empty() || !s.vacuous.is_empty())
        .collect();
    if !read.is_empty() {
        writeln!(
            out,
            "rules read through single-item rules, since as written they match nothing: {}",
            read.len()
        )?;
        for s in read {
            for r in &s.readings {
                writeln!(out, "  {}: {r}", s.cite())?;
            }
            for v in &s.vacuous {
                writeln!(out, "  {}: left as written, {v}", s.cite())?;
            }
        }
    }
    // Every pattern should match some tree; one that cannot is a rule no query breaks as
    // written, which is either an extraction bug or a mismatch between ISO's prose and its BNF.
    let patterns: Vec<(&Statement, &Pattern)> = conformance
        .statements
        .iter()
        .filter(|s| s.kind == "pattern")
        .flat_map(|s| s.forbid.iter().map(move |p| (s, p)))
        .collect();
    let unbreakable: Vec<String> = patterns
        .par_iter()
        .map(|&(s, p)| {
            witness(&base, start, MatchModeDefault::Portable, 0, &[], p)
                .map(|w| w.is_none().then(|| s.cite()))
        })
        .collect::<Result<Vec<_>>>()?
        .into_iter()
        .flatten()
        .collect();
    writeln!(
        out,
        "rules no query breaks as written (with the syntax rules, any claim): {}",
        unbreakable.len()
    )?;
    for c in &unbreakable {
        writeln!(out, "  {c}")?;
    }
    let mut owners: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for s in conformance.unenforced(&claim) {
        let owner = format!("{} ({})", s.kind, s.owner.as_deref().unwrap_or("?"));
        owners.entry(owner).or_default().push(s.cite());
    }
    if !owners.is_empty() {
        writeln!(out, "in force but not enforced by the grammar:")?;
        for (owner, cites) in owners {
            writeln!(out, "  {owner}: {}", cites.len())?;
            for c in cites {
                writeln!(out, "    {c}")?;
            }
        }
    }
    Ok(())
}

/// One file's sentences as the ISO grammar reads them.
struct Covered {
    sentences: usize,
    /// Sentences with no ISO parse, with why.
    unparsed: Vec<(String, String)>,
    /// Parsed sentences whose every tree (up to the limit) fails the verifier, with the first
    /// tree's first violation.
    unverified: Vec<(String, String)>,
    /// Parsed sentences with more than one tree.
    ambiguous: usize,
    prods: BTreeSet<u32>,
    targets: BTreeSet<Target>,
    /// Per parsed sentence with `--scope`: the automaton's rejection and the checker's first
    /// violation, if any.
    scope: Vec<(String, Option<String>, Option<String>)>,
}

/// The names a sentence's variables and columns could have: its binding variables and
/// identifiers.
fn names_in(p: &gql_proof::verify::Plain, out: &mut BTreeSet<String>) {
    if let gql_proof::verify::Plain::Def { name, children, .. } = p {
        if name == "binding variable" || name == "identifier" {
            out.insert(p.text());
        }
        children.iter().for_each(|c| names_in(c, out));
    }
}

fn read_sentences(path: &PathBuf) -> Result<Vec<String>> {
    let text = std::fs::read_to_string(path)?;
    let mut out = Vec::new();
    for line in text.lines().filter(|l| !l.trim().is_empty()) {
        match serde_json::from_str::<serde_json::Value>(line) {
            Ok(serde_json::Value::Object(record)) => {
                let sentence = record
                    .get("query")
                    .or_else(|| record.get("sentence"))
                    .and_then(|v| v.as_str())
                    .ok_or_else(|| anyhow::anyhow!("{}: a record with no query", path.display()))?;
                out.push(sentence.to_string());
            }
            _ => out.push(line.to_string()),
        }
    }
    Ok(out)
}

fn cover(args: CoverArgs) -> Result<()> {
    let bnf = read_grammar(&None)?;
    let cfg = Cfg::from_bnf(&bnf);
    let start = cfg.require(&args.start)?;
    let criteria = Criteria {
        cdrc: true,
        k: args.k,
        lexical: false,
    };
    let all_targets = gql_proof::coverage::targets(&cfg, start, criteria);
    let mut out = io::stdout().lock();
    writeln!(
        out,
        "# coverage of sentences read with the {EDITION} grammar"
    )?;
    let mut results = Vec::new();
    for path in &args.files {
        let sentences = read_sentences(path)?;
        let distinct: BTreeSet<&str> = sentences.iter().map(String::as_str).collect();
        // A long literal is a deep tree (a repeat desugars to right recursion), and every walk
        // over a tree recurses, dropping it included: trees stay on threads with deep stacks
        // and only their coverage comes back.
        let pool = rayon::ThreadPoolBuilder::new()
            .stack_size(1 << 30)
            .build()?;
        type Verdicts = Option<(Option<String>, Option<String>)>;
        type Read = (Option<String>, bool, Vec<u32>, BTreeSet<Target>, Verdicts);
        let parsed: Vec<(String, Result<Read>)> = pool.install(|| {
            distinct
                .par_iter()
                .map_init(
                    || {
                        let tokens = Grammar::new(&bnf);
                        let verifier = Verifier::new(Grammar::new(&bnf));
                        let parser = gql_proof::parse::Parser::new(&cfg, &tokens, &args.start)
                            .expect("the iso grammar builds");
                        (parser, verifier)
                    },
                    |(parser, verifier), s| {
                        let accept = |n: &gql_proof::tree::Node| {
                            verifier.verify(&n.export(&cfg), &n.render(&cfg)).is_empty()
                        };
                        let covered = parser.parse(s, accept).map(|p| {
                            let mut prods = Vec::new();
                            p.tree.prods(&mut prods);
                            let targets = gql_proof::coverage::observe(&cfg, &p.tree, criteria);
                            let violation = (!p.accepted).then(|| {
                                let tree = &p.tree;
                                verifier
                                    .verify(&tree.export(&cfg), &tree.render(&cfg))
                                    .first()
                                    .map_or(String::new(), |v| format!("{}: {}", v.rule, v.detail))
                            });
                            let verdicts = args.scope.then(|| {
                                let plain = p.tree.export(&cfg);
                                let mut names = BTreeSet::new();
                                names_in(&plain, &mut names);
                                let names: Vec<&str> = names.iter().map(String::as_str).collect();
                                let rules: Vec<Box<dyn gql_proof::refine::Rule>> =
                                    vec![Box::new(Scope::new(&cfg, &names[..names.len().min(32)]))];
                                let automaton = gql_proof::refine::accepts(&rules, &plain).err();
                                let checker = gql_proof::verify::scope::check(&plain)
                                    .first()
                                    .map(|v| format!("{}: {}", v.rule, v.detail));
                                (automaton, checker)
                            });
                            (violation, p.ambiguous, prods, targets, verdicts)
                        });
                        (s.to_string(), covered)
                    },
                )
                .collect()
        });
        let mut c = Covered {
            sentences: distinct.len(),
            unparsed: Vec::new(),
            unverified: Vec::new(),
            ambiguous: 0,
            prods: BTreeSet::new(),
            targets: BTreeSet::new(),
            scope: Vec::new(),
        };
        for (s, p) in parsed {
            match p {
                Err(e) => c.unparsed.push((s, e.to_string())),
                Ok((violation, ambiguous, prods, targets, verdicts)) => {
                    if let Some((automaton, checker)) = verdicts {
                        c.scope.push((s.clone(), automaton, checker));
                    }
                    if let Some(v) = violation {
                        c.unverified.push((s, v));
                    }
                    c.ambiguous += usize::from(ambiguous);
                    c.prods.extend(prods);
                    c.targets.extend(targets);
                }
            }
        }
        writeln!(out, "\n## {}", path.display())?;
        writeln!(
            out,
            "sentences: {} ({} distinct), parsed {}, no iso parse {}, parsed but failing the verifier {}, ambiguous {}",
            sentences.len(),
            c.sentences,
            c.sentences - c.unparsed.len(),
            c.unparsed.len(),
            c.unverified.len(),
            c.ambiguous
        )?;
        write_coverage(&mut out, &cfg, &c.prods, &c.targets, &all_targets)?;
        if args.scope {
            write_scope(&mut out, &c.scope, args.show)?;
        }
        let mut rules: BTreeMap<&str, Vec<(&str, &str)>> = BTreeMap::new();
        for (s, v) in &c.unverified {
            rules
                .entry(v.split(": ").next().unwrap_or(v))
                .or_default()
                .push((s, v));
        }
        if !rules.is_empty() {
            writeln!(out, "failing the verifier, by rule:")?;
            for (rule, ss) in &rules {
                writeln!(
                    out,
                    "  {:>5}  {rule}  e.g. {:?}: {}",
                    ss.len(),
                    ss[0].0,
                    ss[0].1
                )?;
            }
        }
        // Where parsing stopped, grouped by the text just after it.
        let mut stops: BTreeMap<String, Vec<&str>> = BTreeMap::new();
        for (s, e) in &c.unparsed {
            let at = e.split(" | ").nth(1).unwrap_or(e);
            let word: String = at
                .trim_matches('"')
                .split_whitespace()
                .next()
                .unwrap_or("")
                .chars()
                .take(12)
                .collect();
            stops.entry(word).or_default().push(s);
        }
        let mut stops: Vec<_> = stops.into_iter().collect();
        stops.sort_by_key(|(_, v)| std::cmp::Reverse(v.len()));
        if !stops.is_empty() {
            writeln!(out, "no iso parse, by the text where parsing stops:")?;
            for (word, ss) in stops.iter().take(args.show * 2) {
                writeln!(out, "  {:>5}  {word:?}  e.g. {:?}", ss.len(), ss[0])?;
            }
        }
        if args.failures {
            for (s, e) in &c.unparsed {
                writeln!(out, "  {s:?}\n    {e}")?;
            }
        }
        results.push(c);
    }
    if let [a, b] = &results[..] {
        let (na, nb) = (args.files[0].display(), args.files[1].display());
        writeln!(out, "\n## both")?;
        let prods: BTreeSet<u32> = a.prods.union(&b.prods).copied().collect();
        let targets: BTreeSet<Target> = a.targets.union(&b.targets).cloned().collect();
        write_coverage(&mut out, &cfg, &prods, &targets, &all_targets)?;
        for (name, x, y) in [(&na, a, b), (&nb, b, a)] {
            let only_prods: Vec<u32> = x.prods.difference(&y.prods).copied().collect();
            let only: Vec<&Target> = x.targets.difference(&y.targets).collect();
            let cdrc = only
                .iter()
                .filter(|t| matches!(t, Target::Cdrc(..)))
                .count();
            writeln!(
                out,
                "\nonly in {name}: {} productions, {cdrc} cdrc targets, {} k-paths",
                only_prods.len(),
                only.len() - cdrc
            )?;
            for &p in only_prods.iter().take(args.show) {
                writeln!(out, "  {}", describe(&cfg, p))?;
            }
            if only_prods.len() > args.show {
                writeln!(out, "  ...")?;
            }
            for t in only.iter().take(args.show) {
                writeln!(out, "  {}", describe_target(&cfg, t))?;
            }
            if only.len() > args.show {
                writeln!(out, "  ...")?;
            }
        }
    }
    Ok(())
}

/// The automaton against the checker: where the automaton accepts what the checker refuses,
/// one of them is wrong; where only the checker accepts, the automaton forbids more than ISO
/// (its readings).
fn write_scope(
    out: &mut impl Write,
    verdicts: &[(String, Option<String>, Option<String>)],
    show: usize,
) -> io::Result<()> {
    let count = |a: bool, c: bool| {
        verdicts
            .iter()
            .filter(|(_, x, y)| x.is_none() == a && y.is_none() == c)
            .count()
    };
    writeln!(
        out,
        "scoping: both accept {}, both reject {}, only the checker accepts {}, only the automaton accepts {}",
        count(true, true),
        count(false, false),
        count(false, true),
        count(true, false)
    )?;
    let mut unsound: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    let mut strict: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for (s, a, c) in verdicts {
        match (a, c) {
            (None, Some(c)) => unsound
                .entry(c.split(": ").next().unwrap_or(c))
                .or_default()
                .push(s),
            (Some(a), None) => strict.entry(a.as_str()).or_default().push(s),
            _ => {}
        }
    }
    for (title, groups) in [
        ("only the automaton accepts, by the checker's rule", unsound),
        (
            "only the checker accepts, by where the automaton refuses",
            strict,
        ),
    ] {
        if groups.is_empty() {
            continue;
        }
        writeln!(out, "{title}:")?;
        let mut groups: Vec<_> = groups.into_iter().collect();
        groups.sort_by_key(|(_, v)| std::cmp::Reverse(v.len()));
        for (key, ss) in groups.iter().take(show) {
            writeln!(out, "  {:>5}  {key}  e.g. {:?}", ss.len(), ss[0])?;
        }
    }
    Ok(())
}

fn write_coverage(
    out: &mut impl Write,
    cfg: &Cfg,
    prods: &BTreeSet<u32>,
    targets: &BTreeSet<Target>,
    all: &BTreeSet<Target>,
) -> io::Result<()> {
    writeln!(out, "productions: {} of {}", prods.len(), cfg.prods.len())?;
    let cdrc = |t: &&Target| matches!(t, Target::Cdrc(..));
    let hit = targets.intersection(all).collect::<Vec<_>>();
    writeln!(
        out,
        "cdrc: {} of {}",
        hit.iter().filter(|t| cdrc(t)).count(),
        all.iter().filter(cdrc).count()
    )?;
    let mut by_k: BTreeMap<usize, (usize, usize)> = BTreeMap::new();
    for t in all {
        if let Target::Path(p) = t {
            by_k.entry(p.len()).or_default().1 += 1;
        }
    }
    for t in &hit {
        if let Target::Path(p) = t {
            by_k.entry(p.len()).or_default().0 += 1;
        }
    }
    for (k, (h, n)) in by_k {
        writeln!(out, "{k}-paths: {h} of {n}")?;
    }
    Ok(())
}
