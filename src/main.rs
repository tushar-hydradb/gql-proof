use anyhow::Result;
use clap::{Parser, Subcommand, ValueEnum};
use gql_proof::cfg::Cfg;
use gql_proof::leaf::StubProvider;
use gql_proof::purdom::{Config, Generator, Reason};
use gql_proof::{ISO_BNF_XML, bnf, describe};
use std::collections::BTreeMap;
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
}

#[derive(Parser)]
struct PurdomArgs {
    /// Breaks ties between equally cheap choices. Same seed, same trees.
    #[arg(long, default_value_t = 0)]
    seed: u64,
    /// Maximum tree height. Productions that need more are reported, not dropped.
    #[arg(long, default_value_t = 50)]
    max_depth: u32,
    /// Start symbol.
    #[arg(long, default_value = "GQL-program")]
    start: String,
    /// Print only this tree (1-based). The summary still covers the whole set.
    #[arg(long)]
    tree: Option<usize>,
    #[arg(long, value_enum, default_value_t = Format::Both)]
    format: Format,
    /// Stop chasing new productions in a tree after this many, for smaller trees.
    #[arg(long)]
    max_new_per_tree: Option<usize>,
    /// Show lexical rules (identifiers, literals, ...) down to single characters.
    #[arg(long)]
    expand_lexical: bool,
    /// Print the coverage summary after the trees.
    #[arg(long)]
    summary: bool,
    /// Grammar XML. Defaults to the vendored ISO file.
    #[arg(long)]
    grammar: Option<PathBuf>,
}

#[derive(Clone, Copy, PartialEq, Eq, ValueEnum)]
enum Format {
    Tree,
    Sentence,
    Both,
    /// Only the coverage summary, same as `--summary` with no trees.
    Summary,
    /// One JSON object per tree (`tree`, `height`, `new`, `sentence`), no summary. Sentences
    /// can contain newlines from comments and whitespace, so this is the format for tooling.
    Jsonl,
}

fn main() -> Result<()> {
    let result = match Cli::parse().cmd {
        Cmd::Purdom(args) => purdom(args),
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

fn purdom(args: PurdomArgs) -> Result<()> {
    let xml = match &args.grammar {
        Some(path) => std::fs::read_to_string(path)?,
        None => ISO_BNF_XML.to_string(),
    };
    let cfg = Cfg::from_bnf(&bnf::parse(&xml)?);
    let start = cfg.require(&args.start)?;
    let config = Config {
        seed: args.seed,
        max_depth: args.max_depth,
        max_new_per_tree: args.max_new_per_tree,
    };
    let outcome = Generator::new(&cfg, config, StubProvider).run(start)?;
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
                "height": root.height(),
                "new": generated.new,
                "sentence": root.render(&cfg),
            });
            writeln!(out, "{record}")?;
            continue;
        }
        writeln!(
            out,
            "# tree {n}: height {}, {} new productions",
            root.height(),
            generated.new
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
    let total = cfg.prods.len();
    let covered = outcome.covered.count_ones(..);
    writeln!(out, "# summary")?;
    writeln!(
        out,
        "seed {}, max depth {}, start <{}>",
        args.seed, args.max_depth, args.start
    )?;
    writeln!(out, "trees: {}", outcome.trees.len())?;
    writeln!(
        out,
        "productions covered: {covered} of {total} (desugared: every [..] both ways, every ... once and repeated)"
    )?;

    let mut by_reason: BTreeMap<&str, Vec<String>> = BTreeMap::new();
    for &(p, reason) in &outcome.uncovered {
        let (key, line) = match reason {
            Reason::Unreachable => ("unreachable from start", describe(&cfg, p)),
            Reason::Unproductive => ("no finite derivation", describe(&cfg, p)),
            Reason::NeedsDepth(d) => (
                "needs a deeper tree",
                format!("{} (depth {d})", describe(&cfg, p)),
            ),
        };
        by_reason.entry(key).or_default().push(line);
    }
    for (reason, lines) in by_reason {
        writeln!(out, "{reason}: {}", lines.len())?;
        // Unreachable productions are mostly the lexical layer (whitespace, comments), which
        // is reachable from <token> instead. Group those by ISO definition to keep it short.
        if reason == "unreachable from start" {
            let mut defs: BTreeMap<String, usize> = BTreeMap::new();
            for &(p, r) in &outcome.uncovered {
                if r == Reason::Unreachable {
                    let origin = &cfg.nts[cfg.prod(p).lhs as usize].origin;
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
    Ok(())
}
