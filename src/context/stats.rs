//! What a run of the context engine spent, and where: per production, per rule definition,
//! per round of the fixed point, per nonterminal, and in emission. Filled by the engine as it
//! goes (no global state), summarized on stderr and written as json for sweeps.

use serde::Serialize;
use std::collections::BTreeMap;
use std::fmt::Write;

/// One production's share.
#[derive(Debug, Clone, Default, Serialize)]
pub struct ProdStats {
    pub describe: String,
    /// Times its partial labels were built (fixed point scans and emission).
    pub scans: u64,
    pub nanos: u64,
    /// Partial labels after a position: the most at any position of any scan, and in all.
    pub partials_max: usize,
    pub partials_total: u64,
    /// Calls to the rule's `push` for it, and the partial labels they gave.
    pub pushes: u64,
    pub pushed: u64,
}

/// One rule definition's share (`node.def`, a desugaring group included).
#[derive(Debug, Clone, Default, Serialize)]
pub struct DefStats {
    pub pushes: u64,
    pub pushed: u64,
    pub push_nanos: u64,
    pub finishes: u64,
    pub finished: u64,
    pub finish_nanos: u64,
}

/// One round of the fixed point.
#[derive(Debug, Clone, Default, Serialize)]
pub struct RoundStats {
    pub round: u32,
    /// Productions scanned, and the labels that were new after it.
    pub scanned: usize,
    pub new_labels: usize,
    pub labels: usize,
    pub nanos: u64,
}

/// One production's share of emission.
#[derive(Debug, Clone, Default, Serialize)]
pub struct EmitProd {
    pub describe: String,
    /// Labels of its left hand side it was expanded for.
    pub expansions: u64,
    /// Backward passes run for it, and the `push` calls those passes made.
    pub backward_runs: u64,
    pub pushes: u64,
    /// Instances emitted for it.
    pub emitted: u64,
    pub nanos: u64,
    /// Options at its positions (labels of each child), the most at one position.
    pub options_max: usize,
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct EmitStats {
    pub prods: BTreeMap<u32, EmitProd>,
    /// Labels reachable from the start, each expanded once.
    pub expanded: u64,
    pub productions: u64,
    /// Backward passes for options no instance took yet, run and skipped (all taken).
    pub backward_runs: u64,
    pub backward_skipped: u64,
    /// Passes against one reached label, for options whose smallest instance gives a label
    /// never reached (single pass emission).
    pub fallback_runs: u64,
    /// Instances the fallback passes emitted.
    pub fallback_emitted: u64,
    /// With joins: instances made ground with their own options, with any option (wide),
    /// not at all, and the time those searches took.
    pub ground_narrow: u64,
    pub ground_wide: u64,
    pub ground_failed: u64,
    pub ground_nanos: u64,
    /// Inside the ground walks: candidates tried at a position, candidates refused for
    /// having no witness (`child_ok`), finished labels refused by `accept`.
    pub ground_candidates: u64,
    pub ground_child_rejected: u64,
    pub ground_accept_rejected: u64,
    /// Partial labels cut for already asking more than the target (`Context::narrower`).
    pub ground_narrowed: u64,
    /// Per production walked: its walks and the candidates they tried themselves (not in
    /// the searches they started), for finding where the searches spend.
    pub ground_by_prod: BTreeMap<u32, GroundProd>,
    /// Backward passes for the options a wide walk needs (`Engine::graph_useful`).
    pub useful_runs: u64,
    pub useful_nanos: u64,
    pub nanos: u64,
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct GroundProd {
    pub narrow: u64,
    pub wide: u64,
    pub candidates: u64,
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct Stats {
    pub prods: BTreeMap<u32, ProdStats>,
    pub defs: BTreeMap<String, DefStats>,
    pub rounds: Vec<RoundStats>,
    /// Labels per nonterminal at the fixed point.
    pub labels: BTreeMap<String, usize>,
    pub emit: EmitStats,
    /// Labels made smaller by dropping facts nothing above reads, and labels rejected because
    /// they hold one that dooms them (see `live`).
    pub projected: u64,
    pub doomed: u64,
    /// Labels a join absorbed (`Options::join`).
    pub joined: u64,
    /// Pairs not pushed because their keys rule them out (`Options::keys`).
    pub skipped: u64,
    /// Wall time per phase, in nanoseconds.
    pub phases: BTreeMap<String, u64>,
}

fn ms(nanos: u64) -> f64 {
    nanos as f64 / 1e6
}

impl Stats {
    pub fn total_labels(&self) -> usize {
        self.labels.values().sum()
    }

    pub fn pushes(&self) -> u64 {
        self.defs.values().map(|d| d.pushes).sum()
    }

    pub fn partials_max(&self) -> usize {
        self.prods
            .values()
            .map(|p| p.partials_max)
            .max()
            .unwrap_or(0)
    }

    /// The summary printed after a run: phases, rounds, and the top `top` of each table.
    pub fn summary(&self, top: usize) -> String {
        let mut s = String::new();
        let _ = writeln!(s, "phases:");
        for (phase, nanos) in &self.phases {
            let _ = writeln!(s, "  {phase:<10} {:>10.1} ms", ms(*nanos));
        }
        let _ = writeln!(
            s,
            "labels {}, pushes {}, partials at most {} at one position, {} labels projected, {} doomed, {} joined, {} pairs skipped by keys",
            self.total_labels(),
            self.pushes(),
            self.partials_max(),
            self.projected,
            self.doomed,
            self.joined,
            self.skipped
        );
        if !self.rounds.is_empty() {
            let _ = writeln!(s, "rounds: round  scanned  new labels  labels  ms");
            for r in &self.rounds {
                let _ = writeln!(
                    s,
                    "  {:>5} {:>8} {:>11} {:>7} {:>9.1}",
                    r.round,
                    r.scanned,
                    r.new_labels,
                    r.labels,
                    ms(r.nanos)
                );
            }
        }
        let mut prods: Vec<&ProdStats> = self.prods.values().collect();
        prods.sort_by_key(|p| std::cmp::Reverse(p.nanos));
        let _ = writeln!(
            s,
            "productions by time: ms  scans  partials max/total  pushes -> pushed"
        );
        for p in prods.iter().take(top) {
            let _ = writeln!(
                s,
                "  {:>9.1} {:>6} {:>7}/{:<9} {:>9} -> {:<9} {}",
                ms(p.nanos),
                p.scans,
                p.partials_max,
                p.partials_total,
                p.pushes,
                p.pushed,
                p.describe
            );
        }
        let mut defs: Vec<(&String, &DefStats)> = self.defs.iter().collect();
        defs.sort_by_key(|(_, d)| std::cmp::Reverse(d.push_nanos + d.finish_nanos));
        let _ = writeln!(
            s,
            "definitions by time: ms  pushes -> pushed (fan-out)  finishes -> finished"
        );
        for (def, d) in defs.iter().take(top) {
            let fan = |n: u64, out: u64| if n == 0 { 0.0 } else { out as f64 / n as f64 };
            let _ = writeln!(
                s,
                "  {:>9.1} {:>9} -> {:<9} ({:>5.2}) {:>9} -> {:<9} <{def}>",
                ms(d.push_nanos + d.finish_nanos),
                d.pushes,
                d.pushed,
                fan(d.pushes, d.pushed),
                d.finishes,
                d.finished,
            );
        }
        let mut nts: Vec<(&String, &usize)> = self.labels.iter().collect();
        nts.sort_by_key(|(_, n)| std::cmp::Reverse(**n));
        let _ = writeln!(s, "nonterminals by labels:");
        for (nt, n) in nts.iter().take(top) {
            let _ = writeln!(s, "  {n:>7}  <{nt}>");
        }
        if self.emit.expanded > 0 {
            let mut prods: Vec<&EmitProd> = self.emit.prods.values().collect();
            prods.sort_by_key(|p| std::cmp::Reverse(p.nanos));
            let _ = writeln!(
                s,
                "emission by production: ms  expansions  backward passes  pushes  emitted  options max"
            );
            for p in prods.iter().take(top) {
                let _ = writeln!(
                    s,
                    "  {:>9.1} {:>10} {:>9} {:>12} {:>8} {:>7}  {}",
                    ms(p.nanos),
                    p.expansions,
                    p.backward_runs,
                    p.pushes,
                    p.emitted,
                    p.options_max,
                    p.describe
                );
            }
            let e = &self.emit;
            let _ = writeln!(
                s,
                "emission: {} labels expanded, {} productions, backward passes {} run / {} skipped / {} fallback ({} emitted), {:.1} ms",
                e.expanded,
                e.productions,
                e.backward_runs,
                e.backward_skipped,
                e.fallback_runs,
                e.fallback_emitted,
                ms(e.nanos)
            );
            if e.ground_narrow + e.ground_wide + e.ground_failed > 0 {
                let _ = writeln!(
                    s,
                    "ground instances: {} from their own options, {} wide, {} failed, {:.1} ms",
                    e.ground_narrow,
                    e.ground_wide,
                    e.ground_failed,
                    ms(e.ground_nanos)
                );
            }
        }
        s
    }
}
