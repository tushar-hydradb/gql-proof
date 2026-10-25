# three variables: from stalling to 152 seconds

> for agents: dated working notes, terse on purpose. people start at the [readme](../README.md)

the typed run at 3 variables now finishes, in 152 s with `--parallel`, 6.3 GB
peak. on main (51d059a) it stalled in the ground walks after about 22 minutes
of preamble and never finished (`three-variable-run-2026-10-23.md`). branch
`tushar/three-vars`, worktree `gql-proof-3vars`, commits 30a78e0..2b759d3.
the set is `sentences/typed-3vars-turbolay-claim.jsonl`

```
./target/release/gql-proof context --rule types --slots 3 --join --keys \
  --parallel --phase cover --cdrc --sentences --jsonl --rules all \
  --claim claims/turbolay.claim --match-mode-default different-edges
```

## the numbers

turbolay claim, `--match-mode-default different-edges`, this machine (15
cores, 24 GB), wall time:

| phase | 2 vars, main | 2 vars, now | 3 vars, main | 3 vars, now |
|---|---|---|---|---|
| fixed point | ~40 s | 6.5 s | ~5 min | 71 s |
| layers | 27 s | 4 s | 214 s | 30 s |
| closure | 135 s | 0.7 s | ~14 min | 3 s |
| ground walks | 319 s | ~8 s | stalled | ~45 s |
| total | 526 s | 19 s | did not finish | 152 s |
| peak | 1.4 GB | 2.0 GB | | 6.3 GB |

coverage at 3 variables: 4,399 of 4,540 productions (141 never), 6,634 of
6,941 cdrc pairs (305 never): the counts `never-targets-2026-10-23.md`
predicted from the 2 variable audit. 2 variables: 4,387 (153 never, one more
covered than main) and 6,606 (333 never). the never lists with and without
`--parallel` are identical at 1, 2 and 3 variables

## what was wrong, not just slow

three completeness bugs, each one able to turn a target with a tree into a
false never. found while making the walks cheaper, because a sound shortcut
changed what came out

- **the closure took ends by equality** (`reach` in `extract.rs`): an option
  was reached when its instance's end had a reached live label, but a ground
  of a joined option can finish within a reached label its own end is not
  (joins group labels apart from how ends fall). `up` trusts the closure as a
  necessary condition, so it refused real contexts; cdrc searches went
  through `under` directly and hid it. now an end is taken when it overlaps a
  reached label (`Context::overlaps`, types: alike and every variable's sets
  meet). lost `RETURN SESSION_USER AS x NEXT ORDER BY x || x FINISH` at 1 slot
  once the cdrc search asked `up` first
- **conditional failures settled early** (`Extractor::search`): a search that
  failed conditionally left its own dependents at its depth, and the next
  search to fail for good at that depth settled them as never. they now move
  to the search their parent depends on. the audit had flagged this as a
  concern
- **the walk's failure memo was keyed by the partial label only**
  (`ground_from`): a failure caused by an earlier child without a witness was
  recorded against the partial label, and another prefix reaching it was cut.
  a failure is now recorded only when no child before the position failed
  (`Walk::taint`). trees got smaller with it (`FILTER LIST [ x ] IS NULL`
  where a nested CAST stood before)

## what made it fast

in the order they landed, each checked for the same sentences (or the same
coverage and never lists where a tie breaks differently):

- **the wide walks only over options that can matter**
  (`Engine::graph_useful`): a ground tree within label `g` comes from a joined
  instance whose end holds it, so a witness walk goes wide only over the
  options of instances that end within `g`; a context walk only over those of
  instances that end in a label the closure reached (once per production).
  the 2 variable never target `LET` rep2 went from 163 s and 78 million
  candidates to 4 s and 16 thousand; the 3 variable stall was the same kind
  of proof of never
- **the layers' steps kept as a graph** (`Engine::layers_graph`, `Graph`):
  building the layers pushes every partial label with every option; those
  steps are kept (16 bytes each, 131 million at 3 variables) and every
  backward pass reads them instead of pushing again: the closure's passes
  (`graph_cheapest_ends`), the ahead tables (`graph_ahead`), the useful
  options. closure 137 s to 0.8 s at 2 variables. checked against the push
  versions on every production at 1 slot before those were deleted
- **the layers in parallel** (`Scan`, a read-only view of the engine; stats
  per thread, `Stats::absorb`). `Context` and `Under` are `Sync` now
- **labels inline** (`smallvec`): scope's and the types rule's variables, the
  kids, scope's drafts and meeting targets. a label is cloned on every push
- **the fixed point's rounds in parallel** (`--parallel`,
  `Engine::round_parallel`): each round's scans read the labels as the round
  began, what they found is added after in production order. deterministic,
  but not the sequential order: joins depend on the order labels arrive, so
  live labels can be grouped differently and the trees differ, the coverage
  not. off by default so the existing sets reproduce
- **a scan's pushes split** (`Scan::steps_from`): a batch of 128 partial
  labels at a time over rayon's pool, applied in order. the scans run on
  plain threads, one per core, largest first (`map_ordered`): a rayon thread
  waiting for its pushes takes up another whole scan and nests it on its
  stack, which overflowed (and peaked at 13 GB before that)
- smaller: cdrc targets try each child label once and ask `up` first; wide
  candidates built once per walk position; per-definition stats without an
  allocation per push; scope's `combine` reads the node name once; the
  closure's passes are one backward product, not two

## what is left

- **memory**: 6.3 GB peak at 3 variables, about a third of it the steps.
  dropping a production's steps once nothing will ask for them, or keeping
  them only for productions a walk visits, would cut it. 4 variables is not
  tried and would not fit as is
- **the fixed point**: 71 s at 3 variables, now bound by its largest scans
  (`<simple case/rep1>`, `<comparison predicate>`, `<simple case>`). a scan's
  partial labels are cloned into `old`/`fresh` each round; borrowing them
  would cut allocation further
- **`--parallel` as the default**: the never lists match at 1 to 3 variables;
  flipping it changes the committed sets' trees, so it waits for a decision
- **the reachability necessary condition** is now overlap, which reaches more
  labels than before (101,193 live labels at 3 variables). still exact for
  existence; the walks pay for the extra labels only where they look
- **the production targets** after cdrc are not measured separately; they
  were never slow

## what not to redo

- the gates: `cargo test --release` (5 minutes) and the ignored
  `extraction_matches_emission` and `joined_grounds_are_exact` (about a
  minute and a half now), all passing at 2b759d3
- compare a change by the sentences at 1 slot (`cmp` on the jsonl, 4 s) and
  by coverage and never lists (`--top 100000`) at 2 variables (19 s) before 3
- `GQL_CHECK_REACHED=1` checks every extracted tree against the closure
  (`check_reached`), `GQL_DEBUG_REACHED=<nt>` prints what the closure missed
  for one nonterminal; the slow target lines name the productions a target's
  walks spent in
