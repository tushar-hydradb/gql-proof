# follow-ups after the two-variable typed sets

> for agents: dated working notes, terse on purpose. people start at the [readme](../README.md)

where the branch `tushar/prune` stands on 2026-10-22, evening, and what is
queued, in the order i would take it. numbers and reasons are in
`research/pruning-2026-10-22.md`; the proof's shape in `algorithm.md`

## ready to run

- **run the typed set on turbolay**: `just turbolay-typed <worktree>` (the
  recipe generates the set again, about 10 minutes; or point the probe at
  `target/engines/turbolay-typed-sentences.jsonl`, the 2,274 passing
  sentences, with `GQL_PROOF_IN`). the claim names turbolay#243 at cb5c5b06;
  `/Users/tushar/code/turbolay-gql-243` is the checkout to confirm against
  it. the crate needs `serde_json = { workspace = true }` under
  `[dev-dependencies]` of `crates/cypher-engine`. then
  `tools/engines/report.py` on the results, beside the purdom short-sentence
  run of 2026-10-21 (`target/engines/turbolay-results.jsonl`): what the
  typed set adds is sentences the engine must accept, so every refusal is
  either an engine bug or a reading of ours to look at. 26 sentences carry a
  newline inside a byte string literal's separator (`X'' \n ''`), which the
  grammar allows; check the engine's lexer takes it

## readings to settle against the text

- **`x + NULL` as an exact number** (4 sentences left out of the set): the
  rule reads 21.2 SR 67 a as a null operand taking its type from its context,
  so `COUNT(*) + NULL` is exact and `TRIM(NULL, x + NULL)` fits 20.16 SR 1;
  the checker types it as a numeric of unknown exactness and refuses. if the
  checker is right, `arithmetic` in `src/context/types.rs` loses exactness
  when an operand is null (a narrowing: `1 + NULL` would no longer serve as a
  list index or a TRIM count)
- **DELETE of a value variable defined by another variable** (`MATCH (x) LET
  y = x DELETE y`): refused by the typed rule because a value variable
  defined by a reference is opaque (a documented narrowing). widening it
  means following a bare reference's class into the definition, which the
  types label has room for (`Has(c)` already carries exact, string, bool,
  dynamic)
- **lists never combine** (20.17 SR 3): the fix follows the rule's own
  reading (elements are not followed), so `[ [1], [2] ]` is now refused too.
  following one level of element class (`ListOf(Class)`) would widen it back;
  only worth it if an engine run shows lists of lists matter

## the gate for three variables

- **the reachability closure** is the largest piece at two variables (about
  170 s of 548 s on the ISO grammar, 190 s under the claim) and scaled 33x
  from one variable against 3.6x labels. it repeats whole backward passes
  when the pending table refills. a worklist keyed by the labels that
  changed, as the fixed point's semi-naive rounds already do, is the one
  change to make before trying `--slots 3` at all
- **then parallel**: the ahead tables (25 s, one per production, independent),
  the per-target searches (independent given the memo tables, which would
  need to be shared or sharded), and the fixed point's rounds (independent
  per production within a round). tushar's order: reduce the work first,
  which the two items above are, then this
- **measure three variables**: `--rule types --slots 3 --join --keys --phase
  cover --cdrc --sentences --jsonl --rules all --claim claims/turbolay.claim`.
  the fixed point alone was 572 s on the ISO grammar before joins; memory at
  two variables under the claim is 1.25 GB, so expect several GB. run with a
  deadline and the progress lines, never blind
- **equality groups** (the plan at `~/.claude/plans/indexed-cuddling-ember.md`,
  steps 1-4): shrink the fixed point by making `x = y` one label instead of
  one per class. only if the three-variable measurement says the label
  count, not the closure, is what hurts. the phantom-grounds theory behind
  the original design was wrong at one variable (`joined_grounds_are_exact`)

## exactness tests still owed

- **extraction against emission at two variables** (plan step 6): the
  equivalence tests run at scope caps 1-3 and typed at one variable; a
  two-variable ignored test from the same joined fixed point is feasible
  (emission is about five fixed points)
- **extraction under a refined grammar**: `extraction_matches_emission` runs
  on the ISO grammar only. the refined grammar found two extraction bugs on
  its first run (shared occurrence ids, refined against ISO target ids); a
  claim-refined variant of the test at one variable would have caught both
- **purdom's own target bookkeeping**: `coverage::targets` returns refined
  production ids and `observe` ISO ones. the extractor now uses
  `observe_refined`; check whether purdom's cdrc skip logic compares the two
  the same way, which would make it regenerate for targets it already covers
- **lexical productions**: 10 productions (quoted character sequences) are
  extracted for and then spelled away by templates, so no tree uses them.
  either `Criteria.lexical` covers them with real spellings or the tally
  keeps naming them, as it does now

## coverage criteria

- **k-paths** (`--k 3`): cdrc covers a production at each parent occurrence,
  one level. the combinations tushar's question touched (a MATCH directly
  under the bare-procedure alternative, an ambient statement under NEXT) are
  3-paths. `coverage::targets` already lists them; the extractor's `cover`
  has no arm for `Target::Path` yet. a path target is a chain of contexts,
  which `under` composes already, so the arm is a loop over the chain

## housekeeping

- remove `emit` and `generate` from the typed path once extraction is the
  only producer (plan step 8); `--phase emit` stays for the equivalence tests
- the `--rules` default on `context` is `none` to keep the measurements
  comparable; for any engine run it should be `all`. flip the default once
  the research numbers are re-taken under it
- merge `tushar/prune` into `main` when the turbolay run has been read: the
  branch is 12 commits ahead and main has not moved since the merge
- `research/pruning-2026-10-22.md` has grown into a log; the write-up tushar
  wants (checker catches rule: TRIM, DELETE, byte trims, lists, in one
  story) can draw on it and `research/checker-catches-rule-2026-10-22.md`
