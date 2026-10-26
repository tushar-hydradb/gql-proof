# cached sentence sets

> for agents: which cached set is which and how each was made. people start at the [readme](../README.md)

generated sentences, kept in the repo because the typed runs take minutes (two
variables is about 11). run engines and detectors against these instead of
regenerating; regenerate when the generator changes what it should produce

each file is jsonl, one object per line with at least a `sentence` field
(newlines inside a sentence are kept, a byte string continued across lines
needs them). the engine runners (`tools/engines/neo4j.py`, the turbolay probe)
and `tools/inventory/violations.py` read them as they are

## the sets

- `typed-2vars-turbolay-claim.jsonl`: types under scope, 2 variables, extracted
  per target from the claim refined grammar for `claims/turbolay.claim`. 2,278
  rows, 2,243 distinct, each with the `target` it covers. made on
  `tushar/prune` at 258437a (2026-10-22), the `.all` variant (4 more list TRIM
  sentences than the default). on turbolay #243 (484d1a72): 1,174 accepted,
  breakdown in the linear doc of query problems
- `typed-2vars-turbolay-claim-exists-table.jsonl`: the same command on
  `tushar/exists-table` (2026-10-22), after 19.4 SR 5, 20.6 SR 3, 8 and 10,
  11.2 SR 2 (an EXISTS, VALUE or nested table body has a binding table type,
  not FINISH's empty type; a VALUE body one column and one row). 2,278 rows,
  2,243 distinct, 547 s, 1.27 GB; the same 2,026 cdrc targets as its
  predecessor plus the nested-query EXISTS one, none lost. the 306 `EXISTS {
  FINISH }` witnesses became `EXISTS { <- }` (graph pattern form, implicit
  nodes by 16.7 SR 14), `VALUE { FINISH }` became `VALUE { RETURN COUNT(*) AS
  x }`. turbolay #243 (484d1a72) results in
  `research/static-semantics-exists-table-2026-10-22.md`
- `typed-2vars-turbolay-claim-last-ten.jsonl`: the same command on
  `tushar/exists-table` (2026-10-23, 32d38c9), after the last four classes
  turbolay refused as ours: bounds ordered at spelling time (16.11 SR 3 a ii,
  `tree::order_bounds`, run by both generators), TRIM's FROM (20.24 SR 3) and
  empty delimited identifiers (21.3 SR 4) as automata, a property of NULL or
  of a record refused by `types.rs`. 3,834 rows, 3,800 distinct, 485 s,
  1.38 GB, the never-covered counts unchanged at 153 and 333; 4 trees flagged
  by the types checker only (`x + NULL` as a TRIM count). turbolay #243
  (484d1a72) results in `research/static-semantics-last-ten-2026-10-23.md`
- `typed-2vars-turbolay-claim-path-minimums.jsonl`: the turbolay command with
  `--match-mode-default different-edges` (turbolay's ID086, now in the recipe)
  on `tushar/exists-table` (2026-10-23), after the path pattern minimums (16.7
  SR 8, 9, 16, 20, 16.12 SR 1-4, 16.4 SR 12) as automata in `src/refine.rs`.
  3,843 rows, 3,808 distinct, 559 s, 1.57 GB: more rows because the automata's
  copies are targets of their own (4,545 productions and 6,942 cdrc pairs to
  cover, were 2,990 and 4,943), the never-covered counts unchanged at 153 and
  333. turbolay #243 (484d1a72) results in
  `research/static-semantics-path-minimums-2026-10-23.md`
- `typed-3vars-turbolay-claim.jsonl`: the typed command (`--match-mode-default
  different-edges --claim claims/turbolay.claim --slots 3`) on `tushar/soundness`
  after the fourteenth review (2026-10-26), the claim's gate in force: 3,473 rows,
  150 productions and 322 cdrc pairs never, 136 withheld, all gate-only, 0 on a
  rule the generator keeps. it replaces main's first three variable set (2b759d3,
  3,857 rows, before the soundness work; about 100 of its sentences fail today's
  checker). how the run got from stalling to fast:
  `research/three-variables-fast-2026-10-25.md`. a third variable adds few
  sentences: the cover targets are met at one or two (`research/soundness-claim.md`)
- `typed-2vars-whole-grammar-before-258437a.jsonl`: types under scope, 2
  variables, whole grammar (no claim), before extraction took the smallest
  context first. 1,228 distinct, each with the `targets` it covers. kept for
  the record in `research/static-semantics-inventory-2026-10-22.md`: it holds
  the 17 use after delete sentences the later list lost by witness choice. its
  successor (1,310 sentences, after 258437a) was not kept
- `typed-2vars-turbolay-claim-soundness.jsonl`, `typed-2vars-whole-grammar-soundness.jsonl`:
  the typed command (`--match-mode-default different-edges`) on `tushar/soundness`
  (2026-10-24), the claim's gate in force (`research/soundness-claim.md`): every
  printed tree passed the syntax, scope and types checkers. after the fourteenth review
  (2026-10-25): turbolay claim 3,465 rows, 160 and 347 never, 124 withheld; whole
  grammar 3,068 rows, 38 and 94 never, 514 withheld (graph type bodies and the
  per-tree category sites, see research/soundness-2026-10-23.md), all on gate-only
  rules, 0 on a rule the generator keeps. no SELECT
  with a FROM and no `$$` are generated (readings, `research/soundness-claim.md`)
- `typed-2vars-whole-grammar-51d059a.jsonl`: the typed command with no `--claim`
  (every feature) and `--deadline 3600`, on main at 51d059a (2026-10-23, before
  the soundness work): 3,508 rows, 3,443 distinct, 437 s; 4,442 of 4,473
  productions and 6,474 of 6,540 cdrc pairs covered, 0 checker failures. kept
  as the record of what the whole grammar reached before the soundness track:
  `violations.py` finds 18.9 SR 7/10/29 (3), 8.2 SR 2 (3), 22.1 SR 3 (8) and
  14.12 SR 7 (32) in it, and a text check finds 18.2 SR 2 / 18.3 SR 2 (closed
  node and edge types with names or key label sets) and 20.9 SR 3 (169
  aggregates over a subquery)
- `scope-turbolay-claim.jsonl`, `scope-neo4j-claim.jsonl`: scope only, `purdom
  --short --claim claims/<engine>.claim --format jsonl`, 3 variables,
  regenerated on `tushar/soundness` (2026-10-24): turbolay 778, neo4j 448 (on
  main at 51d059a: 785 and 463). the earlier copies (2026-10-21, main around 3e12b6c: 790
  and 481 sentences, turbolay accepting 295, neo4j 92) predated the exists,
  path and last ten work

## adding one

name it `<rule>-<cap>-<grammar or claim>.jsonl`, keep the generator's own
fields (`target`, `height`, `tree`), and add a line here with the command, the
commit, the date, the counts and what it was run against
