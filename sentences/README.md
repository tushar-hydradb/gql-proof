# cached sentence sets

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
  `tushar/prune` at ef00fdb (2026-10-22), the `.all` variant (4 more list TRIM
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
- `typed-2vars-whole-grammar-before-ef00fdb.jsonl`: types under scope, 2
  variables, whole grammar (no claim), before extraction took the smallest
  context first. 1,228 distinct, each with the `targets` it covers. kept for
  the record in `research/static-semantics-inventory-2026-10-22.md`: it holds
  the 17 use after delete sentences the later list lost by witness choice. its
  successor (1,310 sentences, after ef00fdb) was not kept
- `scope-turbolay-claim.jsonl`, `scope-neo4j-claim.jsonl`: scope only, `purdom
  --short --claim claims/<engine>.claim --format jsonl`, 3 variables, from
  2026-10-21 (main around f3f9269). on turbolay 295 of 790 accepted, on neo4j
  92 of 481

## adding one

name it `<rule>-<cap>-<grammar or claim>.jsonl`, keep the generator's own
fields (`target`, `height`, `tree`), and add a line here with the command, the
commit, the date, the counts and what it was run against
