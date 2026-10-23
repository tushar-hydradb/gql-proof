# static semantics: handoff

> for agents: dated working notes, terse on purpose. people start at the [readme](../README.md)

for the agent picking up static semantics. what is known, where it lives, how to
measure, and the order to close the gaps in. the progress summary for people is
`research/progress-2026-10-22.md`; the three variable work (performance) is
`research/follow-ups-2026-10-22.md` and is a separate track

## where things are

- the inventory: `research/static-semantics-inventory-2026-10-22.md` (the
  argument and the counts) and `research/static-inventory-2026-10-22.jsonl`
  (every syntax rule: clause, rule number, kind, status, file:line evidence, a
  note in our words). made by `tools/inventory/` from the standard's extracted
  text, which stays out of the repo (`just iso-text` writes it to the
  gitignored `iso-text/` from your pdf)
- the detectors: `tools/inventory/violations.py <sentences...>` finds concrete
  violations of not enforced rules in a sentence set (text level, so lower
  bounds), plus use after delete (dynamic, 22G11)
- the engine breakdown: `tools/engines/breakdown.py <results.jsonl>` sorts an
  engine run into ours, engine deviation, engine parse gap, dynamic, environment
  and reported bugs. its rules match turbolay's messages at #243 (484d1a72)
- cached sentences: `sentences/` (see its README). run against these, don't
  regenerate unless the generator changed
- the rules live in: `src/context/scope.rs` (scope, the label and its flags),
  `src/context/types.rs` (types under scope), `src/refine.rs` (syntax rules
  compiled into the grammar as tree automata, e.g. 16.4 SR 6 and 14),
  `src/leaf.rs` (spelling of names and literals), `src/tokens.rs` (token
  boundaries). the independent checkers: `src/verify.rs`, `src/verify/scope.rs`,
  `src/verify/types.rs`

## the numbers to beat

the inventory: 1,025 syntax rules; 426 constraint and type rules, of which 249
enforced as written, 91 by a stricter reading, 6 checked only, 80 not enforced;
66 catalog rules open as a group

turbolay #243 (484d1a72) on `sentences/typed-2vars-turbolay-claim.jsonl`, from
`breakdown.py`:

```
2,243 distinct
1,174  52.3%  accepted
  488  21.8%  ours: invalid sentence
                250  19.4 SR 5    EXISTS body is FINISH (empty type)
                189  16.7 SR 16   path pattern with no node (MATCH <- ?)
                 26  16.12        quantifier or ? in a simplified pattern
                  9  16.7 SR 8    quantified or questioned primary of length 0
                  6  16.7 SR 20   subpath with no node
                  3  20.24 SR 3   TRIM with a bare FROM
                  2  16.4 SR 12   selective pattern not alone (DIFFERENT EDGES)
                  2  21.3 SR 4    empty identifier in a parameter ($@"")
                  1  20.11        property of NULL
  282  12.6%  engine parse gap (typed VALUE 242, KEEP inside EXISTS 40)
  248  11.1%  engine documented deviation
   19   0.8%  data exception raised as it should
   17   0.8%  no parameters passed by the runner
   15   0.7%  engine bugs already reported
```

the goal for this track is the 488 to 0, and `violations.py` clean on every
cached set, without losing a production or cdrc pair

## how to measure a change

1. `cargo test --release --test context_types` (probes, generated trees against
   both checkers) and the exactness tests if the label changed
   (`pruning_is_exact`, see `research/pruning-2026-10-22.md`)
2. regenerate the typed set, about 11 minutes, with a deadline and progress,
   never blind: `gql-proof context --rule types --slots 2 --join --keys --phase
   cover --cdrc --sentences --jsonl --rules all --claim claims/turbolay.claim`
   (or `just turbolay-typed <worktree>`). save it in `sentences/` with a README
   line; don't leave it in a worktree's `target/`, a removed worktree takes it
   along
3. `tools/inventory/violations.py` on it: the class you closed should be 0
4. run turbolay: the probe in `~/code/turbolay-gql-243` (needs `serde_json` in
   the cypher-engine dev-dependencies), `GQL_PROOF_IN=<set>
   GQL_PROOF_OUT=<results> cargo test --release -q -p hydradb-cypher-engine
   --test zz_gql_proof`, then `breakdown.py`
5. coverage must not drop: productions and cdrc pairs before and after (the
   cover phase prints them)

## the order, and how each closes

1. **statement composition** (about 250 of the 488, and the most reachable
   family in the inventory). rules: 19.4 SR 5, 20.6 SR 5, 6, 8, 10, 11.2 SR 2,
   9.1 SR 5 to 7, 9.2 SR 4 to 7, 12.8 SR 2, 13.6 SR 2, 14.2 SR 3, 4, 14.5 SR 2,
   14.12 SR 26. two synthesized facts in scope's label: the result shape a
   subtree yields (a table, one value, nothing) and the statement kind (query,
   data modifying, catalog), checked where a body is used (EXISTS, VALUE, CALL,
   a NEXT boundary, a composite query's operands). scope's flags (`gf` in
   `scope.rs`) already carry RESULT, FINISHED, CLOSES and NEEDS_TABLE, which
   9.2 SR 7 partly rides on: read those before adding. a witness stays for each
   target: `EXISTS { MATCH (x) RETURN x }` covers what `EXISTS { FINISH }` did.
   **done on `tushar/exists-table` (2026-10-22) for the result shape**: 19.4
   SR 5, 20.6 SR 3, 8 and 10 (by reading: the aggregate way, not LIMIT 1),
   11.2 SR 2, by `FINISHED` meaning "the empty type" and `ONE_ROW` surviving
   to the consumers; see
   `research/static-semantics-exists-table-2026-10-22.md`. the statement kind
   (9.1 SR 5 to 7 and the rest) is still open
2. **path pattern minimums** (about 230). rules: 16.7 SR 8, 9, 16, 20, 16.12 SR
   1 to 4, 16.4 SR 12, and 16.11 SR 3 for bounds. **done on `tushar/exists-table`
   (2026-10-23) but SR 9 and 16.11 SR 3's upper-below-lower**: three automata
   in `src/refine.rs` (`PathMinimums`, `SimplifiedShape`, `SelectiveAlone`),
   the twin in `src/verify.rs`; see
   `research/static-semantics-path-minimums-2026-10-23.md`, including how the
   grammar blew up once and what cut it. two facts per path pattern
   node: whether it can have length 0 and whether it can match 0 nodes,
   synthesized bottom up (an edge has length 1, `?` and `*` make 0 possible,
   concatenation adds). checked at the path pattern, the subpath, and inside
   simplified patterns. either automata in `refine.rs` beside 16.4 SR 6 and 14,
   or flags in the label; the automata keep it out of the engine's cost
3. **leaf values**: 16.11 SR 3 (no upper bound 0, upper not below lower), 18.9
   SR 7, 10, 29 (no zero length or precision), 21.3 SR 4 (no empty delimited
   identifier), 22.1 SR 3 (no `$$` parameter, nothing stands behind it). these
   come from what `leaf.rs` spells, so the fix is the provider refusing those
   spellings in those contexts. 20.24 SR 3 (TRIM with a bare FROM) is grammar
   shape, not a leaf: an automaton
   **partly done on `tushar/exists-table` (2026-10-23)**: 16.11 SR 3 a ii by
   `order_bounds` in `src/tree.rs` (the upper bound re-spelled at spelling
   time, as names are, in both generators: the engine never reads a value), 20.24 SR 3
   and 21.3 SR 4 as automata in `refine.rs`, and `NULL . a` refused by
   `types.rs` (20.1 SR 4-6, 21.2 SR 67); see
   `research/static-semantics-last-ten-2026-10-23.md`. the never counts stayed
   153 productions and 333 pairs. 18.9 SR 7, 10, 29 and 22.1 SR 3 are still
   open. the next smallest witness for a record property was `{ } . a` (20.11
   SR 2 a), so a record source is refused until fields are followed (a
   dynamic source still covers the record derivation): step 4's first case
4. **typing gaps**: groupability for DISTINCT (14.11 SR 4, 14.12 SR 5), closed
   node and edge types, union types and nullability (18.9, 20.8 SR 10, 22.10,
   22.19). widening `types.rs`; check the checker agrees first
5. **graph type bodies** (18.1 to 18.5): consistency of CREATE GRAPH TYPE
   bodies. a small model of the body; close to a catalog
6. **the catalog** (66 rules): references that resolve, procedure signatures,
   parameters with a request behind them. the largest step

beside these, not static semantics, and its own track: **dynamic errors that
can be classified statically**. a variable used after DELETE raises 22G11
(4.4.4) though the query is valid. the rule is typestate: per variable live,
deleted or maybe deleted, plus whether the working table is surely not empty
(true from a statement's start and through INSERT and LET, maybe after MATCH,
FILTER, OPTIONAL). must raise, never raises, may raise; the "should succeed"
suite keeps only never raises

## things that will trip you up

- **luck**: a class can vanish from a regenerated set because extraction picked
  other witnesses, not because a rule took it out. it happened with use after
  delete (17 sentences, then 0, no rule; see the inventory's last section). a
  class is closed only when a rule keeps it out under every witness: check with
  `violations.py`, and a witness shuffle (permuted tie-breaks by seed) is the
  test that makes this general, not built yet
- **the inventory is the agents' reading**: a rule marked not enforced may be
  kept by code nobody found, one marked enforced may be kept only in part.
  confirm against the code before building, and correct the jsonl when wrong
- **this is the 2024 text**: cor 1 amends 13 of the rules (14.7, 14.10 to 14.12,
  15.1, 16.8, 18.1, 18.2, 18.9, 20.7, 22.17); read the amended text for those
- **ambiguous parses**: `{ FINISH }` is a nested query specification and a
  nested data-modifying procedure, `CALL { .. }` is a query, a data-modifying
  and a catalog-modifying statement. a rule must hold under every parse, since
  the engine's probe test accepts any tree and the checker test wants one
  verdict per tree. the test verifiers now run the syntax rules
  (`with_syntax_rules`), which keeps out the parses 13.1 SR 5 forbids, as the
  refine automata do for the generator
- **the next smallest witness**: closing a class makes extraction pick the next
  cheapest body, which may break the next rule (`VALUE { FINISH }` became
  `VALUE { RETURN NO BINDINGS }`, 20.6 SR 3). run
  `generated_trees_pass_the_checkers` before the 11 minute run
- **double quotes**: `""` is an empty string literal in gql, not an identifier;
  only empty backticks are the 21.3 SR 4 case
- **the engine's codes**: turbolay refuses `EXISTS { FINISH }` correctly but as
  0A000 at plan time; a refusal's code can be wrong while the refusal is right.
  `breakdown.py` sorts by cause, not by code
- **nothing iso goes in the repo**: rule numbers and our own notes, never the
  standard's sentences
