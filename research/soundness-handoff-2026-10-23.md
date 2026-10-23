# soundness: handoff

> for agents: dated working notes, terse on purpose. people start at the [readme](../README.md)

the goal: every sentence the generator emits keeps every syntax rule of iso gql
(39075:2024 with cor 1), for the whole language, not only turbolay's claim.
completeness (every valid sentence reachable) is a separate track and not the
goal here. main at ba471db, 2026-10-23

the short version: turbolay refuses none of the 3,800 typed sentences as ours
(`research/static-semantics-last-ten-2026-10-23.md`), but turbolay is not the
oracle. a check against the text on 2026-10-23 found two rule families broken
in the cached sets that no detector and no engine had flagged. the inventory's
classification is right that they are open; nothing measured whether we reach
them. so before closing more rules, audit: every rule, against the text, with a
check that would see it broken

## where things are

- the inventory: `research/static-semantics-inventory-2026-10-22.md` and
  `research/static-inventory-2026-10-22.jsonl` (1,025 rules: clause, sr, kind,
  status, where, note). built by `tools/inventory/` from `iso-text/` (`just
  iso-text`, gitignored, from your pdf)
- the detectors: `tools/inventory/violations.py <sentences...>`, text level,
  about 12 rules
- the independent checkers: `src/verify.rs` (syntax rules over trees, incl.
  the `refine.rs` automata via `automaton_and_verifier_agree`),
  `src/verify/scope.rs`, `src/verify/types.rs`
- where rules are enforced: `src/refine.rs` (structural, as tree automata),
  `src/context/scope.rs`, `src/context/types.rs`, `src/leaf.rs` (spelling),
  `src/tree.rs` (`order_bounds`)
- the previous handoff, for how rules got closed so far:
  `research/static-semantics-handoff-2026-10-22.md`

## what is broken today

checked on `sentences/typed-2vars-turbolay-claim-last-ten.jsonl` (3,834) and
the scope only purdom sets regenerated at ba471db (`purdom --short --claim
claims/<engine>.claim --format jsonl`: turbolay 785 sentences in 112 s, neo4j
463 in 218 s; the committed `sentences/scope-*-claim.jsonl` predate the path,
exists and last ten work and still show 6 fixed classes, regenerate them):

- **18.9 SR 7, 10, 29**: zero length or precision. known. 3 typed, 4 scope
  turbolay. `VALUE x CHAR ( 0b0 ) = NULL FINISH`. leaf values: the bound in a
  type's length or precision is spelled without the rule. close in the leaf
  provider or as a refine fact like `DelimitedNotEmpty`
- **18.2 SR 2 and 18.3 SR 2**: a node or edge type spec simply contained in a
  closed node or edge reference value type has no local alias, key label set or
  type name (18.2), and no key label set, type name, endpoint aliases or key
  labelled source reference (18.3). new. 12 typed, 3 scope turbolay, 2 scope
  neo4j:
  ```
  VALUE x NODE TYPE { } AS a = NULL FINISH
  VALUE x DIRECTED EDGE TYPE { } CONNECTING ( a TO a ) = NULL FINISH
  VALUE x ( ) <-[ { a NODE TYPE { } AS a } ]- ( ) = NULL FINISH
  DELETE SESSION_USER IS TYPED NODE { } AS a
  ```
  turbolay files these as its closed type parse gap, so `breakdown.py` never
  showed them as ours. structural: an inherited context in `refine.rs` (inside
  a closed reference value type) refusing the alias, key label set, name and
  endpoint alias productions, plus the checker
- **20.9 SR 3**: an aggregate function shall not contain a `<procedure body>`.
  19.4 SR 2 says `EXISTS { GP }` "is effectively replaced by" `EXISTS { MATCH
  GP RETURN TRUE AS RIA }`, which contains one. 6 typed:
  `RETURN COUNT ( * ) AS x NEXT RETURN CASE WHEN MAX ( EXISTS { <- } ) IS NULL
  THEN NULL ELSE x END AS y GROUP BY x`. take the strict reading (the rule
  applies after the replacement) and record it as a reading. scope or types
  flag: "contains a procedure body, after effective replacement", synthesized,
  refused at `<aggregate function>`

the dynamic class (use after delete, 22G11) is not a syntax rule and not in
scope here

## why these were missed

- the detectors cover about 12 of the 68 open constraint and type rules; "0
  violations" meant "0 of the ones we look for"
- turbolay is a weak oracle for anything it does not parse: its parse gaps
  (closed types, typed VALUE) hide our invalid sentences under its bucket
- "effectively replaced by" rewrites: rules are stated over the replaced text
  (19.4 SR 2, 3 and others). a rule checked on the surface text misses what the
  replacement adds. nobody listed these rewrites
- the inventory was classified by agents reading the 2024 text with file:line
  evidence; cor 1 amends 13 of the rules and they were not reclassified

## the audit

per rule, one row, every `shall` / `shall not` sentence of a syntax rule (a
rule with several gets a row per sentence, `16.11 SR 3 a ii` style):

1. **classify again, from the text**: kind as before. also take the 482
   "definition" rows and grep their text for `shall`: a definition that
   constrains is a constraint (the extraction loses indentation, so a sub item
   can sit under the wrong number, see the inventory's caveats)
2. **cor 1**: apply the 13 amended rules (14.7, 14.10 to 14.12, 15.1, 16.8,
   18.1, 18.2, 18.9, 20.7, 22.17) from `grammar/corrigendum.json` and classify
   the amended text
3. **effective replacements**: list every syntax rule that says "is
   effectively replaced by" or "is equivalent to", and for each constraint
   rule whether it can see what the replacement introduces. each such pair is a
   row
4. **enforcement**: where the generator keeps it (file:line), or the claim or
   grammar making it unreachable (say which feature or production)
5. **the check**: where the independent checker reports it (`src/verify*`).
   this is the column that matters: a rule the checker does not report is not
   known to hold, whatever the generator does. aim for the checker covering
   every constraint and type rule, so "0 checker failures on the whole grammar
   set" is the soundness claim, and `violations.py` shrinks to a cross check
6. **reachability**: whether a generated set holds a construct the rule talks
   about (a text grep is enough to say "reachable"; it is not enough to say
   "unreachable", that needs the grammar or claim reason from 4)

output: a new jsonl next to the inventory, same keys plus `sentence` (the
shall text, in our words, not quoted), `replacement`, `check`, `reachable`.
split the clauses across agents by chapter; each agent reads `iso-text/`
itself, the rules stay paraphrased in the repo (nothing iso owned committed)

## the open rules, by how they close

68 constraint and type rules open at ba471db (64 not modelled, 4 checked only),
65 catalog rules. "unreachable under turbolay's claim" is not good enough for
this goal: the whole grammar set reaches them

- **structural, refine automata**: 18.2 SR 2, 3, 7; 18.3 SR 2, 3, 4, 8; 18.1
  SR 10; 18.5 SR 1 (distinct names need values, see leaf); 17.6 SR 1; 8.2 SR
  2; 14.2 SR 3, 4; 9.2 SR 4 to 7; 20.6 SR 5, 6; 20.9 SR 3
- **statement kinds**, a synthesized kind (query, data modifying, catalog) in
  scope's label: 9.1 SR 5, 6, 7; 12.8 SR 2; 13.6 SR 2; 14.5 SR 2; 14.12 SR 26
- **leaf values**: 18.9 SR 7, 10, 13, 21, 28, 29, 38, 40; 21.2 SR 20. ordering
  between two values settles at spelling time like `order_bounds`
- **graph type bodies**: 18.1 SR 8, 9, 11, 14, 16; 18.3 SR 17, 18. need a model
  of the body (aliases and key label sets declared, then referenced)
- **typing**: 7.1 SR 6; 10.1 SR 5, 8; 10.2 SR 5, 8; 14.11 SR 4; 14.12 SR 5
  (22.15 has no type restriction in the 2024 text; check cor 1, else these are
  vacuous); 18.9 SR 62, 65, 68, 84, 87, 88; 20.8 SR 9, 10; 20.15 SR 2; 20.16
  SR 1; 20.24 SR 4; 21.2 SR 73, 75; 22.10 SR 5, 6; 22.19 SR 2, 5
- **catalog** (65): references that must resolve. for soundness without a
  catalog model, the honest option is to not generate what needs one (refuse
  the productions that reference a catalog object by name) and list them as
  never, rather than emit sentences whose validity depends on a catalog nobody
  declared. decide this before modelling a catalog
- **5.3 SR 4** (confusable identifiers): numbered ascii names; make it a
  reading with the leaf provider's alphabet as the argument

## order

1. regenerate the stale sets at main: the scope sets (the commands above) and
   a whole grammar typed set at 2 variables (no `--claim`; the cached
   `typed-2vars-whole-grammar-before-258437a.jsonl` is from before the exists,
   path and last ten work). with `--deadline` and the progress lines
2. close the three broken families above, each with a probe in the tests and
   the checker reporting it first (red, then green)
3. the audit, by chapter, in parallel agents
4. close what the audit finds reachable, structural first, then statement
   kinds, leaf values, graph type bodies, typing
5. the catalog decision
6. the claim: per rule, the row from the audit. sound = every constraint and
   type rule is enforced (generator), reported (checker), and the checker
   passes on the whole grammar set; readings listed

## what not to redo

- the 2 variable typed run is the regression gate (about 8 minutes); any rule
  change is measured there and on the 1 slot cover run (9 s) first
- `extraction_matches_emission` and `joined_grounds_are_exact` after any
  label change
- `automaton_and_verifier_agree` (tests/refine.rs) after any refine rule: the
  checker and the automaton have to agree
- 3 variables is not this track (`research/three-variable-run-2026-10-23.md`)
