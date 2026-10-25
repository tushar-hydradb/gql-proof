# roadmap

where gql-proof stands and what is left, in the order it blocks the claim. each step points at the notes with the detail. prior art for every step is in `research/prior-art-2026-10-20.md`

## the goal

for every feature an engine claims, evidence that it handles all of it: every construct the standard defines for the feature is used by some valid query, the engine answers each one right, and every assumption the claim rests on is either proven or written down. for every feature it does not claim, it rejects what it should

the closest existing work is the esmeta line for javascript, which tests valid programs only and reports bugs found, not conformance

## done

- **the grammar, from iso.** iso's grammar is downloaded, corrigendum 1's edits applied from its pdf, and read as a context free grammar. a proof once for the whole grammar that printing tokens with one space between them is valid gql text
- **coverage of the grammar.** a set of queries that uses every rule (purdom's algorithm), every rule in every place it can appear (cdrc), and every chain of up to k rules (k-paths). k = 5 runs in about a second
- **a second checker.** every query is checked against iso's grammar again by code written separately from the generator, so the two have to agree
- **features.** every conformance rule is read out of the standard's pdf and checked against annex a, the feature list and table 10. an engine's claim (`claims/`) restricts generation to its features, and every unclaimed feature gets a query the engine must reject
- **engines.** runs against neo4j and turbolay, with a breakdown of every refusal by cause
- **other suites.** any suite's queries parsed with the iso grammar and measured with the same coverage. turbolay#261 measured (`research/pr-261-comparison-2026-10-21.md`)
- **meaning.** every variable bound before it is used and every expression typed, at up to 2 variables, checked again by separate checkers. the first attempt multiplied the grammar out and never finished at three names; the context engine works over the grammar as it is instead (`algorithm.md`)
- **cost under control.** the typed run at 2 variables went from not finishing to about 10 minutes (`research/pruning-2026-10-22.md`, `research/complexity-2026-10-22.md`)
- **the arguments.** why a fixed number of variables is enough: 3 for productions and 4 for production-in-place pairs, measured to 4, and 2 typed variables (`research/cutoff-2026-10-21.md`, `research/types-cutoff-2026-10-22.md`, `research/totality-2026-10-21.md`)
- **the syntax rule inventory.** all 1,025 syntax rules of the standard classified by what we do with each. of the 426 that constrain a query, 76 are still open (`research/static-semantics-inventory-2026-10-22.md`)
- **the first rule closed from it.** a subquery's body has to produce a table, so `EXISTS { FINISH }` is gone. turbolay's acceptance went from 52% to 62% of the typed set (`research/static-semantics-exists-table-2026-10-22.md`)

## next, in order

1. **static semantics sound.** close the open syntax rules our queries still break. path patterns first: they are 230 of the 238 queries turbolay rightly refuses as ours. then leaf values (zero lengths, empty names), typing gaps, graph type bodies, and a catalog. each closed by a rule, so it holds whatever query extraction picks, not by luck. plan and order: `research/static-semantics-handoff-2026-10-22.md`
2. **3 variables.** the bound the coverage argument needs for productions. needs the fixed point faster again: `research/follow-ups-2026-10-22.md`
3. **graphs and the first answer checks.** a witness graph per query, built from the query so a known row has to come back, plus near misses and every graph up to about 3 nodes. checks that need no evaluator: the witness row appears, and equivalent queries agree. `research/oracle-2026-10-22.md`. done for the typed set: the witness construction is stated and proved and built, and so is the reference evaluator over the witness graph (`gql-proof oracle`, `research/oracle-witness-2026-10-23.md`); 3,604 of the 3,800 typed sentences get a graph and their whole result, 180 a status with the reason. turbolay agrees on 2,381 of the records it runs; every disagreement is one of four findings against it
4. **the rest of the negatives.** queries that break exactly one grammar rule or one syntax rule, each labelled with the phase it should fail in and the status it should fail with
5. **a reference evaluator.** built with step 3 for the read-only language over the literal classes (`src/oracle/eval.rs`), with the data exceptions; left: data modification, use after delete, and the values the standard leaves to the implementation, which need a declaration per engine
6. **the claim.** for that core, stated as bernot, gaudel and marre do: the features, the bound, the hypotheses, and what backs each one (proof, construction or evidence). per feature: tests, coverage, what is left and why
7. **grow outward.** the catalog, data modification, edge case values (nulls, overflow, number type mixes, empty groups: most of the real bugs we found comparing against neo4j were values like these)

## open even after all that

- **beyond the bound.** that the bound on variables and chain length is enough stays a hypothesis. a reference evaluator and proofs about turbolay's lowering narrow it, they do not close it
- **optimized builds.** the engine's optimizer can take different paths for the same query, so a claim about one build is not automatically a claim about another. open, and tracked in the linear doc on keeping the proof valid while turbolay gets fast
- **rendering.** we always print one space between tokens, uppercase keywords and no comments. varying that inside the proven token boundaries is cheap and not done
- **readings.** where the standard can be read more than one way we picked a reading, and each one goes in the claim
- **outside a single query.** transactions, sessions and concurrency need a model checker or a history checker, not a query generator
- **implementation-defined behaviour.** about 100 items, each needs a declared value (the default match mode is the template)
