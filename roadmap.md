# roadmap

the goal: a generator that produces semantically coherent gql, so we can claim, per iso feature we advertise, that the engine is total over it (right value or right status code), stated as bernot, gaudel and marre test hypotheses with each hypothesis either discharged or listed

prior art for everything below is in `research/prior-art-2026-10-20.md`. the nearest work is the esmeta line (jest, feature-sensitive coverage), which tests valid programs only and claims bugs found, not conformance

## done

- iso bnf vendored, parsed, desugared; purdom covering trees with node-count length, reference height and zheng & wu reference length
- `check-grammar`: proof once for the grammar that tokens joined by a space are gql source text (21.3 SR 13, 14), with 3 stated assumptions
- `verify.rs`: every printed tree checked against the iso ebnf, prose leaves, token-internal rules and rendering, independent of the generator
- structural syntax rules compiled into the grammar as tree automata (16.4 SR 6, 16.4 SR 14, 13.1 SR 5), checked again by the verifier, the two kept in agreement by a differential test. ID086 as a parameter
- cdrc and k-path coverage (`--cdrc`, `--k N`) on the refined grammar: targeted shortest trees, havrikov's algorithm 1. k = 5 runs in about a second. open: a reference height for paths, since a few deep simplified path pattern chains need more height than the production-based one

## pieces left, in the order they block the claim

1. **feature tagging and negatives.** every subclause has conformance rules ("without feature GL01, conforming gql language shall not contain `<unsigned hexadecimal integer>`"). extract them mechanically into a map from productions to feature ids, checked against `features.xml`. tags only go on optional elements and alternatives (cide's discipline), so restricting to the claimed features is one more refinement that deletes exactly those and never leaves broken syntax. negatives come in the same step:
   - parse-level: raselimo, taljaard and fischer's poisoned pairs and rule mutation, which already sit on top of purdom
   - feature-level: one unclaimed-feature subtree per tree, the engine must say "not supported"
   - syntax-rule level: negate one compiled automaton at a time, and have the verifier confirm exactly that rule fails. eris (pldi 2026) shows why: a deliberate error can land in another valid derivation
   - every negative labelled test262 / wasm style: `{phase: parse | syntax-rule | feature | runtime, status: <class>}`
2. **context provider (static semantics).** the biggest piece. scoping and binding (`MATCH`, `LET`, `FOR`, `YIELD`, `NEXT`, `CALL (x) {}`), the type each expression slot expects, a catalog (graphs, graph types, labels, properties, procedures), parameters. bound names are unbounded, but a finite abstraction of the environment is not: typed variable slots up to a bound and the expected type of each slot. that goes into the same product construction as the syntax rules, so purdom, cdrc and k-paths keep working unchanged, and targets no well-typed query reaches are reported as infeasible (no prior work does this, they count over invalid trees or drop what they cannot finish). on top:
   - concrete names assigned late, with xsmith's lifting (create the missing declaration upstream) instead of discarding the tree
   - dinkel's split between scoped query state and the persistent schema, one rule per gql clause
   - mgql's schema model for the catalog: closed graph types, node and edge types, nullability, unions and lists
   - without it most sentences are rejected for semantic reasons, e.g. `SESSION SET GRAPH X''` + newline + `'B  e  '` (11.1 SR 3 a ii wants a graph reference)
3. **syntax rule inventory.** classify every syntax rule in the pdf once: structural (compile into the grammar), binding or typing (context provider), implementation-defined (a parameter, like ID086), or not syntax at all (general rules). gives a coverage number for the rules we honour
4. **data.** a minimal graph per query and partition built by a solver (xdata, qagen, qex style, with z3), plus hand-picked shapes under the small scope hypothesis: self-loops, parallel edges, short cycles, disconnected parts, nulls, multi-labels. sqlfpc's mc/dc, null included, as the adequacy criterion. consistent with the context provider's catalog. no graph data generator meets a coverage goal today, gdsmith and dinkel only avoid empty results
5. **oracle.** in tiers, each test tagged with the tier that backs it:
   - expected status for negative tests, known by construction
   - reference execution: mgql for the read-only core through an emitter from our trees to lean terms, gpml-conformance for paths, cross-checked where they overlap
   - general-rule tables for the rest, **exception conditions included**. neither mgql nor gpml-conformance models them, and they are half of the totality claim
   - metamorphic relations (tlp, rewrites that must not change results), reported as consistency only, never as correctness
   - later, a compositional reference evaluator
6. **value partitions.** most real bugs in the neo4j diff were value level (null, overflow, int/float/decimal mixes, empty groups). a second coverage dimension crossed with operators
7. **harness.** run against the engine, compare with the oracle, minimize failures, keep them as sqllogictest-style regression cases
8. **the claim.** cedar's structure: what is proved, what is tested, what is not modelled. bgm's form: h_min and h1 to h5, each marked proof, construction or evidence. keyed to annex d feature ids. per feature: test count, syntax and semantic coverage, mutation score, residual risk (böhme's bias-corrected estimators, the naive ones underestimate), per-test outcomes. test262, xqts and the opencypher tck all disclaim certification, so word it as evidence under stated hypotheses

## holes that stay after cdrc and k-path

- meaning: k-path picks syntax combinations, not meaningful ones. closed by the context provider
- correctness: coverage says what ran, not that it was right. closed by the oracle
- data: queries need a graph. closed by fixtures
- beyond k: the regularity hypothesis (depth k stands for all depths) stays an assumption. narrowed by a compositional reference evaluator (or translation validation per query) and kani proofs of lowering up to depth k
- values: grammar classes are not value classes. value partitions and a mutation score
- planner paths: the same syntax takes different code paths (`Filter(false)`, the index scan skip). metamorphic checks with planner rewrites toggled
- lexical variety: we always print one space and uppercase keywords, no comments. randomize rendering inside the proven token boundaries (case, whitespace, comments, delimited identifiers)
- readings: SR 5, 6 and 14 already needed interpretation. every reading goes in the claim, doubtful ones get escalated
- outside query syntax: transactions, sessions, concurrency (GT, GS features) need a model checker or a history checker, not the generator
- implementation-defined: about 100 entries, each declared (ID086 is the template)

## order

1. feature tagging, the claimed-feature refinement, and the three kinds of negatives
2. context provider phase 1: the finite environment abstraction in the product grammar, scoping, binding and a small type system for the read-only core (`MATCH`, `RETURN`, `WHERE`, expressions). cdrc and k-paths on the typed grammar with infeasible targets reported
3. oracle for that core via mgql and gpml-conformance, exception condition tables for it, and solver-built graphs
4. the claim for that core in bernot's terms: features F, bound k, hypotheses H1 to H5 and what discharges each
5. grow outward: data modification, the syntax rule inventory, value partitions
