# roadmap

the goal: a generator that produces semantically coherent gql, so we can claim, per iso feature we advertise, that the engine is total over it (right value or right status code), stated as bernot, gaudel and marre test hypotheses with each hypothesis either discharged or listed

## done

- iso bnf vendored, parsed, desugared; purdom covering trees with node-count length, reference height and zheng & wu reference length
- `check-grammar`: proof once for the grammar that tokens joined by a space are gql source text (21.3 SR 13, 14), with 3 stated assumptions
- `verify.rs`: every printed tree checked against the iso ebnf, prose leaves, token-internal rules and rendering, independent of the generator
- structural syntax rules compiled into the grammar as tree automata (16.4 SR 6, 16.4 SR 14, 13.1 SR 5), checked again by the verifier, the two kept in agreement by a differential test. ID086 as a parameter
- cdrc and k-path coverage (`--cdrc`, `--k N`) on the refined grammar: targeted shortest trees, havrikov's algorithm 1. k = 5 runs in about a second. open: a reference height for paths, since a few deep simplified path pattern chains need more height than the production-based one

## pieces left, in the order they block the claim

1. **feature tagging.** every subclause has conformance rules ("without feature GL01, conforming gql language shall not contain `<unsigned hexadecimal integer>`"). extract them into a map from productions to feature ids, checked against `features.xml`. restricting to the claimed features is then one more refinement, and each unclaimed feature gives negative tests the engine must reject
2. **context provider (static semantics).** the biggest piece. scoping and binding (`MATCH`, `LET`, `FOR`, `YIELD`, `NEXT`, `CALL (x) {}`), the type each expression slot expects, a catalog (graphs, graph types, labels, properties, procedures), parameters. not expressible by grammar specialization since bound names are unbounded, so an attribute-grammar style generator threading an environment, in the style of xsmith or cedar's generators. without it most sentences are rejected for semantic reasons, e.g. `SESSION SET GRAPH X''` + newline + `'B  e  '` (11.1 SR 3 a ii wants a graph reference)
3. **syntax rule inventory.** classify every syntax rule in the pdf once: structural (compile into the grammar), binding or typing (context provider), implementation-defined (a parameter, like ID086), or not syntax at all (general rules). gives a coverage number for the rules we honour
4. **data.** small-graph fixtures under the small scope hypothesis (up to m nodes and edges; cycles, nulls, multi-labels, self-loops), consistent with the context provider's catalog
5. **oracle.** cheapest first: expected status for negative tests (known by construction), metamorphic relations (tlp, rewrites that must not change results), mgql for the read-only core and gpml-conformance for paths, then a compositional reference evaluator for the rest
6. **value partitions.** most real bugs in the neo4j diff were value level (null, overflow, int/float/decimal mixes, empty groups). a second coverage dimension crossed with operators
7. **harness.** run against the engine, compare with the oracle, minimize failures, keep them as sqllogictest-style regression cases

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

1. feature tagging and the claimed-feature refinement
2. context provider phase 1: scoping, binding and a small type system for the read-only core (`MATCH`, `RETURN`, `WHERE`, expressions)
3. oracle for that core via mgql and gpml-conformance, plus small-graph fixtures
4. the claim for that core in bernot's terms: features F, bound k, hypotheses H1 to H5 and what discharges each
5. grow outward: data modification, the syntax rule inventory, value partitions
