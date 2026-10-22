# roadmap

the goal: a generator that produces semantically coherent gql, so we can claim,
per iso feature we advertise, that the engine is total over it (right value or
right status code), stated as bernot, gaudel and marre test hypotheses with each
hypothesis either discharged or listed

prior art for everything below is in `research/prior-art-2026-10-20.md`. the
nearest work is the esmeta line (jest, feature-sensitive coverage), which tests
valid programs only and claims bugs found, not conformance

## done

- iso bnf fetched (`just fetch`, nothing iso-owned in the repo), parsed,
  desugared; purdom covering trees with node-count length, reference height and
  zheng & wu reference length
- `check-grammar`: proof once for the grammar that tokens joined by a space are
  gql source text (21.3 SR 13, 14), with 3 stated assumptions
- `verify.rs`: every printed tree checked against the iso ebnf, prose leaves,
  token-internal rules and rendering, independent of the generator
- structural syntax rules compiled into the grammar as tree automata (16.4 SR 6,
  16.4 SR 14, 13.1 SR 5), checked again by the verifier, the two kept in
  agreement by a differential test. ID086 as a parameter
- cdrc and k-path coverage (`--cdrc`, `--k N`) on the refined grammar: targeted
  shortest trees, havrikov's algorithm 1. k = 5 runs in about a second. open: a
  reference height for paths, since a few deep simplified path pattern chains
  need more height than the production-based one
- feature claims: every conformance rule extracted from the pdf by
  `tools/conformance.py` and checked against annex a, `features.xml` and table
  10; claims closed under table 10 and checked against 24.2 and 24.3; the rules
  of unclaimed features compiled into the grammar as automata with inherited and
  synthesized state, read again by the verifier, the two kept in agreement by
  tests; a negative per unclaimed rule (`negatives`), its expected status
  declared like ID086. found 6 rules whose prose is one bnf level off; read
  through single-item rules, each reading named
- engines: claim files with deviations (syntax a claim needs that an engine
  leaves out), `claims/neo4j.claim` and `claims/turbolay.claim`; g046/g047
  compiled as order rules; `--short` sentences; coverage that tells "outside the
  claim" apart and ignores bookkeeping copies; `just neo4j`, `just turbolay`
  with a report. acceptance on short sentences: neo4j 79 of 491, turbolay 322 of
  803, the rest mostly meaning
- cor 1:2026: read from its pdf into instructions, every one classified
  (`tools/corrigendum.py`); its grammar edits applied to iso's 2024 `bnf.xml`,
  through a bnf notation reader checked against all of iso's own conversion; its
  conformance rule, table 10 and 24.2 edits applied by the extractor. the target
  is now 2024 + cor 1. turbolay's reading of it holds: every session and
  transaction command is an optional feature
- an iso parser (`src/parse.rs`, libmarpa) and `cover`: any suite's sentences as
  derivation trees of our grammar, verified and measured like ours. turbolay#261
  measured (`research/pr-261-comparison-2026-10-21.md`)
- refinement l-attributed, with rules that choose and copies with fixed text;
  context provider slice 1, scoping (`src/scope.rs`), sound against an
  independent checker (`verify/scope.rs`) on every generated tree and on #261's
  corpus

## pieces left, in the order they block the claim

1. **the rest of the negatives.** feature-level negatives are done. still to
   come:
   - parse-level: raselimo, taljaard and fischer's poisoned pairs and rule
     mutation, which already sit on top of purdom
   - syntax-rule level: negate one compiled automaton at a time (the `required`
     mode feature negatives use), and have the verifier confirm exactly that
     rule fails. eris (pldi 2026) shows why: a deliberate error can land in
     another valid derivation
   - every negative labelled test262 / wasm style:
     `{phase: parse | syntax-rule | feature | runtime, status: <class>}`.
     feature negatives already carry `phase: feature`
   - left from feature tagging: g031/g033 (fixed length path pattern operands),
     since "fixed quantifier" compares a quantifier's two bounds (16.11 SR 3),
     which needs the values, as do 16.11 SR 3's own checks (upper bound > 0,
     lower <= upper) the generator does not make yet
   - cor 1's 35 recorded syntax rule, general rule and prose edits
     (`corrigendum` in `conformance.json`): input for the context provider (14.7
     SR 11 and 12, 14.10 SR 4 on aggregates in sort keys, 14.11 SR 10, 15.1 SR 8
     and 9, 16.8 SR 4) and for the exception tables (the 2202F, 2202E, 2202M,
     2201Z and 22G03 changes in 20.x and 22.10)
2. **context provider (static semantics).** the biggest piece. scoping is done
   (slice 1, readings in `src/scope.rs`; correlation in subqueries and patterns,
   declarations under unions and quantifiers, and three-item lists are what it
   leaves out). left: the type each expression slot expects (slice 2), a catalog
   (graphs, graph types, labels, properties, procedures), parameters. bound
   names are unbounded, but a finite abstraction of the environment is not:
   typed variable slots up to a bound and the expected type of each slot. that
   goes into the same product construction as the syntax rules, so purdom, cdrc
   and k-paths keep working unchanged, and targets no well-typed query reaches
   are reported as infeasible (no prior work does this, they count over invalid
   trees or drop what they cannot finish). on top:
   - concrete names assigned late, with xsmith's lifting (create the missing
     declaration upstream) instead of discarding the tree
   - dinkel's split between scoped query state and the persistent schema, one
     rule per gql clause
   - mgql's schema model for the catalog: closed graph types, node and edge
     types, nullability, unions and lists
   - emits an obligations record per query, collected while the tree is built
     rather than by a second pass: variables and their types, the labels and
     properties they need, which must be equal (a repeated name is a join) and
     which must differ (match modes), and the predicates per partition (which
     `WHERE` should come out true, false or null). data and oracle read it
     instead of reanalysing the query, the way xdata and qagen do
   - without it most sentences are rejected for semantic reasons, e.g.
     `SESSION SET GRAPH X''` + newline + `'B  e  '` (11.1 SR 3 a ii wants a
     graph reference)
3. **syntax rule inventory.** classify every syntax rule in the pdf once:
   structural (compile into the grammar), binding or typing (context provider),
   implementation-defined (a parameter, like ID086), or not syntax at all
   (general rules). gives a coverage number for the rules we honour
4. **data.** a minimal graph per query and partition built by a solver from the
   context provider's obligations record (xdata, qagen, qex style, with z3),
   plus hand-picked shapes under the small scope hypothesis: self-loops,
   parallel edges, short cycles, disconnected parts, nulls, multi-labels.
   sqlfpc's mc/dc, null included, as the adequacy criterion. consistent with the
   context provider's catalog. no graph data generator meets a coverage goal
   today, gdsmith and dinkel only avoid empty results
5. **oracle.** in tiers, each test tagged with the tier that backs it:
   - expected status for negative tests, known by construction
   - witnesses, known by construction: the graph was built so that a binding
     satisfies the query, so that row must be in the result. a partial oracle
     (rows that must appear, not the full answer) that reaches past mgql's core
     and catches wrong empty results, dropped rows and wrong status codes
   - reference execution: mgql for the read-only core through an emitter from
     our trees to lean terms, gpml-conformance for paths, cross-checked where
     they overlap
   - general-rule tables for the rest, **exception conditions included**.
     neither mgql nor gpml-conformance models them, and they are half of the
     totality claim
   - metamorphic relations (tlp, rewrites that must not change results),
     reported as consistency only, never as correctness
   - later, a compositional reference evaluator
6. **value partitions.** most real bugs in the neo4j diff were value level
   (null, overflow, int/float/decimal mixes, empty groups). a second coverage
   dimension crossed with operators
7. **harness.** run against the engine, compare with the oracle, minimize
   failures, keep them as sqllogictest-style regression cases
8. **the claim.** cedar's structure: what is proved, what is tested, what is not
   modelled. bgm's form: h_min and h1 to h5, each marked proof, construction or
   evidence. keyed to annex d feature ids. per feature: test count, syntax and
   semantic coverage, mutation score, residual risk (böhme's bias-corrected
   estimators, the naive ones underestimate), per-test outcomes. test262, xqts
   and the opencypher tck all disclaim certification, so word it as evidence
   under stated hypotheses

## holes that stay after cdrc and k-path

- meaning: k-path picks syntax combinations, not meaningful ones. closed by the
  context provider
- correctness: coverage says what ran, not that it was right. closed by the
  oracle
- data: queries need a graph. closed by fixtures
- beyond k: the regularity hypothesis (depth k stands for all depths) stays an
  assumption. narrowed by a compositional reference evaluator (or translation
  validation per query) and kani proofs of lowering up to depth k
- values: grammar classes are not value classes. value partitions and a mutation
  score
- planner paths: the same syntax takes different code paths (`Filter(false)`,
  the index scan skip). metamorphic checks with planner rewrites toggled
- lexical variety: we always print one space and uppercase keywords, no
  comments. randomize rendering inside the proven token boundaries (case,
  whitespace, comments, delimited identifiers)
- readings: SR 5, 6 and 14 already needed interpretation. every reading goes in
  the claim, doubtful ones get escalated
- outside query syntax: transactions, sessions, concurrency (GT, GS features)
  need a model checker or a history checker, not the generator
- implementation-defined: about 100 entries, each declared (ID086 is the
  template)

## order

1. parse-level and syntax-rule negatives, labelled
2. context provider phase 1: the finite environment abstraction in the product
   grammar, scoping, binding and a small type system for the read-only core
   (`MATCH`, `RETURN`, `WHERE`, expressions), and the obligations record. cdrc
   and k-paths on the typed grammar with infeasible targets reported
3. solver-built graphs from the obligations record with witnesses as the first
   oracle, then mgql and gpml-conformance for that core and exception condition
   tables for it
4. the claim for that core in bernot's terms: features F, bound k, hypotheses H1
   to H5 and what discharges each
5. grow outward: data modification, the syntax rule inventory, value partitions
