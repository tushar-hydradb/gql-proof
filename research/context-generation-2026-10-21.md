# adding context to a grammar generator without growing the grammar

> for agents: dated working notes, terse on purpose. people start at the [readme](../README.md)

the question: who else has made a grammar-based generator emit well-scoped, well-typed sentences, and how did they keep it from blowing up. our slice 1 and 2 compile scope and types into a product grammar (nonterminal × inherited × synthesized state). with two names it takes 5 minutes, with three it never finished in 4 hours. raptor (`papers/raptor/`) makes the same point for transit: the time-expanded graph is too big, so it works in rounds over the timetable itself, keeps pareto bags per stop and rescans only routes through stops that improved

four searches, every citation checked against a publisher, dblp, acl anthology, crossref or the paper itself unless marked unverified

## the short answer

- nobody multiplies the grammar except input algebras (gopinath, nemati, zeller, icse 2021), which rewrites the grammar per pattern and only works for small pattern sets. that is what we do, and it is the known dead end
- everyone else carries context beside the derivation: attributes or an environment read while choosing (xsmith, csmith, yarpgen, sqlancer, dinkel), constraints solved over an untouched grammar (isla, fandango, dewey's clp), or typing rules run backwards (pałka, fetscher, quickchick)
- none of them keeps systematic grammar coverage over valid trees. the only paper that defines coverage over attribute-grammar trees is harm and lämmel 2000, and it says outright that some targets are infeasible and leaves them to the user
- nobody reports infeasible targets per target. the template for doing it is from code coverage: bardin et al. 2015, covered / proven infeasible / unknown

so the combination we want (valid by construction, purdom/cdrc/k-path counted over valid trees, infeasible targets reported with a reason) has no prior work. the pieces to build it from all exist

## 1. the algorithm: lazy derivations with labels

- **knuth, "a generalization of dijkstra's algorithm", ipl 6(1) 1977**, doi 10.1016/0020-0190(77)90002-3. the grammar problem: cheapest derivation per nonterminal when rule costs are superior functions (monotone, at least each argument). purdom's first pass is this with cost = size. height (max+1) and size (sum+1) are both superior
- **nederhof, "weighted deductive parsing and knuth's algorithm", computational linguistics 29(1) 2003**, https://aclanthology.org/J03-1006. knuth over items of a deduction system: items exist only once derived, the item space is never enumerated. for us an item is a nonterminal with a label, created only when something derives it
- **felzenszwalb and mcallester, "the generalized a* architecture", jair 29 2007**, doi 10.1613/jair.2187. lightest derivation with a* bounds from coarser abstractions. the base grammar with attributes erased is that abstraction: purdom's height and size per nonterminal bound every labelled item, so items that cannot beat the best known are never expanded. same idea as **klein and manning, a* parsing, hlt-naacl 2003** (https://aclanthology.org/N03-1016), exact while touching 3-5% of the edges
- **bancilhon, maier, sagiv, ullman, magic sets, pods 1986**, doi 10.1145/6012.15399, plus semi-naive evaluation. magic sets push the top-down binding into bottom-up evaluation, so a nonterminal is expanded under an inherited label only when some parent asks for it. semi-naive joins only last round's new facts: raptor's "rescan only what improved". **dyna** (eisner, goldlust, smith, hlt-emnlp 2005, https://aclanthology.org/H05-1036) runs exactly this for weighted logic programs
- **huang and chiang, "better k-best parsing", iwpt 2005**, https://aclanthology.org/W05-1506. the k-th best derivation of a node computed only when a parent asks for it. for cdrc and k-paths: the next cheapest derivation through a target, pulled on demand
- **dasgupta, chakrabarti, desarkar, "multiobjective heuristic search in and/or graphs", j. algorithms 20(2) 1996**, doi 10.1006/jagm.1996.0015, and **andersen, nielsen, pretolani, bicriterion shortest hyperpaths, ima j. management mathematics 14(3) 2003**. the warning: pareto bags on hypergraphs can be exponential and the multi-objective and/or problem is np-hard. keep the label small (height, size) and put the semantic summary in the item key, not in the pareto criteria

## 2. the state: requirements up to renaming

this is what kills the per-name blowup. a subtree is summarised by what it needs from outside and what it declares, never by the environment it sits in, and names are counted, not named

- **grygiel and lescanne, "counting and generating lambda terms", jfp 23(5) 2013**, doi 10.1017/S0956796813000178. counts terms by (size, number of free indices). the free-variable bound is exactly a requirement parameter
- **gvero, kuncak, kuraj, piskac, "complete completion using types and weights", pldi 2013**. succinct types: an environment becomes a set of types, order and multiplicity dropped. reachability is decided on that finite abstraction first, terms rebuilt after
- **boyapati, khurshid, marinov, korat, issta 2002** and **gligoric et al., udita, icse 2010**, doi 10.1145/1806799.1806835. isomorphism breaking: a fresh object is always the next unused one. fresh names in canonical order (de bruijn levels) mean `MATCH (a) RETURN a` and `MATCH (b) RETURN b` are one item
- **zhang, sun, su, skeletal program enumeration, pldi 2017**, https://arxiv.org/abs/1610.03148. the closest generator: fixed skeletons, then every variable-use pattern up to alpha-equivalence. exhaustive within a skeleton, but skeletons come from existing tests, not from grammar coverage

## 3. memoising and pruning

- **duregård, jansson, wang, feat, haskell 2012** and **kuraj, kuncak, jackson, scife, oopsla 2015**, doi 10.1145/2814270.2814323. enumerators memoised by their parameters (scife: "trees of size n with keys in r"). for us: per (nonterminal, requirement, type), the count and the smallest witness. a target reachable only through items with count 0 is infeasible, with the items as the reason
- **claessen, duregård, pałka, "generating constrained random data with uniform distribution", flops 2014 / jfp 25 2015**, doi 10.1017/S0956796815000143. counting plus lazy pruning of partial values, pruned counts subtracted, giving uniform sampling over valid terms. useful later, when we want random valid sentences beside the covering ones
- **runciman, naylor, lindblad, lazy smallcheck, haskell 2008** and **polikarpova et al., synquid, pldi 2016**. check partial trees: a hole the verdict does not depend on prunes all its fillings. that is the requirement check during the left to right scan of a production
- **godefroid, "compositional dynamic test generation", popl 2007**. per-function summaries make tests grow with feasible paths per function, not their product. per-nonterminal summaries of which semantic states are realisable are the same thing for grammars
- **kuznetsov, kinder, bucur, candea, "efficient state merging in symbolic execution", pldi 2012**. merge states that differ only in what nothing downstream reads. we already do a crude version (`DISCARD`), it should be the rule, not the exception

## 4. refining the abstraction from the checker

- **guo et al., tygar / hoogle+, "program synthesis by type-guided abstraction refinement", popl 2020**, doi 10.1145/3371080. search a small graph over coarse abstract types; when a concrete witness fails the real type check, split only the abstract state the failure blames and search again
- this is the principled version of what i did by hand in slice 2 (opaque value variables, case and coalesce narrowed to exact or null, the simple case operand classes). each was a manual split or merge after the checker failed a tree. with tygar's loop the independent checkers we already have drive the refinement, and the state only grows where the language needs the distinction

## 5. coverage over valid trees and infeasibility

- **harm and lämmel, "two-dimensional approximation coverage", informatica 24(3) 2000**, https://www.informatica.si/index.php/informatica/issue/view/96/84. the one precedent. syntactic coverage plus coverage of abstract attribute domains (empty, singleton, many), trees completed smallest first and kept only if their conditions hold. negatives by negating exactly one condition. they say syntactic coverage is "relaxed due to semantic constraints" and that whether coverage can still improve is undecidable; infeasible targets are relaxed by hand, never reported
- **lämmel and schulte, geno, testcom 2006**, doi 10.1007/11754008_2. combinatorial coverage cut down by hand-set depth, balance and pairwise controls; context conditions as filters on constructors, so generate then filter
- **hennessy and power, empirical software engineering 13(4) 2008**, doi 10.1007/s10664-008-9067-7. purdom on iso c++ gave 81 sentences, 7 of them valid programs. the motivating number for this whole slice
- **steinhöfel and zeller, isla, esec/fse 2022**, doi 10.1145/3540250.3549139. constraints and z3 over an untouched grammar; k-path coverage only as a cost term in the solver's queue (`low_k_coverage_penalty`, `low_global_k_path_coverage_penalty`, k = 3, checked in `solver.py`). k-paths are counted over the grammar, so an infeasible one is chased forever and never reported. unsat is per formula
- **zamudio amaya, smytzek, zeller, fandango, issta 2025**, doi 10.1145/3728915. evolutionary search over python constraints, much faster than isla, no coverage over valid trees, no infeasibility
- **bardin et al., "sound and quasi-complete detection of infeasible test requirements", icst 2015**, doi 10.1109/ICST.2015.7102607. value analysis plus weakest preconditions prove ~95% of infeasible coverage labels infeasible. the reporting shape to copy: covered, proven infeasible, unknown

## the query generators, for completeness

sqlancer (rigger and su, osdi 2020), sqlsmith, squirrel (ccs 2020), dynsql (usenix security 2023), gdsmith (issta 2023), dinkel (arxiv 2408.07525, pvldb 19) and graphgenie (icse 2024) all keep a live schema and scope object in a hand-written generator and generate randomly. dinkel's split between query state and graph schema, updated after every clause, is the useful model for slice 3. none has grammar coverage or infeasibility

## what this means for gql-proof

the core changes from "multiply the grammar, then run purdom" to knuth-style lazy derivation over items:
- an item is a base nonterminal with a label: what the subtree needs from outside (counts of node, edge, path and value variables it references, by kind and type class), what it declares, and its own type class. no names, no inherited environment
- items are built bottom up in rounds, each round rescanning only productions with a child that gained an item or a smaller witness last round (semi-naive, raptor's marking). an item keeps one witness, its smallest tree: no pareto sets, one sentence per target is enough, so the multi-objective warning above does not apply
- a production is scanned left to right like a raptor route: a declaration from an earlier child discharges a later child's requirement, failed combinations are pruned on the spot
- inherited context goes top down by demand (magic sets): a parent asks for a child item only under the context it can give
- base-grammar purdom heights and sizes bound every item (a*), so items that cannot beat the best known witness for a target are never expanded
- names are given at the end, fresh in canonical order, which is xsmith's lifting
- abstractions start coarse and are split only where the checker fails a witness (tygar), instead of by hand
- every target ends covered, proven infeasible (no item pair meets, with the items as the reason) or unknown (budget spent)

what stays: the two checkers, the corpus differential, `cover`, the parser. they judge the new engine exactly as they judged the product one

## unverified

- the doi of xsmith (gpce 2023) and of dewey, roesch, hardekopf, ase 2014
- the content of lämmel, "grammar testing", fase 2001, of harm and lämmel, "testing attribute grammars", waga 2000, and of keramati and mirian-hosseinabadi, ist 2015 (doi 10.1016/j.infsof.2014.09.007), which may be a close match: constrained input grammars with coverage criteria
- myth's memoisation and transit's observational-equivalence pruning are from memory, the pdfs did not load
- two names were wrong in the brief: fandango is zamudio amaya, smytzek, zeller (not steinhöfel), and bardin et al. 2015 does not include chebaro
