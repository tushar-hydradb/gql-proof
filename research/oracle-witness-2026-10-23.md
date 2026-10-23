# the witness oracle: a graph and a known answer for every query, from what generation already knows

> for agents: dated working notes, terse on purpose. people start at the [readme](../README.md)

the plan in `research/oracle-2026-10-22.md` says a run should check answers, not
only acceptance. this note is the first step: the statement to prove, the
construction that proves it, where the construction stops today, and what gets
built from it. branch `tushar/oracle`, main at 51d059a, 2026-10-23

## the statement

inputs, all of which exist at the end of a typed run:

- `q`, a sentence of the typed set, and its tree `T(q)` over the iso grammar
- `C(q)`, the generation record: per variable its kind (node, edge, path,
  value, group) from scope's label and its class from types' label, and the
  flags the labels carry (an aggregate below, a nested query below, a yield).
  the generator computes this to make `q` valid; the oracle reads it and does
  not recompute it (`--jsonl` now writes it as `vars`, see "the export")

outputs:

- `G(q)`, a graph in our own ir: nodes with a label set and properties, edges
  with a label set, a direction and properties, every element with a test only
  `_id` property
- `S(G)`, an ordered list of statements that puts an empty engine into the
  state `G`. compiled per engine from the ir: gql `INSERT`, cypher `CREATE`,
  turbolay's in-memory records. anything the engine accepts is fair game; the
  statements are never the construct under test
- `q_r`, the expected outcome of `q` on `G(q)`: a bag of rows, or "no result"
  with status 00000, or an exception class

**theorem 1 (witness).** for every `q` in the pattern core (defined below)
there is a computable `G(q)` and a record `r(q)` such that, by the general
rules of iso 39075, either the binding table of `q`'s match on `G(q)` contains
`r(q)`, or the pattern of `q` has no match on any graph and the table is empty
on every graph; and the construction says which

**theorem 2 (exact, bounded).** for every `q` in the pattern core and every
finite graph `G`, the bag `q(G)` is computable, so `q_r = q(G(q))` is known in
full, not only up to one row

theorem 1 is what is built in this note. theorem 2 is the reference evaluator
for the pattern core (roadmap step 5); its proof is one paragraph here because
the standard already gives the algorithm, and its code is the next step

## the pattern core

a `q` is in the core when every `MATCH` in it is a `<simple match statement>`
whose graph pattern, after the syntax rule transformations of 16.7 (SR 10
multiset alternation to union, SR 12 element where to parenthesized where, SR
14 implicit nodes and full edges), has:

- node and edge patterns with any label expression and a property
  specification whose values are literals
- concatenation, union, quantifiers (fixed, bounded, `*`, `+`) with a lower
  bound up to 64 (a knob; the set has bounds up to 2,560 from the radix
  spellings, which are a hop count finding for an engine, not a witness
  problem), `?`, parenthesized subpatterns with a path mode (WALK, TRAIL,
  SIMPLE, ACYCLIC) and a subpath variable, path variables, several path
  patterns in one list, either match mode
- simplified path pattern expressions (16.12), read as the edge patterns,
  groups and label expressions SR 5 and 6 rewrite them to
- where clauses (element, parenthesized, graph pattern) that are
  conjunctions of: `x . k = literal`, `x : LE` / `x IS LABELED LE`, `x . k IS
  [NOT] NULL`, `x IS [NOT] DIRECTED`, `x IS [NOT] SOURCE OF y`, `x IS [NOT]
  DESTINATION OF y`, `PROPERTY_EXISTS ( x , k )`
- a selective prefix (ALL, ANY, SHORTEST and their variants) only on a path
  pattern whose witness is its only match on `G(q)`, which the construction
  checks and otherwise reports (theorem 2 lifts this)

and whose statements, walked in order through `NEXT`, are `MATCH` (above),
`FILTER` of the same core predicates (a requirement made true on the witness,
14.6), `RETURN` of variables (with `AS`, `DISTINCT`, `GROUP BY`; the record is
renamed to the columns, 14.11), `ORDER BY` (keeps the row), `LIMIT n` with
`n > 0`, and `FINISH` last. `OFFSET`/`SKIP` and `LIMIT 0` may drop the row and
leave the core. the graph plays no part in a `q` without a `MATCH`: `G(q)` is
empty, and `q_r` is the business of the expression evaluator, not this note

everything else (a where clause with an arbitrary expression, a `LET`, a
`CALL`, `EXISTS` in a predicate, aggregates, `OPTIONAL`, data modification) is
out of the core today. a `q` out of the core still gets `G(q)` (the witness of
its patterns) and a weaker `q_r`: status 00000 with no claim on rows. the
oracle output tags every row with which tier backs it

the cached typed set (`sentences/typed-2vars-turbolay-claim-path-minimums.jsonl`,
3,808 distinct): 2,143 sentences contain a `MATCH`, 2,135 start with one and
most are `MATCH <pattern> FINISH`; 117 are `MATCH ... RETURN ...`. so the
pattern core is where the sentences are. `gql-proof oracle` on that set
(`--match-mode-default different-edges`, 4 s):

| tier | sentences |
| --- | --- |
| witness (theorem 1) | 1,695 |
| of which no graph matches | 8 |
| status only | 2,105 |

out of the core by reason, a sentence counted once per reason: no `MATCH` at
the top level 1,673; a return item that is an expression 685; a statement that
is not `MATCH` or a core `FILTER` (`VALUE`, `LET`, `ORDER BY` alone, `CALL`)
349; a selective prefix 203; `EXISTS` in a where clause 195; a where clause
that is a bare value 112; `OR`/`XOR` in a where clause 36; a property value
that is not a test literal 28; a null predicate not on a property 22; a
comparison that is not property = literal 15; `OPTIONAL` 12; a composite query
11; a quantifier bound over 64, 21; the rest under 10 each. the two big
families left are the expression evaluator's (`RETURN <expression>`, 685) and
`EXISTS` (195: a nested pattern that is true on the witness graph exactly when
its own witness is a subgraph; the construction applies, the plumbing is not
done)

## the construction

work on the pattern after the 16.7 transformations, so every path alternates
node and edge patterns, every edge pattern is a full one, and every element
where clause is a parenthesized one. `W` returns a partial graph (elements
created so far), a path binding `b` in the sense of 22.2 GR 13 (a word of
symbols with an element each, bracket and subpath symbols included) and a
verdict: witness or unsatisfiable, with the reason

- **node pattern** `( v LE {k: lit, ...} )`: if `v` is already bound (it was
  declared earlier in this path pattern list as an unconditional singleton, or
  `v` is an incoming binding), the binding is to that node, and the pattern's
  requirements are added to it; otherwise a fresh node `n`. requirements:
  the node's label set must satisfy `LE` (22.5), and for each pair its
  property `k` must equal `lit`. `LE` is a propositional formula over label
  names with `%` true (every label set is non-empty, 22.5 NOTE 399) and `!`
  negation: find a model by enumeration over the names mentioned plus one fresh
  name (so `!a` is satisfied by `{ L0 }`), the smallest model first. no model
  (`!%`, `a & !a`) is unsatisfiable. `{k: NULL}` is `x.k = NULL`, which is never
  true: unsatisfiable. two requirements on one node that disagree (`x : a` and
  `x : !a`, two values for one key) are unsatisfiable
- **edge pattern** `-[ v LE {..} ]->` and the six other full forms: a fresh
  edge `e` between the node bound just before and the node bound just after
  (both exist after SR 14), labels and properties as for nodes. direction by
  the edge kind: pointing left makes the left node the destination, pointing
  right makes it the source, undirected makes an undirected edge; for the
  three "or" kinds and any direction pick one proposition of 22.3 GR 3 f iii 2
  D that makes the constraint true: left or undirected picks left, undirected
  or right picks right, left or right picks right, any direction picks right.
  an edge variable bound twice at the same depth binds one edge: under
  DIFFERENT EDGES that is no match (16.4 NOTE 227), under REPEATABLE ELEMENTS it
  is a match only when both occurrences agree on the endpoints
- **concatenation**: `W(PST) · W(PC)`, with one rule from 22.2 GR 16 b: two
  node bindings with no edge binding between them (juxtaposed node patterns,
  or a node before and after an empty quantified group) bind the same node, so
  they merge, requirements combined
- **union** `P1 | P2 | ...`: `W(P1)`. variables exposed by the other operands
  only are conditional singletons and bind null in the record. a multiset
  alternation is a union after SR 10, with a system subpath variable per
  operand
- **quantified** `(P) {m,n}`, `*`, `+`: `m` iterations of `W(P)` chained, the
  first node of iteration `i+1` merged with the last node of iteration `i`,
  each iteration otherwise fresh (`*` has `m = 0`, `+` has `m = 1`). at `m =
  0` the binding is empty and the nodes before and after the group merge (22.2
  GR 16 b again). every variable declared under the quantifier is a group
  variable: it binds the list of its `m` elements
- **questioned** `(P) ?`: zero iterations, variables bind null
- **parenthesized** `( sv = MODE P WHERE cond )`: `W(P)` wrapped in the bracket
  bindings and, with a subpath variable, its begin and end symbols; then the
  mode check of 22.2 GR 16 d on the extracted path of the wrapped binding:
  TRAIL needs no edge bound twice, SIMPLE no node bound twice except first and
  last, ACYCLIC no node bound twice. fresh elements never repeat, so a repeat
  comes only from a variable bound twice, which the merge made one element: a
  repeat under a restrictive mode is unsatisfiable (16.4 NOTE 224: `MATCH
  ACYCLIC (X) -> (X)` finds nothing). `cond` is applied as a requirement, see
  where clauses
- **path pattern list** `P1, P2, ...`: the `W` of each, over one graph, so a
  variable bound in `P1` and `P2` is one element (16.4 GR 7). the multi-path
  binding is the tuple
- **where clauses**: each conjunct of the core is a requirement on an element
  of the binding and is made true by construction: `x . k = lit` sets `k`,
  `x : LE` adds `LE` to `x`'s label constraint, `x . k IS NULL` forbids `k` (a
  property that is null is absent), `IS NOT NULL` gives `k` a value if it has
  none, `x IS DIRECTED` and the source and destination forms are decided by
  the edge's direction, which the edge pattern already fixed: a conjunct that
  contradicts it is unsatisfiable (`<-[ y ]-` with `x IS SOURCE OF y` where
  `x` is the left node). `PROPERTY_EXISTS` is `IS NOT NULL`
- **match mode**: DIFFERENT EDGES holds since every edge pattern gets a fresh
  edge unless a variable repeats, which is handled above. REPEATABLE ELEMENTS
  imposes nothing. the default is ID086 and comes from `--match-mode-default`,
  as for the generator
- **the record** `r(q)` (22.8): each unconditional singleton variable maps to
  its element, each group variable to its list, each conditional singleton
  not bound by the chosen operand to null, each path variable to the path of
  the compressed binding. after `MATCH`, `FINISH` gives no result, `RETURN` of
  variables gives the row of their values, `NEXT` passes the table on
- **the observation**: a `MATCH P FINISH` has one observable, completion, so
  the record also carries `observe`: the same sentence with `FINISH` replaced
  by `RETURN` of every variable the patterns bind (`RETURN 1 AS n` when they
  bind none), and the row it must contain, or 0 rows when no graph matches.
  this is a second query, so it rests on H-observe below; it is what turns
  1,668 completion checks into row checks

### proof of theorem 1

by structural induction on the transformed pattern, showing the witness
binding `b(P)` is in `SLM(P)` of 22.3 on `G(q)`:

- element pattern (22.3 GR 3 b): `b` is one elementary binding `(EPI, GE)`;
  `GE` is a node or an edge as required, and its label set satisfies `LE`
  because the model chosen is, by 22.5 and induction over `LE`, a satisfying
  label set
- concatenation (3 f): `b(PST) · b(PC)` is consistent by 22.2 GR 16: the
  extracted path is a path of `G(q)` because every edge was created between
  the two nodes it sits between (16 a); non-separable node bindings were
  merged (16 b); every edge connects its neighbours (16 c); and the
  directionality constraint of the edge pattern holds because the direction
  was chosen to make exactly the proposition of its kind true (3 f iii 2 D)
- quantified (3 c): `b` is in `S^m`, which is in `TOOMUCH` or `WAYTOOMUCH`,
  and consistent by the chaining and the argument above
- questioned (3 d): `S^0` contains the empty binding
- union (3 h): `SLM(P1) ⊆ SLM(P)`
- parenthesized (3 a): the wrapped binding is consistent, including 16 d,
  which is what the mode check verified
- 16.4: GR 7 holds since every unconditional singleton binds one element by
  the merge; GR 8 holds by freshness; GR 9 holds because each where conjunct
  is true on `b` by construction; the reduced match `REDUCE(b)` is in `SRM`
- 16.3 GR 6: the initial working table of a procedure is the unit table (one
  record, no fields; hypothesis H-unit below), so the loop runs once with an
  empty `COMBINED`; `r(q)` is the `INNER` built from `RM` and is appended; the
  natural join with an empty record is `r(q)`. 14.4 GR 1 and 2 make it the
  working table

for the unsatisfiable verdicts, the same rules show no binding exists on any
graph: a label expression with no model fails 22.5 on every label set; `x.k =
NULL` is unknown for every value (19.3); a forced repeat fails 16 d on every
path; a contradicted direction fails 3 f iii 2 D on every edge. so the match
table is empty on every graph, and 14.4 makes the working table empty

### proof of theorem 2

22.3 defines `SLM` of every subpattern by concatenation, union and bounded
power of finite sets of path bindings over a finite graph; with an unbounded
quantifier the set is infinite in general but the standard requires such a
pattern to be selective or under DIFFERENT EDGES (NOTE 385), and under
DIFFERENT EDGES a binding uses each edge at most once, so iterations are
bounded by the edge count of `G`; a selective pattern is reduced by 22.4 to
shortest or counted paths, which are decided on the finite set. so `SLM`,
`SRM` and the match table are computed by enumeration, and the rest of a core
`q` is relational algebra over that table. the evaluator is this enumeration
written from 22.3 and 22.4 literally; it is the next thing to build

## near misses, as a corollary

for every element the witness uses, one change removes `b(P)` from `SLM(P)`:
drop an edge (16 a fails), flip a directed edge (3 f iii fails), remove a label
the model needs or add one a negation forbids (22.5 fails), move a property
value off its literal (GR 9 fails), make a forced-equal node pair two nodes.
theorem 1 then says the witness row is gone; whether another row appears is
theorem 2's question. so near misses are reported as "the witness row must
not appear" until the evaluator lands, then as full bags. this is xdata's and
sqlfpc's adequacy criterion (every predicate true and false, null included)
restricted to the pattern

## the ir and the setup statements

```
graph:   { nodes: [node], edges: [edge] }
node:    { id, labels: [name], properties: { name: value } }
edge:    { id, source, target, labels: [name], directed: bool, properties }
value:   null | bool | integer | float | string            (test literal classes)
```

every element carries `_id: <id>` as a property, so a returned element is
compared by it, not by the engine's identity (plan: "compare by a canonical
key, a test only id property")

the setup is ordered: nodes first, then edges, so every edge references
nodes that exist. per engine:

- **gql** (any engine with `INSERT`): one statement, nodes first and edges by
  variable: `INSERT ( n0 :a {k: 1, _id: 0} ) , ( n1 :b {_id: 1} ) , ( n0 )
  -[ :T {_id: 2} ]-> ( n1 )`. a variable may be declared again by a later
  insert pattern without a filler (16.5 SR 10 b: the first declaration is the
  defining one, later ones carry no label or property specification). an edge
  with several labels is `:a&b` (`<label set specification>`); an undirected
  edge is `~[ ]~`
- **cypher** (neo4j): `CREATE` with the same shape. neo4j has exactly one type
  per relationship and no undirected relationships, so an edge with two
  labels or none, or undirected, is unloadable there and the row says so
- **turbolay**: the probe's `MemoryStorage::with_graph` takes vertex and
  relationship records (`crates/cypher-engine/src/model.rs`: labels a set,
  one relationship type, directed). same limits as cypher plus scalar values
  only (null, boolean, integer, float, string)

an unloadable graph is a row of the per-engine "not modelled" list, not a
failure of the engine

## hypotheses the oracle rests on

each is a row of the claim, bernot style:

- **H-unit**: a procedure's working table starts as the unit table. to cite
  from the text (see "open")
- **H-load**: after `S(G)` the engine's graph is `G` up to element identity.
  checked by a read-back query per engine (`MATCH (n) RETURN n._id, labels`),
  so it is evidence, not assumption
- **H-id**: `_id` identifies elements and is never named by a generated
  query (the leaf provider's property names are `a`, `ab`, ...: true today)
- **H-ID086**: the match mode default the engine declares
- **H-literal**: a literal of the test classes stored as a property compares
  equal to the same literal in a predicate (19.3 on exact numerics, strings,
  booleans): this is what the engine is being tested on, so a failure here is
  a finding, not a broken hypothesis
- **H-core**: the tier of `q_r` is declared per row: `witness` (theorem 1),
  `bag` (theorem 2, later), `status` (out of core)
- **H-observe**: the engine evaluates a `MATCH` the same way whether `FINISH`
  or `RETURN` follows it. bernot's observability hypothesis in our terms: the
  only observable sorts are result tables and status codes, and `FINISH` has
  no table. an engine that plans the two differently can break it, which is
  itself a finding, so the observation query is reported beside the sentence,
  never in its place

## the export of C

the typed run's `--jsonl` records gain a `vars` field, one object per variable:

```
{"name": "x", "decl": ["edge"], "out": ["edge"], "aliased": [false], "new": [false]}
{"name": "x", "class": ["exact", ["exact"]], "column": ["value"], "need": ["any"], "out": ["value"], ...}
```

the values are gathered from every label of the extracted tree that holds a
slot of the variable (`Context::describe` per rule, `Under::describe` for
types, merged per slot by the pair; `assign_names` now returns which slot got
which name and where every labelled node's slots start). the root label is
not the place: a whole sentence closes every variable, so its label has no
slots. scope gives `need`, `out`, `decl`, `column` (a kind each) and the
`new`/`aliased` flags; types gives `class`: a class name where the variable
has a definition, a list of allowed classes where its uses leave the choice
open. the record is what generation knew; nothing is recomputed from the text

`oracle` reads `vars` when the file carries it and checks the kind it gives
every pattern variable against what the witness bound (`check_vars`): on the
1-slot set 0 disagreements over 1,262 variables, on the 2-variable set
(`sentences/typed-2vars-turbolay-claim-vars.jsonl`, regenerated at 202c76d
with the field, 1,287 rows naming a variable) 0 over the 246 witness records
that bind one. the earlier cached sets predate the field

### parameters

a query with `$b` needs the parameter sent along with it, of a class its site
accepts. a parameter's class is dynamic (4.14.4: it stands wherever a class is
checked), so the rules never store what a site asks of it, and storing it
would be a new fact in the label, which is what blows the run. instead the
export asks the rules: `context::parameter_classes` re-runs the whole context
over the tree once per candidate class with the parameter's label forced to
that class (`Context::with_class`, at every node that is exactly the
parameter, since `<general value specification>` sets the dynamic class
itself), and keeps the classes under which the tree is still accepted at the
top. no new rule, no new label; the cost is one `accepts` per class per
parameter, only on the 42 of 3,834 sentences that have one. the record:

```
"params": [{"name": "$b", "classes": ["exact", "approx"]}]
```

`oracle` gives each parameter a value of the first class its site admits
among exact (`1`), string (`'a'`) and boolean (`TRUE`), as `parameters`, and
both probes send it (turbolay's `ParameterMap`, neo4j's `parameters`). a
parameter whose site admits none of the three leaves the core with the reason:
a list, a record, an element or a temporal value the harness has no way to
pass yet, or a site that admits nothing

what the 1-slot set says (96 parameter sites): 11 sites admit every class
(`LIMIT $b`, `OFFSET $b`, `SHORTEST $b`: the rules do not type a
non-negative integer specification, and `1` is right there), 85 admit nothing.
the 85 are all `VALUE x <type> NOT NULL = $b`: the types rule accepts only a
dynamic value as the initializer of a `NOT NULL` typed `VALUE`, and no literal
(`VALUE x FLOAT NOT NULL = 1.5` is refused at `<boolean predicand>`). so these
sentences exist only because a parameter stands anywhere, and no class is
known for them: a reading in `types.rs` for the soundness track to look at,
and until then they stay out of the core. `examples/params_debug.rs` prints
the admitted classes of one sentence with the rules' trace (`GQL_TRACE=trace`)

## what is built on this branch

- `src/oracle.rs`: the ir, the label expression models, `W`, the record, the
  three emitters, and the tier tagging; `tests/oracle.rs` pins the
  construction on 15 sentence shapes (merges, self loops, unsatisfiable
  labels and modes, directions, quantifiers, unions, simplified patterns,
  paths, chains, the record check)
- `gql-proof oracle <sentences.jsonl>`: parses each sentence with the iso
  grammar, applies the 16.7 transformations, runs `W`, and writes one json
  line per sentence: `sentence`, `graph`, `setup` (`gql`, `cypher`,
  `turbolay`), `expect` (`tier`, `outcome`, `rows`/`row`), and `why` when out
  of the core or unloadable
- the `vars` export in the context command

## runs

- **neo4j** (`tools/engines/oracle_neo4j.py`, the throwaway container): of
  1,132 witness records with a cypher setup, 10 agree and 1,122 are refused
  with a syntax error. neo4j reads cypher, and gql's abbreviated edge `<-` is
  not cypher's `<--`; the 10 are `MATCH ( ) FINISH` shapes. so neo4j is no
  target for the typed set without a gql to cypher rendering, which is out of
  scope; the runner stays for the day one exists
- **turbolay** (`just turbolay-oracle`, the #243 worktree 484d1a72): the first
  run, before observation queries, had every witness record that ran agree
  (1,054, all `FINISH` completions), 1,015 refused in turbolay's known gaps, 0
  disagreements. with observation queries and chains:

  | verdict | records |
  | --- | --- |
  | agree, the witness row among the rows or no rows as expected | 1,337 |
  | disagree | 3 |
  | refused (turbolay's parse and planning gaps, `breakdown.py`'s buckets) | 1,013 |
  | failed at run time (all of the status tier: `PATH [ ... ]`, casts, dates) | 25 |
  | unjudged (status tier, run for the outcome only) | 1,405 |

  two earlier disagreements were ours (a delimited identifier with a doubled
  delimiter, ```` is the name made of one backtick, was not unescaped; fixed,
  with a test). the three left are one finding:

  ```
  MATCH ( x ) RETURN x NEXT FILTER x : ! % FINISH
  MATCH ( x ) RETURN x NEXT FILTER x : ! ( % ) FINISH
  MATCH ( x ) RETURN x NEXT FILTER x IS NOT LABELED % FINISH
  ```

  on a graph with one labelled node turbolay returns the row. by 22.5 SR 2 b
  a wildcard is satisfied by every non-empty label set, and by 2 d its
  negation by none, so the table is empty on every graph (NOTE 399 says every
  label set is non-empty in this edition). turbolay agrees with that reading
  for `x : % & ! %` (no row), so its negated wildcard alone is the odd one
  out: a labeled predicate bug, to file against turbolay with these three
  sentences and the graph `( n0 :L0 { _id : 0 } )`

## open

- H-unit is cited (4.8.2: a root execution context's working table is a new
  unit binding table; 9.x SR 10: a program's incoming working table is the
  unit binding table type)
- theorem 2's evaluator, which also lifts the selective prefix and the near
  miss limits
- value variables: `C` carries their class; the expression evaluator is where
  they get a value
- the probe: turbolay's `zz_gql_proof.rs` loads an empty graph and counts
  rows; it needs to load the ir and serialize rows by `_id`
- engines' bulk loaders instead of `INSERT`/`CREATE` where they exist

## papers worth having locally

the exact problem statement and the nearest constructions. the first four
were checked against a publisher or dblp today, the rest are in
`research/prior-art-2026-10-20.md` or marked

- binnig, kossmann, lo, **reverse query processing**, icde 2007, pages 506
  to 515. the problem as stated here: given `q` and a result, a database
  instance that produces it; a reverse operator per relational operator,
  push based from the result down to the base tables
- binnig, kossmann, lo, özsu, **qagen: generating query-aware test
  databases**, sigmod 2007. the same with cardinality constraints and a
  solver
- olston, chopra, srivastava, **generating example data for dataflow
  programs**, sigmod 2009, doi 10.1145/1559845.1559873. completeness,
  conciseness and realism of example data built operator by operator through
  a pipeline; the closest template for a `NEXT` chain
- khalek, elkarablieh, laleye, khurshid, **query-aware test generation
  using a relational constraint solver** (adusa), ase 2008, pages 238 to 247.
  alloy for query-aware databases
- rigger, su, **testing database engines via pivoted query synthesis**, osdi
  2020. the dual of the witness: pick a row, synthesize the predicate that
  must select it. and **finding bugs in database systems via query
  partitioning** (tlp), oopsla 2020, the metamorphic tier
- chandra et al., **xdata**, arxiv 1411.6704; tuya et al., **sqlfpc**, stvr
  2010: the adequacy criterion for near misses
- francis et al., **cypher: an evolving query language for property graphs**,
  sigmod 2018; francis et al., **gpc: a pattern calculus for property graphs**,
  pods 2023; and the same group's **a researcher's digest of gql**, icdt 2023
  (unverified title and venue, from memory): the formal reading of 22.3
- mannila, räihä, **test data for relational queries**, pods 1986
  (unverified): small databases that separate queries, the small scope idea
  before alloy
- guagliardo, libkin, **a formal semantics of sql queries, its validation,
  and applications**, pvldb 2017: validating an executable semantics against
  engines, the method for theorem 2's evaluator
- mgql (lean) and gpml-conformance (arxiv 2609.23032): executable pattern
  semantics to cross-check the evaluator
- bagan et al., **gmark: schema-driven generation of graphs and queries**,
  tkde 2017: graph and query generation with selectivity control, for the
  exhaustive small graphs later
