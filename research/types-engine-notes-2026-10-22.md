# types in the context engine: where we are

working notes for whoever picks this up next (a person or an agent). the plan
this follows is `research/types-engine-plan-2026-10-21.md`; the engine is
described in `algorithm.md` and `src/context.rs`. pictures of everything below:
https://claude.ai/artifact/R8qbDmSoZiQ2f32wr2QVtM (private to tushar)

## state of the code

commits on main, newest first:

- 25a3f18 `src/context/types.rs`: value expression types as a rule under scope,
  `--rule types` in `gql-proof context`, `tests/context_types.rs`
- 5b1a303 `src/context/pair.rs`: the combinator `Typed<A, B>`, `B: Under<A>`
  holds no slots and sees each step of `A` (its inputs, output and link).
  `tests/context_pair.rs`: `Typed<Scope, Unit>` emits exactly scope's grammar,
  5% slower
- 26503e3 `research/cutoff-2026-10-21.md` measured to 4 variables, and the
  `coverage_by_cap` test

the commit after these adds `Label::kids()`, the `census` and `pair_waste`
tests, and this file

what `types.rs` does:

- label: the expression's class (`Ty::Is(class)` or `Ty::Slot(slot, mask)`, a
  deferred class: the variable's, with the classes the sites it passed still
  allow), one `Entry` per scope slot (`Free`, `Need(Req)`, `Has(class)`), a few
  fact bits, and while a production is scanned the children's classes (`kids`)
- the check arms are ported from the old product automaton
  (`product-baseline:src/types.rs`), done at finish over concrete classes
- a deferred class passes wherever an opaque value would; where it would not,
  it is chosen among `DOMAIN` (exact, str, bool, node, edge, path) and the
  choice is written on the variable as a `Need`
- LET and VALUE definitions give their variable `Has(class)` (followed: exact,
  str, bool, dynamic; else opaque); FOR, columns, yields are `Has(opaque)`; a
  return item alias gets its expression's followed class
- `Relinked::new` meets entries along scope's link and checks every input
  slot against scope's view of it, closed (local) slots included. that check
  is what refuses `MATCH (x) RETURN x + 1 AS y`, where x closes at the RETURN
- scope gained read-only `Label::width()` and `Label::view(slot) -> View`

how to run:

- probes and checker test: `cargo test --release --test context_types`
  (about 2 minutes, mostly the generated-trees test)
- trace one sentence: `GQL_TEXT='...' cargo test --release --test
  context_types explain -- --ignored --nocapture`
- label census of the widest nonterminals: `... census -- --ignored`
- `gql-proof context --rule types --slots 1 --phase generate --seeds 2`
  checks generated trees with `verify::scope` and `verify::types`

## numbers (one variable, whole grammar)

- scope alone: 8,054 labels, 77k pushes, fixpoint 39 ms, emission 0.14 s
- scope with types: 81,406 labels, 31.4M pushes, fixpoint 17.6 s, emission
  89 s
- correctness: all 49 probes pass, 410 generated trees, 0 failing either
  checker
- the plan's gate was x3 labels and x3 fixpoint at one variable, so it is
  crossed; 2 and 3 variables were not run

census (`census` test): a label is roughly scope label x class x entries.
`common value expression`: 37 x 22 x 8 possible, 2,046 reached. the hot scans
pair two expression children: `comparison predicate` tries 2,182 x 4,352 =
9.5M pairs for 23,874 finished labels; `simple case` 6.2M. the 8 entries per
variable compound with the cap (512 at 3 variables); the 22 classes do not

fixed already: `datetime subtraction parameters` kept both operand classes
(8,576 labels); it now requires one instant class there, as its only reader
does

## what was explored, and where it landed

this was a conversation between tushar and claude. tushar's ideas and
challenges are marked as his

entries (what a label asks of each variable):

- merge exact unions: two labels equal except one slot's entry (node vs edge)
  are one label "node or edge". exact only when they differ in one slot
- tushar: in `x = y` the two must share a class, so whichever is declared
  first decides the other, and both declared prunes early. this is
  unification. bottom-up, the comparison is always seen before the binders, so
  the rule becomes: record `x : a, y : a, a in S` and let each binder
  intersect `S`, in any order. both variables cannot stay unknown to the top:
  scope makes every reference meet a binder, and every binder fixes a kind or
  class (opaque ones then refuse the comparison)
- tushar: this is type inference, a solved problem; can typescript's be used?
  answer: not typescript (local, bidirectional, leans on contextual typing,
  i.e. inherited types, unsound by design, not a library). the match is
  principal typings (trevor jim, popl 1996), the compositional side of
  hindley-milner: a typing carries assumptions on free variables, discharged at
  binders. and narrowing as in luck (lampropoulos et al., popl 2017): keep
  unknowns symbolic, instantiate only where a constraint forces it. crate if
  needed: `ena` (rustc's union-find with values)
- caveats raised: gql has overloading (exact and approx compare, null and
  dynamic are wildcards, result classes depend on operands), so a typing is a
  small set, and the class is enumerated only where the result depends on it
- direction (agreed in principle, not built): entries become principal
  typings, a partition of the slots into groups each with one set of allowed
  classes. at 3 variables that is 5 groupings times a few sets instead of 8^3

the class itself (22 values at expression nonterminals):

- per-nonterminal grouping: a nonterminal only needs to tell apart what the
  consumers it reaches tell apart (comparison 16 groups, cast operand 15,
  return alias and LET 5, sort key 2, conditions 2). computed once over the
  grammar like liveness, applied by `project` when a label is stored. exact
  only if every parent treats the grouped classes alike in its check and in
  the class it hands up (operators like `+` push distinctions down); this is
  tree automaton minimization. from the bnf: `comparison predicand` is used
  only by the comparison (16 groups), `cast operand` only by cast (15),
  `aggregating value expression` by sort key, return item, select item (6),
  but `value expression` feeds 15 parents and keeps 19. so modest
- join keys: a production scan is a join done as a nested loop. let the rule
  give a key for the partial label and the child label at a position (a
  necessary condition) and pair only matching keys. comparison has one:
  comparability family
- tushar: flowing up is the pain because shared nonterminals must keep the
  union; pass a needs-class down and prune unsatisfiable subtrees. answer
  given: bottom-up never builds an unsatisfiable label, the waste is in
  combining labels where they do not fit; demand down loses sharing (one copy
  per demand, and some parent needs nearly everything anyway); and passing the
  environment down relocates the 8^n rather than removing it. the agreed
  version: sideways information passing (magic sets' term) inside the left to
  right scan, a left sibling's label filtering which right sibling labels are
  tried, without recomputing anything. tushar asked to measure before deciding

proposed order, after the count below: principal typings for entries first
(they cut labels, which is where the cost is), then join keys where cheap and
exact (comparison family, the CASE family), then static class grouping if the
label count still blocks 3 variables. tushar has not decided yet

## the count (decides filtering vs pruning)

`pair_waste` in `tests/context_types.rs` enumerates one full scan of every
production with two or more child nonterminals, at one variable, and splits the
pairs (partial label, child label) into tried, kept by the push, and useful
(some finished label comes out of it: what a perfect filter would keep). 33 s,
3.3 GB peak

```
all productions: 31,166,315 tried, 13,166,107 kept (42%), 5,360,783 useful (17%)

     tried       kept     useful  useful%  production
 9,496,064  4,178,736    931,552    9.8%  comparison predicate
 6,178,793  2,754,089    179,173    2.9%  simple case
 2,637,376  1,137,472  1,137,472   43.1%  simple case/rep1
 1,113,399    123,293    123,293   11.1%  list element list
   957,489    456,905      4,955    0.5%  case abbreviation (NULLIF)
   628,056    278,408     24,298    3.9%  datetime subtraction parameters
   ~313,000   ~138,000   ~101,000   ~32%  each arithmetic operator
comparison with a family key: 2,474,968 tried (26%), 0 useful pairs dropped
```

what it says:

- a perfect sideways filter, or any top-down pruning of this kind, skips at
  most 83% of the pairs: about 6x overall. that bound holds for tushar's
  demand-down idea too, since it can only remove pairs that are useless here
- the useful pairs alone are 5.4M, against 77k pushes for scope in total: 70x.
  so most of the cost is real combinations of labels, not waste. the lever is
  the number of labels (entries as typings, class grouping), and filtering is
  a constant factor on top
- the family key at the comparison is cheap and exact: it keeps 26% of pairs
  (3.8x fewer) and drops nothing useful. the oracle there keeps 9.8%
- the big filterable spots are the CASE family: simple case 2.9% useful,
  NULLIF 0.5%. arithmetic sits near 32%, little to gain. lists and when
  operand lists are already filtered exactly by the push
- caveat: "useful" counts pairs leading to any finished label, including ones
  emission later finds unreachable from the start, so the true oracle is a bit
  smaller

## after the count

- `typing_estimate` (merge today's labels that differ only in what they ask of
  the variable, at one variable): labels 81,406 → 24,795 (÷3.3, 3.1x scope),
  pushes 31.2M → 2.45M (÷12.7). so typings beat any filter (≤ ÷6)
- types at 2 variables: no fixed point in 600 s (354k labels and rising,
  2.75 GB); scope alone is 26k labels in 0.63 s
- tushar: the goal is a scaling factor that does not grow with the number of
  variables, at least not exponentially. answer: exact labels are exponential
  in the variables they describe at once, in the worst case; the way out is to
  bound how many are typed at once. `research/types-cutoff-2026-10-22.md`
  argues a typed cap of 2 loses no production or cdrc pair (Has past the cap
  degrades to opaque, Need past it is rejected). agreed as the direction
- `research/complexity-2026-10-22.md`: time and space of fixpoint, emission
  and generation, the factors and how they multiply (per-variable states of
  scope and types multiply inside the power; pushes are labels squared at
  binary productions), checked against the measurements

## open
- not done from the plan: `purdom --rules all` with types and
  `Verifier::with_types()`, `cover --types` on the #261 corpus, neo4j and
  turbolay reruns, widening the followed classes, readme and doc updates
- the cutoff argument (`research/cutoff-2026-10-21.md`) has no
  distinct-required list for types yet; with equality groups, a group of
  variables is the new unit to count

## working rules from tushar

- no blind long runs: instrument, small budgets, bring numbers when stuck
- never rewrite code with sed or python string replacement; use ast-grep or
  an edit tool
- prefer ecosystem crates over hand-rolled utilities
- commits skip signing (`git -c commit.gpgsign=false`)
- docs wrap at 80 columns; nothing iso-owned or pdf-derived in the repo
- anything posted under tushar's name follows his voice (lowercase, no
  trailing periods, `-` lists); outward posts need his confirmation
