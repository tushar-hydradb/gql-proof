# how generation works, and where context makes it expensive

> for agents: how the pipeline computes and what it costs, terse on purpose. people start at the [readme](README.md)

a high level walk through the pipeline, what each step computes and costs, the
two ways we tried to add context (scoping, types), and measured numbers. written
to find where to cut compute

## 1. the pipeline

```
iso bnf.xml
  -> desugared cfg          src/cfg.rs: [..], {..}, ... become groups
  -> refine (syntax rules)  src/refine.rs: 3 syntax rules + the claim, automata
  -> [context]              scoping and types: the expensive part, sections 4-5
  -> purdom analysis        src/purdom.rs: shortest subtrees and contexts
  -> purdom covering trees  every production at least once
  -> targeted trees         src/purdom/targeted.rs: every cdrc and k-path target
  -> verify each tree       src/verify*.rs: independent checkers, all must pass
```

sizes: the iso grammar desugars to 1266 nonterminals and 2658 productions, 2139
of them reachable from `<GQL-program>`. targets: 2658 productions, 3416 cdrc,
6956 3-paths

## 2. purdom (production coverage)

input: a cfg and a start symbol. output: a small set of trees that together use
every production

- phase 1, shortest subtrees: `len[nt][r]`, the smallest tree of each
  nonterminal within remaining height `r`. a bottom-up fixpoint over the
  grammar, `O(productions x height)`
- phase 2, shortest contexts: for each nonterminal, the cheapest tree from the
  start with a hole where that nonterminal goes, placed with room `r`. top-down
  over the same tables
- covering: build trees one by one. at each node pick the production that
  reaches the most still-unused productions within budget, else the shortest
  one. a production is used once its tree is emitted. trees stay under the
  reference height (the tallest of the per-production minimum heights) and the
  reference length (zheng and wu: the longest of the per-production shortest
  covering sentences)
- cost: tiny. the whole thing is linear in the grammar times the height. on the
  plain iso grammar it is milliseconds

## 3. cdrc and k-paths (havrikov, kampmann, zeller algorithm 1)

targets are counted on the base grammar, by occurrence (a position on a right
hand side):

- cdrc target: production `p` of `X` used at occurrence `o` of `X`
- k-path: a chain of k occurrences along a root path of a tree (groups skipped)

for each target not yet covered, longest first:
1. its shortest tree = shortest context down to the first occurrence of the
chain + the chain itself, fixed + shortest subtrees everywhere off the chain
(the phase 1 and 2 tables again)
2. emit it, and drop every other target it happens to cover
3. out of reach at the height cap: tried again at 4x the height, reported as
needing more height or never

cost: per target, one walk down the chain plus table lookups. thousands of
targets, each cheap. no search

the important property: purdom, cdrc and k-paths never search. they read
precomputed tables of "shortest subtree of nonterminal N" and "shortest context
around N". anything that makes the grammar bigger makes those tables bigger, but
the algorithms stay table lookups

## 4. context, try 1: the product grammar (`product-baseline` branch)

idea: compile each rule into the grammar, so the tables above only contain valid
trees. every nonterminal is copied once per state a rule tells apart:

```
copy = (nonterminal, inherited state, synthesized state)
state = set of facts, per variable name: bound as node/edge/path/value,
        declared, used, ...
```

a production `X -> A B C` in a context becomes one copy per combination of its
children's states that the rule accepts. the children's states multiply

- scope with 2 names: 1.7M productions (from 2658), 5 minutes, 2.3 GB, and
  purdom then runs on that grammar
- scope + types with 2 names: same order; every generated tree valid, sound on
  the #261 corpus
- 3 names: never finished in 4 hours. every fact is per name, so a third name
  multiplies every state set

## 5. context, try 2: the lazy engine (`src/context.rs`, uncommitted)

idea from raptor (round based transit routing): do not materialise the product.
compute, per nonterminal, only the labels its subtrees can actually have, in
rounds, and keep one smallest witness each

- a label is synthesized only: what the subtree needs from outside (references),
  what it declares or binds, flags (aggregates below, a nested query below, ...)
- variables are slots, not names: canonical order, so renamings are one label.
  names are given after generation
- a production is scanned left to right: the partial label after each child
  meets each label of the next child (`push`), deduplicated before the next
  position
- rounds: a production is rescanned only when a child gained a new label
- emission: one nonterminal per label reachable from the start; for each
  (production, position, child label) one smallest instance, so the emitted
  grammar is linear in labels, not labels times child labels. then purdom, cdrc
  and k-paths run on the emitted grammar unchanged

cost model, where `L(N)` is the labels of nonterminal N and `P(p, i)` the
partial labels after position i of production p:

```
fixpoint:  sum over productions p, positions i of
           P(p, i) x L(child i) x fan-out of push
emission:  for every reachable label of every nonterminal,
           for every production of it:
           a backward pass of the same size as the forward one
```

### measured (value expression alone, scope rule, `just context-sweep`)

```
             fixpoint          partials  emit                  emitted
slots labels pushes   time     max       pushes  time          prods
1     11,700 0.6M     0.2 s    498       9M      2.2 s         12,434
2     44,046 9.0M     4.7 s    1,920     2,356M  898 s         52,211
3     130,645 86M     86 s     10,880    -       > 9 min, cut  -
```

- with the engine and no rule, the whole grammar is 8 ms: the engine itself is
  cheap
- labels grow about x3.5 per slot, pushes x10-15 per slot: the partial labels at
  one position grow with the product of what the children before it carry
- at one slot there are already 11,700 labels: most of the label space is flags
  (aggregate below, query below, tokens, use flags), not variables
- emission is the wall: it redoes a backward pass per reachable label, x260 from
  1 to 2 slots

### why it grows

a label must say everything any ancestor might check. an expression deep in the
grammar does not know if it will end up under a sort key (no nested query
allowed), under a return item (aggregates allowed), under a graph pattern
(references must be the pattern's own), so it carries all of it up. every
independent thing it carries multiplies the labels of every nonterminal above
it, and a production's partial labels are roughly the product of its children's.
the product grammar had the same growth from the inherited side; the lazy engine
moved it to the synthesized side

## 6. what both tries assume

both put context before generation: the generator only ever sees valid trees, so
coverage counts over valid trees and an unreachable target is proven infeasible.
that guarantee is what costs. purdom/cdrc/k-path only need, per target, one
shortest valid tree; both tries compute every label of every nonterminal to get
there

## 7. generate, then repair (your idea)

```
for each target (production, cdrc, k-path):
    # tables of sections 2-3, milliseconds
    t = shortest tree for the target, syntax only
    loop:
        v = first rule t breaks (the checkers in src/verify/)
        if none: emit t, done
        # local edits that make v pass, the target's chain untouched
        fixes = repairs(t, v)
        if none: target is unknown (not proven infeasible)
        fan out over fixes, smallest first
```

the fixes the checkers' violations suggest, per rule family:

- unbound reference (20.12 SR 8): rename to a variable bound before it, of the
  right kind; or insert a binder before it (`LET x = ...`, a node pattern in an
  enclosing MATCH): xsmith's lifting
- name declared twice, field twice, column twice: rename one occurrence fresh
- kind mismatch (edge used as node): rename to a variable of that kind, or
  change the declaration's pattern
- type class mismatch: replace the operand subtree with the shortest subtree of
  the wanted class (a literal), or wrap it in a cast
- aggregate where none may be, nested query in a sort key: replace that subtree
  with its shortest sibling alternative

where it fits well:
- the cost is per target, and most trees are already valid or one fix away: no
  global table of labels
- the checkers already exist and say which rule and which node, which is exactly
  what a fix needs
- names come for free: a fresh name is a rename, no slots or label space

what it gives up, or needs care:
- infeasibility is no longer proven: a target the search cannot fix is
  "unknown", with the rule that blocked it. bardin et al. (icst 2015) report
  covered / infeasible / unknown, which is the honest version
- a fix can destroy the target (the chain) or break another rule: the search
  must keep the chain fixed and re-check after each fix; fan-out bounds the work
  per target
- termination: each fix must make progress (fewer violations, or a smaller
  tree), or the loop can cycle
- the shortest syntactic tree may need many fixes when a smarter tree would need
  none; generating with a few cheap biases (prefer productions that bind before
  they reference) cuts the repairs

a middle ground: keep the cheap, local rules in the grammar (the 3 syntax rules,
the claim, already fast), and repair only the context rules (scope, types),
which are the ones that multiply

## 8. numbers to beat

- syntax only, all criteria (`purdom --rules syntax --cdrc --k 3`): 0.6 s, 45 MB
- product grammar, scope + types, 2 names: about 5 minutes per run, 2.3 GB
- lazy engine, scope, value expression alone, 2 slots: 5 s fixpoint + 15 min
  emission
