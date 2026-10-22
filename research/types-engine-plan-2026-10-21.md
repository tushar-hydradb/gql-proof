# plan: static types in the context engine

> for agents: dated working notes, terse on purpose. people start at the [readme](../README.md)

written by a planning teammate from the code (no edits), for review before any
work starts. scope-only numbers it builds on are in
research/totality-2026-10-21.md

## 1. composition: a dependent product, not a bigger scope label

a combinator `context::pair::Typed<A, B>` with label `(A::Label, B::Label)`. `B`
implements `Under<A>`: it adds no slots, keeps one entry per slot of `A`'s
label, and runs after `A` on each step, seeing `A`'s output label and link

```rust
trait Under<A: Context> {
    type Label: Clone + Ord + Debug;
    fn empty(&self, node, a: &A::Label) -> Self::Label;
    fn push(&self, node, pos, a_partial, b_partial, a_child, b_child,
            a_out: &A::Label, link: &Link) -> Vec<Self::Label>;
    fn finish(&self, node, a_partial, b_partial, a_out, link)
        -> Vec<Self::Label>;
    fn facts(&self) -> Vec<FactSpec>; fn project(...); fn show(...);
}
```

for each `(a_out, link)` of `A`'s push or finish, the combinator:
- relinks `B`'s per slot entries through `link`, the arithmetic of `relink`
  (context.rs): inputs on one output or one step local slot meet, locals are
  checked then dropped
- calls `B` with `A`'s output
- keeps labels canonical: `Draft::done` sorts by scope's `Var` only, so slots
  with equal vars and different type entries are re-sorted stably by `B`'s entry
  and the permutation goes into the link. `A`'s label is unchanged, equal vars
  being interchangeable

facts merge (scope uses bits 0-23 and 32-46, types gets 48-63, asserted
disjoint), `project` splits the masks, `top` and `spells` are `A`'s

why not grow scope's `Var` and `Label`:
- scope stays its own baseline: `--rule scope` and its tests keep their meaning
- identity is already in `Link`, so types never touches `meet`, `joined`,
  `discharge` or `merge`
- types still sees what it needs: `a_out` gives each slot's kind, the link which
  reference met which binder. scope only gains read-only accessors

## 2. what a type label holds

```rust
// vars.len() == scope's slots
struct Label { class: Ty, aux: u16, vars: Vec<Entry> }
// Class: the 20 classes
enum Ty { None, Is(Class), Slot(Slot) }
// Req: Node | Edge | Element | Path | Value(Class)
enum Entry { Free, Need(Req), Has(Class) }
```

- **the class of a reference is deferred** (`Ty::Slot`): a reference does not
  guess its class. category sites and parentheses pass it through, as the old
  `site` passed `Opaque` and as `verify::types` reads categories. only an
  operator, a function or a strict site resolves it, writing `Need(c)` on that
  slot: `x + 1` is `Need(Value(Exact))`, `x.k` is `Need(Element)`, one label not
  two, `x = y` at most 5 pairs. `RETURN x`, `RETURN x AS y`, `ORDER BY x` never
  fan out
- **meeting a binder**: after each step every output slot is reconciled with
  scope's kind. node, edge or path: the entry is `Free` or a fitting `Need`. out
  value: `Has(c)`, set by `let variable definition` and `value variable
  definition` from the `=` expression's class on the slot scope marks new; other
  value binders (FOR, columns, YIELD, CALL) get `Has(Opaque)`, the old reading.
  two needs narrow like scope's `narrow`, `Has(c)` meets `Need(Value(c'))` only
  if `c == c'`, `Has(Opaque)` meets only `Free`
- **value classes followed** start at {Exact, Str, Bool}; any other class a LET
  defines is `Has(Opaque)`, which is sound. widened only within the gates
- **the old tricks**:
  - opaque: kept (value query, element_id, closed record fields, graph and table
    references, DURATION of a record, value variables not followed)
  - UNREAD: becomes a liveness fact (bit 48) cleared at statement boundaries;
    `project` drops the class where it is dead
  - NARROWED: kept, CASE, NULLIF and COALESCE results exact or null, one folded
    result class in `aux`
  - OPERAND: synthesized instead of inherited, a 4 bit mask of acceptable
    operand classes {Exact, Str, Node, Edge} from the when operands, ANDed up
    the list, checked where the simple case operand meets it
  - the other carried facts (MODIFIED, SAW_NODE, SAW_EDGE, ORDERING, YEARS, set
    function kind, IMMATERIAL, ANY_TYPE, NOT_NULL) become `aux` bits cleared by
    their consumer
- **liveness, honestly**: it will not cap the class at `value expression`, since
  comparisons read it and liveness is a union over occurrences. it does at
  statements, return items, value types outside a CAST and the old UNREAD set.
  the real caps are the deferred class, the small value class set, and one class
  per partial label
- **estimate**: 3 to 6 classes per expression position on top of the deferred
  one; typed categories x2-3, `value expression` about x6, statements about
  x1.2. at 3 variables, 70k labels becomes about 200-350k

## 3. check sites

two operand checks at the push of the second operand, single node checks at
finish:
- leaves (finish): literals (time and datetime zoned by text, defaults from the
  leaf provider during the fixed point, duration by `duration_text`),
  constructors, general value specification, datetime, length, string, byte,
  list and binary set functions
- sources (finish): binding variable reference is `Slot(0)`; property reference
  is dynamic on a node, edge or dynamic source, opaque otherwise, and puts
  `Need(Element)` on a deferred source; value query and element_id opaque;
  DURATION of a record opaque
- categories (finish): the primaries and boolean predicand pass deferred and
  opaque through; record, node and edge reference expressions strict; graph and
  table references and object expression primary dynamic only; FOR source a
  list; search condition boolean
- modified (push, finish): factor, duration factor, boolean factor and test
- binary operators (push of the second operand): arithmetic, the concatenations,
  datetime plus or minus duration, duration arithmetic, AND, OR, XOR, modulus
- predicates: comparison (`comparable` at the push, ORDERING carried),
  normalized, directed, node and edge reference, all_different and same, the
  rest boolean; DURATION_BETWEEN operands of one instant class
- CASE family (push): folded narrowed results, NULLIF comparable, operand masks
- CAST and value types (finish): target class and flags, then castable, NOT
  NULL, immaterial, dynamic
- aggregates (finish), statements (finish): typed value initializer assignable,
  sort key scalar, let value expression, aggregating value expression, value
  initializer, definitions set `Has`
- global (finish): a call with an opaque operand, or only a null one, rejects

helpers (fits, comparable, combine, castable, assignable, arithmetic, zoned,
duration_text) come verbatim from product-baseline:src/types.rs

## 4. verification

1. generated trees: `gql-proof context --rule types --phase generate` checks
   `verify::types` beside `verify::scope`, counted apart; `purdom --types`
   builds the pair and verifies with `with_types`. gate: 0 failures on seeds 0-7
   and with `--cdrc --k 3`
2. probes: tests/context_types.rs ports the baseline's tests/types.rs (accepted
   if any verified tree is), both lists kept, plus `LET x = 1 RETURN x + 1 AS y`
   and `LET x = true FILTER x RETURN 1 AS y` accepted, `MATCH (x) RETURN x + 1
   AS y`, `FOR x IN [1] RETURN x * 2 AS y`, `LET x = 'a' RETURN x * 2 AS y`
   refused, and a generated trees test
3. the #261 differential: `cover --types` ported, the automaton never accepting
   what the checker refuses (hard gate); "both" should rise above the baseline's
   6,528 now LET classes are followed, "only the checker" fall below 3,069
4. combinator regression: `Typed<Scope, Unit>` gives scope's exact labels and
   grammar

## 5. measurement gates

- `Typed<Scope, Unit>`: same labels, fixed point and emission within +15%
- types at 1 variable: labels at most x3, fixed point at most x3
- at 2: labels at most x4, fixed point at most x5
- at 3: labels at most x5 (350k), fixed point at most 60 s, emission at most 5
  min
- iterate with `--start "value expression"` and the census

stop: if 2 variables pass x6 labels or x10 fixed point time, stop, report the
census and push fan-out per definition, and shrink before resuming, in order:
value classes to {Exact}, `Need(Element)` to node only, resolve the deferred
class only at strict sites, value variables opaque again. no 4 variables before
3 passes

## 6. steps

1. scope-only numbers at 1 and 2 variables recorded
2. the combinator (src/context/pair.rs), and the `Unit` regression test
3. read-only scope accessors, scope tests unchanged
4. src/context/types.rs: helpers, label, deferred class, binders, leaves and
   sources, categories, operators, predicates, CASE, CAST, aggregates,
   statements, probes after each group
5. CLI: `--rule types`, the types check in generate, the 1/2/3 variable gates
6. `purdom --types`, seeds and `--cdrc --k 3`
7. `cover --types` on the #261 corpus
8. widen the value classes (approximate, temporal, then FOR and columns) only
   while the gates hold, each reading in the module doc
