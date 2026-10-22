# time and space of the context engine, and how the factors interact

the engine is `src/context.rs` (see `algorithm.md`); the rules are scope
(`context/scope.rs`) and types under it (`context/types.rs`,
`context/pair.rs`). this derives the cost of each phase from the code, names
the factors, and checks the model against what was measured. the types cutoff
it leans on is `research/types-cutoff-2026-10-22.md`

## the pipeline

```
grammar ──fixpoint──▶ labels per nonterminal
          (scans)     + kept partial layers
                              │
                          emission (backward passes)
                              ▼
                      emitted grammar ──purdom──▶ trees
                      (one nonterminal per reachable label)
```

## names

- `G`: the base grammar (iso bnf desugared). with no rule the engine sees
  1,266 labels (one per nonterminal), emits 1,207 nonterminals and 2,139
  productions from the program, and does 9,377 pushes (one per symbol of every
  production)
- `k`: scope's slot cap, the most variables one label holds
- `L_N`: the labels of nonterminal `N` at the fixed point; `L = Σ L_N`
- `P_{p,i}`: the partial labels production `p` holds after position `i`
- `t_push`: the cost of one push (link the slots, meet the entries, check);
  grows a little with label size: 0.5 µs at k = 1, 2.3 µs at k = 3 for scope

## fixpoint: time

a production is scanned left to right; at position `i` every partial label
meets every label of the child there, and the distinct results are kept. the
scan is semi-naive: kept partials meet only new child labels, new partials meet
all of them. so across all rounds each pair (partial, child label) is pushed
exactly once, and the number of rounds drops out:

```
pushes = Σ_p Σ_i  |P_{p,i}| · |L_{child(p,i)}|          (each pair once)
T_fix  = t_push · pushes  +  finishes  +  rounds · (bookkeeping)
```

checked: one full scan per production, counted independently
(`pair_waste`), gives 31.17M pushes; the engine's own count over 52 rounds is
31.37M

what the sum is made of:

- a **chain** production (one child, like `numeric primary ::= value
  expression primary`) costs `|L_child|`: linear, cheap however big
- a **binary** production (`a + b`, `a = b`, `f(a, b)`) has `P_{p,1} ≈
  |L_a|`, so it costs `|L_a| · |L_b|`: the square of the label count. these
  dominate: at k = 1 with types, 5 productions are half the pushes
- longer productions are bounded by their partial layers, which deduplicate:
  `|P_{p,i}| ≤ min(Π_{j<i} |L_j|, the label space)`. the CASE family keeps
  folding into one result class, which is what keeps it bounded

so, roughly, `pushes ≈ Σ_binary |L_a| · |L_b|`: **time is quadratic in the
labels of expression nonterminals**

## labels: where the factors meet

a label at an expression nonterminal holds scope's part (per variable its
need, out, decl, column, flags; a few flags for the subtree), the class, and
per variable a type entry. variables are slots up to renaming, so a label's
variables are a multiset, not a tuple. with `σ` scope states per variable,
`e` type entries per variable, and `C` classes:

```
L_N(k)  ≈  F_N · C_N · Σ_{m ≤ k}  multisets of m variables over σ·e states
        =  F_N · C_N · Σ_{m ≤ k}  C(σe + m - 1, m)
        ≈  F_N · C_N · (σe)^m / m!   for the largest m a subtree reaches
```

this is how the factors interact:

- **scope's and types' per-variable states multiply inside the power**: one
  variable has `σ · e` states, not `σ + e`. adding a variable multiplies the
  labels by about `σe / m`
- **the class multiplies once**, not per variable
- **squaring at binary productions doubles the exponent**: pushes go as
  `C² · (σe)^{2m} / (m!)²`
- in `k` this is polynomial of degree `σe` (because of the multiset), but the
  degree is large; in practice each variable is a factor of `σe / m`

measured, scope alone (`e = 1`, `C = 1`):

```
 k   labels   ×      pushes      ×      ×² of labels   fixpoint
 1    8,054          77,219                             0.04 s
 2   26,236  3.26    768,539    9.95   10.6             0.63 s
 3   70,364  2.68  5,169,854    6.73    7.2            12.0 s
 4  180k     2.56                                     266 s
```

labels grow by `≈ σ/m` per variable (`σ ≈ 5-6`), pushes by the square, as the
model says

measured, types under scope, k = 1: labels ×10.1 over scope, pushes ×406. the
square of 10.1 is 102; the remaining ×4 is the partial layers: a partial label
keeps every child's class until finish (`kids`), so `P_{p,1}` at the
comparison is 2,182 but `P_{p,2}` is 125,736 (`C²` before the check folds it).
at k = 2 the fixed point did not finish in 600 s (354k labels and rising,
widest `cast specification` with 12,784)

## fixpoint: space

```
S_fix = Σ_N |L_N| · size(label)                  labels
      + Σ_p Σ_i |P_{p,i}| · 3 · size(label)      kept layers, back pointers
```

kept layers dominate where partials hold children's classes: 125,736 at one
position at k = 1 with types, against 2,912 for scope at k = 3. each kept
partial stores itself, the partial before it and the option taken (labels are
cloned, not shared). measured peak: scope at k = 3, 406 MB; types at k = 2,
2.75 GB when stopped

## emission

each production's layers are kept from the fixpoint. for each production, one
backward pass from the complete partials to the labels reached (one push per
pair again), and a forward pass per wanted option (one push per partial); a
fallback pass for labels reached late, memoised by how many are reached

```
T_emit ≈ (2 + F) · pushes · t_push        F: fallback passes per production
|N_e|  = labels reachable from the start   (≤ L)
|P_e|  ≈ one instance per (parent label, production), plus one per wanted
         option per production
```

measured, emission costs about 5 fixpoints: scope k = 3, 66 s against 12.8 s;
types k = 1, 89 s against 17.6 s. so `F ≈ 3`

## generation

purdom over the emitted grammar: shortest derivations and reference lengths are
a fixed point over `P_e`, then covering trees. linear in the emitted grammar
times the tree height `h`:

```
T_gen ≈ O(|P_e| · h)
```

measured: scope 1.6, 5.5, 23 s at k = 1, 2, 3; types 13.3 s at k = 1 (40k
emitted productions)

## all together

```
per variable:   σ (scope) × e (types)          ─┐
per label:      C (class) × multiset of m vars  ├─▶ L_N
per production: |L_a| · |L_b| (binary)          ├─▶ pushes
per partial:    × C per child class kept        ┘     │
                                    T_fix, and T_emit ≈ 5 T_fix
space:          L + Σ partials (× 3 labels each)
output:         |N_e| ≤ L, |P_e| ─▶ T_gen linear
```

## what each fix changes in the formula

- **cutoff** (proved for scope): `k` is a constant, 3 or 4
- **principal typings**: `e` becomes a few sets per variable, plus equality
  groups. estimated at k = 1 by merging today's labels: labels ÷3.3, pushes
  ÷12.7
- **typed cap `t = 2`**: the types part of the power, `m` becomes `min(m, 2)`.
  types then multiply scope by a constant as `k` grows
- **class grouping per nonterminal**: `C` becomes its consumers' groups;
  comparison predicand 22 → 16
- **join keys**: `|L_a| · |L_b|` becomes `Σ_key |L_a(key)| · |L_b(key)|`;
  measured at the comparison, ÷3.8 with nothing useful dropped
- **check at push, not finish**: removes the `C` per child kept in partials,
  the ×4 between labels squared and pushes

with typings and the typed cap, the label count becomes

```
L_N(k) ≈ F_N · C_N · Σ_{m ≤ k} C(σ + m - 1, m) · T(min(m, 2))
```

where `T(2)` is the type states of two variables (a few sets each, or one
group). the types part is then a constant factor over scope at every `k ≥ 2`,
and the per-variable growth is scope's own `σ / m`. an estimate, not a
measurement: at k = 3, scope's 70k labels times 3 to 6 is 200k to 400k labels,
and pushes times 10 to 36 is 50M to 190M, a few minutes of fixpoint before join
keys. the plan's gate at k = 3 is 350k labels and 60 s

## what stays exponential, and why

a label must describe exactly which combinations of its variables' states
occur, because the totality proof needs exact labels. a set of combinations
over `m` variables can be any relation, so in the worst case it takes `(σe)^m`
labels. the ways out are the ones above: bound `m` (the cutoffs), shrink the
per-variable states (typings), and represent correlations structurally
(equality groups) instead of as rows. dropping exactness (a separate state
per variable, joined independently) would be linear in `m`, but it emits labels
with no valid tree, and the generator would then build invalid trees
