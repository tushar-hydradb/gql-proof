# how many typed variables a coverage target needs

> for agents: dated working notes, terse on purpose. people start at the [readme](../README.md)

`research/cutoff-2026-10-21.md` bounds the variables scope needs: no larger
cap covers more past `c*` (3 for productions, 4 for cdrc pairs, measured to 4;
YIELD lists cost two slots per item, so 4 and 6 there). this is the same
argument for types, for a second, smaller cap: how many variables a label must
hold a type constraint on at once. if that is 2 while scope needs 3 or 4, the
type state of a label is raised to the power 2 whatever scope's cap is, which
is what keeps the per-variable growth from compounding (see
`research/complexity-2026-10-22.md`)

## setup

- a variable is **typed** in a label when its entry says something:
  `Need(req)` (a use asked for a kind or class) or `Has(c)` with `c` not
  opaque (a definition gave it a class). `Free` and `Has(opaque)` cost nothing
- the proposed rule, with typed cap `t`: a label with more than `t` typed
  variables first degrades every `Has(c)` to `Has(opaque)`, then is rejected
  if it still has more than `t`. degrading is sound (an opaque value is
  accepted in fewer places, so every tree kept is still valid); rejecting is
  sound (fewer trees). neither can make an invalid tree valid
- `TCov(t)`: the targets (productions, cdrc pairs) used by some valid tree
  under typed cap `t`, with scope's cap fixed at its own `c*`
- monotone: `TCov(t) ⊆ TCov(t + 1)`, for the same reason as scope's: the cap
  only filters labels

## claim

`TCov(2) = TCov(t)` for every `t ≥ 2`, for productions and cdrc pairs. so the
typed cap is 2

## argument

take a valid tree `T` covering target `τ` (one production, or a production at
one occurrence inside another). change `T` outside `τ`'s nodes until no label
holds more than 2 typed variables, keeping it valid and keeping `τ`

1. **value variables become literals.** a reference to a value variable of
   class exact, str or bool, outside `τ`, can be replaced by a literal of the
   same class (`1`, `'a'`, `true`), and one of class dynamic by a property
   reference of a node (`n.k`, which is dynamic). every type check reads only
   the class, so every check that passed still passes, and scope loses a
   reference, which it allows (a variable bound and not used is fine). after
   this, value variables are typed only where `τ` itself mentions them
2. **definitions nobody reads go opaque.** a `LET` or `VALUE` definition whose
   variable is no longer read in a typed way can have its class forgotten: it
   is the degrade step, and nothing reads the class. this is what keeps `LET x
   = 1, y = 2, z = 3` (the LET list recursion, which scope needs 3 variables
   for) inside the cap: all three are opaque
3. **element variables of one kind become one.** two node variables (or two
   edges, or two paths) that are not distinct-required can be made one: scope
   allows it (its collapse step), and types only ever read the kind, which is
   the same. after this, the typed element variables are pairwise of different
   kinds, or distinct-required
4. **equality groups count once.** `x = y`, `SAME`, `ALL_DIFFERENT` and the
   like need their operands of one class or kind, so they are one group; by 3
   the group can be one variable unless its members are distinct-required

what is left in any label is the typed variables `τ`'s own nodes force. a
single production forces at most:

- `source/destination predicate` (`x IS SOURCE OF y`): a node and an edge, 2
- every other expression production: at most one variable of each operand,
  and operands that can be literals are literals by 1; operands that must be
  elements and share a kind are one by 3. comparison `x = y` is covered by
  `x = 1`; `SAME(x, x)` and `ALL_DIFFERENT(x, x)` by one variable if scope
  allows the repeat (to check)

a cdrc pair is a parent production and a child production at one of its
occurrences. the child's variables sit inside one operand of the parent, so
the pair forces the parent's 2 at most, the child's forced variables being
among them (the child of `x IS SOURCE OF y` at the edge operand forces the
edge `y`)

so 2 suffices, and `source/destination predicate` shows 2 is needed

## what this rests on

- the list of places the grammar forces a variable rather than allowing a
  literal must be complete: element variable references, the property source,
  path primaries, `IS SOURCE OF` and `IS DESTINATION OF`, `SAME`,
  `ALL_DIFFERENT`, `PROPERTY_EXISTS`, `IS DIRECTED`, labeled predicates. a
  position that forces three typed variables of different kinds would make the
  cap 3
- step 1 changes the tree's text outside `τ`, so it holds for productions and
  cdrc pairs. a k-path for k ≥ 3 can reach into the replaced reference; the
  bound for k-paths is an upper bound, as for scope
- scope's own distinct-required list (from the scope cutoff) is assumed
  complete. a distinct-required list of typed variables would multiply the
  cap; none is known: the lists scope forces apart (SET, REMOVE, LET, RETURN,
  SELECT, YIELD items) hold bare references or new names, which are untyped
  once 1 and 2 apply

## checking it

the claim is checked the same way scope's was, by measuring one past the
bound: with the typed cap implemented, compare coverage (productions, cdrc
pairs) at `t = 2` and `t = 3` with scope at its cap. any target `t = 3` adds
falsifies the claim and names the missing forced position. that needs the cap
implemented and the 2-variable fixed point to finish, neither true yet
