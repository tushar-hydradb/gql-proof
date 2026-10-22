# path pattern minimums (16.7 SR 8, 16, 20; 16.12 SR 1-4; 16.4 SR 12)

the second family from the static semantics handoff, 230 of the 238 sentences
turbolay refused as invalid on our side after `EXISTS { FINISH }` went.
branch `tushar/exists-table`, after the merge of its first two commits

## the rules, from the text

16.7 SR 7 and 15 define a minimum path length and a minimum node count bottom
up: a node pattern (0, 1), an edge pattern (1, 0), a concatenation sums (one
node less where two node patterns touch), a union or multiset alternation
takes the minimum, a quantified primary multiplies by the lower bound, a
questioned primary is 0, parentheses pass through. SR 14 comes first: an edge
pattern under a quantifier or `?` is parenthesized, and in any path term an
edge pattern not preceded or followed by a node pattern gets an implicit empty
one. so a bare `<-` counts two nodes and `( <- ) ?` none. 16.11 SR 2
normalizes quantifiers (`*` is `{0,}`, `+` is `{1,}`, `{n}` is `{n,n}`, a
missing lower bound is 0). then SR 16: a path pattern's expression has node
count > 0; SR 20: so has a parenthesized expression with a subpath variable;
SR 8: what a quantifier or `?` repeats has path length > 0

16.12 SR 5-6 rewrite a simplified expression `<-/ ... /-`: wrapped in
parentheses; a label, negation, conjunction or direction override becomes one
edge pattern; a concatenation two edges in one term; a union or alternation
one per operand; `S q` becomes `( edge ) q`, `S ?` becomes `( edge ) ?`,
`( contents )` a parenthesized expression. so a simplified node maps onto the
path grammar one to one, and `<-/ a ? /-` has no node. SR 1-4: a negation,
direction override or conjunction holds no concatenation, quantifier, `?` or
multiset alternation, an override no override

16.4 SR 12: under DIFFERENT EDGES (given or ID086's default) a selective path
pattern is alone in its list. 16.6 SR 4 makes a pattern selective by the
search prefix it simply contains, so KEEP's prefix does not count (reading)

readings recorded in the code: the automaton carries "at least one" (two
booleans), the checker computes the integers; a non-ASCII decimal digit in a
bound counts as nonzero (the generator spells U+0663 only); 16.11 SR 3 a i (an
upper bound is not 0, and `{0}` is `{0,0}` by SR 2 c) rides along, SR 3 a ii
(upper below lower) stays open. 16.7 SR 9 (no quantified primary directly
under a quantified primary, at the same depth) came in after the first
turbolay run showed it reachable (`TRAIL ( <- + ) +`). 16.12 SR 1 and 4 are
read with NOTE 255 and 257: a negation or conjunction becomes a label
expression, so a direction override inside one (`a & < a`) is a non-label
construct, as turbolay reads it too

## where it lives: three automata in `src/refine.rs`

`PathMinimums`: every path node synthesizes one of NODES / NO_NODES and one
of LEN / NO_LEN, exhaustive so "every operand" reads as "no child has
NO_NODES" under the union of children and "some operand" as "a child has
NODES". a bare edge keeps an EDGE fact until its factor (implicit nodes) or
its quantifier (parentheses) consumes it. a bound's zeroness comes from the
digit tokens of its `<unsigned integer>`, computed only where a bound asks for
it (an inherited WANT fact), so numbers elsewhere are not copied. facts clear
at the path pattern, a filler, a parenthesized WHERE and the graph pattern.
`SimplifiedShape`: being below a negation, conjunction or override is an
inherited context, and the forbidden nodes are refused in it outright
(`rejects`), nothing synthesized; 16.7 SR 9 is the same shape inside
`PathMinimums` (an `in-quant` context from a quantifier's primary down to the
end of its depth of matching). `SelectiveAlone`: a search prefix other than
ALL marks its path pattern selective, the list counts its patterns, the graph
pattern decides with the match mode or ID086. all three are bookkeeping: their
copies are not coverage contexts. `FIRST_FREE_FACT` moved from 12 to 32

the checker twin in `src/verify.rs` (`minimums`, `term`, `simplified`,
`lower_bound`, `bound_value`, `selective`) computes the integers from the
text, with SR 14's insertions done on the flattened factor list of a term and
16.12's rewrite on virtual factor lists. `tests/refine.rs` lists the rules and
probes each with skeleton trees; its two differential tests (random trees from
the base grammar: automaton accepts iff the verifier reports none of the
rules; random trees from the refined grammar: the verifier reports nothing)
passed on the first full run

## the graph did blow, once

the first version synthesized the 16.12 facts and let a union's repetition
group accumulate every subset of the minimums: a simplified term had 10
states, its repeated operands 15, and `simplified path union ::= term | term
{ | term }...` fanned out to 1,500 productions. the refined grammar went from
5,264 to 11,633 productions. two cuts brought it back: the group folds the
minimum as operands come (it is associative), and 16.12 became an inherited
context so nothing is synthesized for it

a third cut came from the first long run: the inherited contexts had gone
down into everything below a negation or a bound, so the identifier characters
of a label name and the digits of a number had `^inside` and `^want` copies,
and the cover phase counts every copy's production as a target (that is how
copies have always counted: `<general quantifier@unguarded>` was a target of
its own before). the contexts now stop at the simplified and integer
nonterminals

a fourth lesson came with 16.7 SR 9: as a synthesized fact ("a quantified
primary below") it doubled every path nonterminal's states and the unions
fanned out again (10,362 productions); as an inherited context it costs 600

```
                          before (exists-table)      first version         final (with SR 9)
refined grammar           2,460 nts  5,264 prods     2,932   11,633        2,972   7,834
scope, 2 slots            32,406 labels 0.97 s       34,272  2.4 s         34,941  1.3 s
types, 1 slot             33,923 labels 2.49 s       34,896  3.2 s         34,580  2.6 s
types, 2 slots, cover     547 s, 1.27 GB             (not run)             559 s, 1.57 GB, fixpoint 47 s
```

what is left of the growth: `path pattern union` and `path multiset
alternation` at 216 productions each (operands with 3 minimums times the
older rule's guarded-or-not, cubed), and the path family's 3 to 6 copies

## turbolay's ID086

turbolay's default match mode is DIFFERENT EDGES: it refused `MATCH <- , ANY
<-` under 16.4 SR 12 with no match mode written. the generator had assumed
portable (no default), which is right for a set meant for any engine and
wrong for one meant for turbolay. `just turbolay-typed` now passes
`--match-mode-default different-edges`, which also drops the guards 16.4 SR 14
no longer needs there. the sets below were made with it

## what the regenerated set shows

`sentences/typed-2vars-turbolay-claim-path-minimums.jsonl`: 3,843 rows, 3,808
distinct (were 2,278 and 2,243): the automata's copies are coverage targets of
their own, so the cover phase has 4,545 productions and 6,942 cdrc pairs to
reach instead of 2,990 and 4,943. the never-covered counts are the measure
that matters and they did not move: 153 productions and 333 pairs, before and
after (a diff of target names is no measure here, one tree covers many targets
and the names carry the copy labels). the run took 559 s and 1.57 GB, the
fixed point 47 s. `violations.py`: the path detectors at 0 on the new set (61
and 24 on the old), nothing else grew; the two 16.11 SR 3 hits left are
upper-below-lower (`{ 8 , 0o2 }`), the open half of that rule. the witnesses
moved from `MATCH <- ?` to shapes like `MATCH ( TRAIL <- * ) <-`: a trailing
bare edge brings its implicit nodes

## turbolay #243 (484d1a72), by `breakdown.py`

```
                              exists-table set (2,243)   path-minimums set (3,808)
accepted                      1,401   62.5%              2,773   72.8%
ours: invalid sentence          238   10.6%                 10    0.3%
  16.7 SR 16 no node            189                           0
  16.12 shapes                   26                           0
  16.7 SR 8, 20, 16.4 SR 12      17                           0
  16.11 SR 3 upper below lower    1                           2 (open)
  21.3 SR 4, 20.24 SR 3, 20.11    6                           8 (leaf spellings, next)
engine documented deviation     272                         645
engine parse gap                283                         331
environment, raised, bugs        49                          49
```

the sets differ in size, so the share is the number to read: our invalid
sentences went from 10.6% to 0.3%, and of the valid sentences outside the
documented deviations and the environment turbolay handles 2,792 of 3,127
(89%, was 83%). the deviations grew with the set: 336 "path factors outside
the executable subset" (a `+` or `*` on a simplified pattern, `MATCH -/ a a
/- +`), 23 label expressions on variable-length relationships, 10 bounds above
turbolay's IL018 of 255, 4 searches over unbounded walks. what is left on our
side is the leaf family of the handoff's step 3 (empty delimited identifiers,
TRIM with a bare FROM, a property of NULL) and 16.11 SR 3's upper-below-lower

## for the next rule

- a group node's `step` is where to fold an associative fact; otherwise the
  union of children enumerates subsets and the product grammar pays for them
- a "contains no X" rule is an inherited context with `rejects`, not a
  synthesized fact: the forbidden productions never enter the grammar
- the skeleton probes in `tests/refine.rs` now carry real edges, nodes and
  bounds, since every rule has to hold on the same tree
