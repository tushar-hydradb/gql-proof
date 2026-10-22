# a subquery body has a binding table type (19.4 SR 5 and kin)

> for agents: dated working notes, terse on purpose. people start at the [readme](../README.md)

the first rule closed from the static semantics handoff
(`research/static-semantics-handoff-2026-10-22.md`): the largest class of our
own invalid sentences on turbolay, `EXISTS { FINISH }` (250 of the 488).
branch `tushar/exists-table`

## the rule, from the text

19.4 SR 5: the declared type of an EXISTS body (a nested query specification)
shall be a binding table type. the body's declared type is its last
statement's (9.2 SR 13); a linear statement's is its last element's (14.3 SR 6,
13.1 SR 9); FINISH is the empty type (14.10 SR 5), a data-modifying statement
without a result statement has FINISH implicit (13.1 SR 2-3), and a
catalog-modifying statement is the empty type outright (12.1 SR 4). a nested
query specification used as a statement passes its own type up (9.1 SR 2-3,
20.6 SR 5 b ii), so the chain is followed through nesting. there is no
"no result statement" case for queries: an ambient linear query statement
always ends in a result statement or is a nested specification

the same fact closes 20.6 SR 8 (VALUE body) and 11.2 SR 2 (nested binding table
query). 20.6 SR 3 (VALUE returns one column) came along: once `VALUE { FINISH }`
was gone, the next smallest witness was `VALUE { RETURN NO BINDINGS }`, which
the types checker already refused, so the generator had to learn it too

## 20.6 SR 10, after the review

the one unsorted sentence on turbolay was ours: `VALUE { RETURN CURRENT_DATE
AS x }` returns more than one row. 20.6 SR 10 wants LIMIT 1 (a) or a single
return item that directly contains an aggregate function with no GROUP BY (b);
SR 5 a wants the emitting statement to be one linear query statement, so a set
operation is out too. a second label flag, `ONE_ROW`, is set by a RETURN with
an aggregate and no GROUP BY, cleared by a set operation, carried like
FINISHED, and demanded at VALUE. the LIMIT 1 way is not generated: the label
does not see the literal (a reading, 92 rules are now narrower). the checker
reads the literal (`returns_one_row`) and sorts a set operation under SR 5.
`breakdown.py` sorts turbolay's message for it. witness: `VALUE { RETURN
count(*) AS x }`

## where it lives

scope's label, no new fact. `gf::FINISHED` existed (set by FINISH, carried
along a statement chain by `combine`, read by the 14.2 SR 5 check at the
composite query expression) and was cleared at `statement` so it never left
one. now it means "the subtree's declared type is the empty type": set by
FINISH, by a data-modifying body without a result statement, by a
catalog-modifying statement; carried up through statement, block, body,
nested specifications; cleared at `procedure specification` (the program's top
and CALL's wrapper, where nothing reads it); refused at the three consumers,
with the one-column count for VALUE. `src/context/scope.rs`, the consumer arm
near `"exists predicate"`

the checker twin in `src/verify/scope.rs`: `emits_finish` walks the same chain
structurally, `finishes` (14.2 SR 5) now recurses into nested specifications.
reading recorded there: a FINISH reached through a nested specification is
14.2 SR 5's FINISH too, since an empty-typed operand cannot be column
name-equal (14.2 SR 10)

## cost

the point the plan had to defend: no refined copies (the refine line is
unchanged, 2,460 nonterminals and 5,264 productions) and labels do not split,
a FINISH-ending statement label closes with no outputs so it was distinct
already. measured on the turbolay claim:

```
                          before                 after 19.4 SR 5       after 20.6 SR 10 too
scope, 2 slots            32,253 labels 0.96 s   32,250 labels 0.99 s   32,406 labels 0.97 s
types, 1 slot             33,782 labels 2.46 s   33,779 labels 2.53 s   33,923 labels 2.49 s
types, 2 slots, cover     603 s (memory)         566 s, 1.26 GB         547 s, 1.27 GB
```

`ONE_ROW` splits aggregate-without-GROUP-BY RETURN labels from the other
non-plain ones: half a percent more labels, within noise on time

## what the regenerated set shows

`sentences/typed-2vars-turbolay-claim-exists-table.jsonl`: 2,278 rows, 2,243
distinct, the same 2,026 cdrc targets as before plus the nested-query EXISTS
one, none lost (diffed by target, not counted). `violations.py`: the new
detector (an EXISTS or VALUE body that is FINISH) at 0 and the 20.6 SR 10 one
at 0, nothing else grew. the 306 `EXISTS { FINISH }` witnesses became
`EXISTS { <- }`: the graph pattern form, valid by 16.7 SR 14's implicit node
patterns. the nested-query witnesses are now `EXISTS { RETURN CURRENT_DATE AS
x }` and `VALUE { RETURN COUNT(*) AS x }`

## turbolay #243 (484d1a72), by `breakdown.py`

```
                              before (484d1a72 on the old set)   after
distinct                      2,243                              2,243
accepted                      1,174   52.3%                      1,401   62.5%
ours: invalid sentence          488   21.8%                        238   10.6%
  19.4 SR 5 EXISTS { FINISH }   250                                  0
  20.6 SR 10 VALUE not one row    1 (unsorted then)                  0
  16.7 SR 16 no node            189                                189
  16.12, 16.7 SR 8, 20 ..        49                                 49
engine parse gap                282                                283
engine documented deviation     248                                272
environment, raised, bugs        51                                 26
unsorted                          1                                  0
```

the 250 went to accepted (227 with the VALUE one) and to turbolay's documented
deviations (the rest: bodies like `CALL { FINISH }` at the top level that
were the context of an EXISTS before now stand alone and hit "expected
exactly one typed query statement"). of the valid sentences outside the
documented deviations and the missing parameters, turbolay handles 1,420 of
1,707 (83%, was 80%). the path pattern family (16.7 SR 16 and kin, 230) is
now 97% of what is left on our side: the next rule, in `src/refine.rs`

## things that bit, for the next rule

- **ambiguous parses in the tests.** `{ FINISH }` is a nested query
  specification and a nested data-modifying procedure; `CALL { ... }` is a
  query, a data-modifying and a catalog-modifying statement; `MATCH .. MATCH
  ..` in an EXISTS block is also a data-modifying body. the engine's probe
  test takes any accepted tree and the checker test demands one verdict per
  tree, so a rule has to hold under every parse. the parses that break 13.1
  SR 5 (a data-modifying statement modifies something) are kept out by the
  refine automata in the real pipeline but the test verifiers did not run
  them: `tests/scope_checker.rs` and `tests/context_types.rs` now build the
  verifier `with_syntax_rules`, which is what the generator sees
- **the next smallest witness.** closing a class makes extraction pick the
  next cheapest body, which may break the next rule (20.6 SR 3 here, caught
  by `generated_trees_pass_the_checkers`). run that test before the long run
- the standard's text comes from the pdf with `just iso-text`, into the
  gitignored `iso-text/`; nothing of it goes in the repo
