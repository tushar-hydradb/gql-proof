# static semantics: the last ten

> for agents: dated working notes, terse on purpose. people start at the [readme](../README.md)

after the path pattern family (`static-semantics-path-minimums-2026-10-23.md`)
turbolay refused 10 of 3,808 sentences as invalid on our side: 4 empty
delimited identifiers (`LIMIT $@""`, `MATCH <-/ @`` + /-`), 3 TRIM with a bare
FROM (`ORDER BY TRIM ( FROM NULL ) FINISH`), 2 general quantifiers with the
upper bound below the lower (`MATCH <- { 8 , 0o2 } FINISH`) and 1 property of
a bare NULL (`RETURN NULL . a AS x`). four rules, four homes, none of them the
context engine's labels. branch `tushar/exists-table`, worktree
`gql-proof-exists`, commits 5d0108d and 0412020 (code) and the ones after
(records); the set is from 32d38c9

## the bounds: order settled at spelling time (16.11 SR 3 a ii)

the two sentences exist because of a rule interaction: a bare edge under a
quantifier needs a nonzero lower bound to have a node at all (16.7 SR 16), so
every sentence covering an upper-bound target under an edge carries a nonzero
lower bound, and `PathMinimums` knows zero or nonzero, not which is larger.

the grammar cannot say it. a fixed lower bound of `1` under a present upper
bound needs right context: after desugaring, `general quantifier ::= { opt1 ,
opt2 }` hides whether opt2 is empty from `down` at opt1. the upper bound's
copy under a nonzero lower (left context, visible) has no text that fits
every lower. value buckets in the automaton (digit count by radix) multiply
copies and still do not order across radixes.

so the engine stays value blind and the order is settled where names are:
`order_bounds` in `src/tree.rs`, called right after `name` in `cover`'s
`extract` closure (`src/context/extract.rs`) and by purdom's `settle` after
every tree it builds (`src/purdom.rs`, `purdom/targeted.rs`), so both
generators agree with the checker; the first version ran it in `cover` only
and `iso_targeted_trees_verify` said so. the prefixed digits can take a
purdom tree at its height or length cap above it, and the productions it adds
must count as used or the targeted search seeks them again
(`short_sentences_cover_what_packed_ones_do`): `settle` marks them and sets
`Generated::settled`, which the cap checks in `tests/purdom.rs` and
`tests/coverage.rs` honour. at every `general quantifier` with both bounds
it reads the values (`verify::unsigned_integer_value`, shared with the
checker) and, when the upper is below the lower, re-spells the upper with
digits prefixed to the ones it was extracted for, in its own radix: `0o2`
under `8` becomes `0o12`, `0b1` becomes `0b1001`. the prefix is the smallest
that reaches the lower, or a random one while the value stays within
turbolay's IL018 cap of 255. the digits and radix stay, so every production
and pair the tree was found for is still in it (coverage is observed on the
final tree, after naming); the prefix adds only digit productions covered
elsewhere. `spell` derives the new text under the radix's own definition, the
child of `<unsigned integer>`: derived from `<unsigned integer>` itself,
`0o152` came out as a decimal integer whose `o` was an `<other digit>`, a
prose leaf that takes any character (the first run showed it, 2 trees failing
21.4 SR 2); and `Analysis::spell` now takes the derivation with the fewest
prose leaves, since a refined copy lists its productions in no grammar order
and `10` under a `@want` copy came out with an `<other digit>` for the `0`
(`refined_trees_satisfy_the_rules` showed that one). a spelling the copy cannot derive leaves the tree alone and the
checker reports it. the quick check for this kind of change is the 1 slot
cover run (`--slots 1 --phase cover --cdrc`, 9 s), which already extracts
`{ 8 , 0o152 }`-shaped trees.

the checker reports the order as `16.11 SR 3 a ii`, a name apart from the
automaton's `16.11 SR 3` (upper bound 0), because the differential test
`automaton_and_verifier_agree` in `tests/refine.rs` compares the automaton
with the verifier over generated trees and the grammar alone does not enforce
the order.
readings: an `<other digit>` is worth 1 in a value (the generator spells
U+0663), as the checker already read it

## TRIM's FROM (20.24 SR 3 b i 1)

a combination of two absent optionals under a present FROM, no production of
its own, so no target is lost. `TrimOperands` in `refine.rs`: a synthesized
fact set at `trim specification`, `trim character string` and `trim byte
string` (at those definitions, not below, so the string expression under
them is not copied), refused at the node of `trim operands` or `byte string
trim operands` whose items hold the FROM token (the desugared `[ [spec]
[chars] FROM ]` group) when the fact is missing, dropped at the operands and
at `multi-character trim function` (BTRIM's trim string has no FROM and must
not leak upwards). reading: 20.25 has no twin of the rule for byte strings,
but its General Rule 2 b reads the `<trim byte string>` as if present, so a
bare FROM is refused there too; the checker cites 20.24 SR 3 for both

## empty delimited identifiers (21.3 SR 4)

the empty alternative of the optional inside the quotes is invalid under
every witness. `DelimitedNotEmpty` in `refine.rs`: a synthesized fact set at
the two character representations, judged at `delimited identifier` (refused
without it) and dropped at `character string literal`, because
`<double quoted character sequence>` is shared: `""` is the empty string
literal there, legal, and the first version of the rule refused it until the
differential test said so. the accent sequence belongs to identifiers alone.
the empty alternative of the double quoted optional is still covered by the
string literal; the accent one has no valid witness, and refinement drops its
copy as unreachable before the count is taken, so the never counts did not
move: 153 productions and 333 pairs

## a property of NULL (20.1 SR 4-6, 21.2 SR 67)

21.2 SR 67 gives a bare NULL its type from a context that fixes one, else it
is implementation defined (IA014) whether 42001 is raised. a property source
wants a node, edge or record type and fixes none, so the sentence is never
portable; turbolay refuses it. `types.rs` at `property reference`: a Null
source is refused (the other 20.1 SR 4-6 sites keep admitting Null, so
`PATH [ NULL , NULL , NULL ]` is unchanged: turbolay runs it, a dynamic
error). the checker (`verify/types.rs`) treated `Ty::Null` as wild there and
now reports it. no label changes for this one

## cost

| | before | after |
|---|---|---|
| refined grammar | 2,972 nts, 7,854 prods | 2,980 nts, 7,859 prods |
| scope 2 slots, labels | 34,941 | 34,949 |
| types 1 slot, labels | 34,580 | 33,343 |
| 2-variable run | 559 s, 1.57 GB, 3,843 trees | 485 s (442 s extraction), 1.38 GB, 3,834 trees |
| never covered | 153 productions, 333 pairs | 153 productions, 333 pairs |

## the set and turbolay

`sentences/typed-2vars-turbolay-claim-last-ten.jsonl`: 3,834 rows, 3,800
distinct; 0 trees fail the syntax rules or the scope checker, 4 only the
types checker (the four `x + NULL` TRIM counts, the unsettled reading). `violations.py`: only the open 18.9 SR 7/10/29 class, 3
sentences (`CHAR ( 0b0 )`). turbolay #243 (484d1a72)
by `breakdown.py`:

```
3800 distinct sentences
  2772   72.9%  accepted
   645   17.0%  engine: documented deviation
            336  path factors outside the executable subset retain their synt
                 e.g. 'MATCH -/ a a /- + FINISH'
            158  L26: typed VALUE definition
                 e.g. 'VALUE x INT = NULL FINISH'
             94  expected exactly one typed query statement
                 e.g. 'CALL { FINISH }'
             23  a label expression on a variable-length relationship is not 
                 e.g. 'MATCH ~[ IS % ]~ + FINISH'
             10  IL018: a quantifier bound above 255
                 e.g. 'MATCH <- { 888 } FINISH'
              8  the fraction of PERCENTILE_CONT must be a literal or a param
                 e.g. 'RETURN COUNT ( * ) AS x NEXT RETURN PERCENTILE_CONT ( x , x ) AS y'
              6  expression is outside the initial typed slice
                 e.g. 'MATCH ( x WHERE EXISTS { <- } ) FINISH'
              4  a path search over unbounded walks is not supported; add TRA
                 e.g. 'MATCH REPEATABLE ELEMENTS <- , ANY <- + FINISH'
              2  an inline procedure that does not end in RETURN is not suppo
                 e.g. 'CALL { FINISH } FINISH'
              2  syntax error or access rule violation: invalid syntax or sta
                 e.g. 'RETURN CURRENT_DATE AS x NEXT CALL ( x ) { FINISH }'
              2  a subquery inside a LET body is not supported
                 e.g. 'FILTER LET x = CURRENT_DATE IN EXISTS { <- } END IS NULL FINISH'
   334    8.8%  engine: parse gap
            242  typed VALUE with a reference, record or closed type
                 e.g. 'VALUE x ( ) = NULL FINISH'
             88  KEEP after a graph pattern inside EXISTS
                 e.g. 'FILTER EXISTS { <- KEEP WALK } FINISH'
              4  <no escape> @ before a delimited identifier
                 e.g. 'LIMIT $@"x" FINISH'
    26    0.7%  environment
             26  no parameters passed by the runner
                 e.g. 'LIMIT $b FINISH'
    19    0.5%  dynamic: raised as it should
              8  invalid date, time, or datetime function field name: the rec
                 e.g. 'ORDER BY DATE ( { } ) FINISH'
              4  trim error: the TRIM character must be exactly one character
                 e.g. 'ORDER BY TRIM ( SESSION_USER FROM SESSION_USER ) FINISH'
              2  malformed path: PATH[...] does not identify a path
                 e.g. 'RETURN PATH [ NULL , NULL , NULL ] AS x'
              2  invalid argument for general logarithm function: a logarithm
                 e.g. 'RETURN COUNT ( * ) AS x NEXT ORDER BY LOG ( x , x ) FINISH'
              2  invalid duration function field name: the record's fields ar
                 e.g. 'ORDER BY DURATION ( { } ) FINISH'
              1  invalid argument for natural logarithm: the natural logarith
                 e.g. 'RETURN COUNT ( * ) AS x NEXT ORDER BY LN ( x - x ) FINISH'
     4    0.1%  engine: bug already reported
              3  NEXT with YIELD does not parse
                 e.g. 'MATCH ( x ) RETURN x NEXT YIELD x FINISH'
              1  FINISH in a composite query or before NEXT CALL
                 e.g. 'FINISH NEXT CALL { FINISH }'
valid, outside documented deviations and the environment: 2791 of 3129 handled (89%)
```

## the next smallest witness

closing `NULL . a` moved the record derivation of `<property source>` to its
next cheapest witness, `RETURN { } . a AS x`: a closed record with no fields,
which 20.11 SR 2 a refuses and the types checker reports (`RECORD {} has no
field a`); `extraction_matches_emission` (0 bad trees) caught it. the types
engine knows a record's class, not its fields ("not followed"), so it cannot
show any record source to have the field: `types.rs` now refuses a record
source at `property reference` until step 4 of the handoff (typing gaps)
follows field names. the record derivation of `<property source>` is still
covered, by a dynamic source (`ORDER BY $b . a FINISH`, 20.11 SR 2 b), so the
never counts did not move; the types label at 1 slot went from 34,523 to
33,343 with it

## what is left on our side

none: turbolay refuses no sentence of the set as invalid on our side (was 10
of 3,808, 488 of 2,243 at the start of this track). the two repaired bounds
(`{ 8 , 0o152 }`, `{ 8 , 0b11011 }`) run; `RETURN { } . a AS x` runs too
(turbolay gives a null, the text makes it a syntax error, see above). the four
sentences that moved from "ours" are the `@"x"` and `` @`x` `` delimited
identifiers with a `<no escape>` prefix, which turbolay does not parse: an
engine parse gap now, sorted by `breakdown.py`. accepted 2,772 of 3,800
(72.9%, was 72.8%); the valid sentences outside documented deviations and the
environment handled 2,791 of 3,129 (89%)
