# the never targets at 2 variables: an audit, and what 3 variables buy

> for agents: dated working notes, terse on purpose. people start at the [readme](../README.md)

an audit by a separate agent of the 153 productions and 333 cdrc pairs the
2-variable typed run (`tushar/exists-table` at 2e39c72, the turbolay claim)
reports as never covered: is every one of them really without a tree at the
cap (totality), and which of them does a third variable free. the per-target
classification is `never-targets-2vars-2026-10-23.tsv` (cause, minimum
slots, note, target); the targets expected to flip at 3 slots are
`never-targets-3var-flips-2026-10-23.tsv`. the full never lists come from the
usual command with `--top 100000` (`--top` is the rows-per-table cap of the
report, `src/main.rs`), 434 s

## the verdict: no miss

every never target has a cause other than extraction. none is excluded by
the claim or needs a catalog: the refined grammar drops claim-forbidden
productions before targets are counted, and purdom with the syntax rules and
the claim alone covers every remaining ISO target. every 2-variable never
target is also never at 1 slot (227 / 472 there; 213 flipped from 1 to 2, 0
appeared)

| cause | productions | pairs |
|---|---|---|
| needs 3 variables | 12 | 16 (+ 12 pairs whose other copy needs 4) |
| needs 4: the recursive rep occurrence of the three-item lists | 0 | 12 |
| needs 4: graph pattern YIELD with two items (each yielded item costs a declaration slot and a yield slot) | 4 | 7 |
| needs 6 or 8: YIELD with three or four items | 1 | 3 |
| iso rule, rule and checker agree: 14.11 SR 8 (unaliased return item not a variable), 14.10 SR 4 (EXISTS in a sort key) | 23 | 40 |
| scope reading: a bare variable as a pattern WHERE (no correlation into patterns; an element is not a boolean) | 3 | 6 |
| types reading: a variable reference is only read as exact, string or boolean (`types.rs` VALUES and the slot mask), so no tree for the `is<bvr>` copies under list, record, byte string, datetime, duration | 73 | 174 |
| types reading: CASE, NULLIF, COALESCE operands and results are exact or NULL; booleans and EXISTS refused | 36 | 61 |
| rule gap: `RETURN *` refused by the scope rule at every cap | 1 | 2 |

how it was checked: for every family the shortest sentence was written by
hand and judged by a scratch checker (parse with the ISO grammar, every tree
through the verifier with the syntax rules and the claim, `verify::scope`,
`verify::types`, and the typed rule itself at 2, 3 and 4 slots). the "needs
k" rows are sentences refused by the rule below k and accepted at k; the
reading rows are refused at every cap. the emission oracle
(`extraction_matches_emission` with `GQL_JOIN=1`) is exact at 1 slot (1,826
productions, 2,840 pairs, 0 bad trees, 78 s); at 2 slots it was still running
after 40 minutes and was stopped, so the 2-slot oracle is not a measurement

## two things found on the way

- **`RETURN *` is a rule gap**: the scope rule refuses `MATCH (x) RETURN *`
  (and ORDER BY, ALL, DISTINCT, under CALL, after NEXT, after FOR) at every
  cap and under `--rule scope` alone. `NEEDS_TABLE` set at the return
  statement for a star (`src/context/scope.rs`, `d.set(gf::NEEDS_TABLE,
  true)` in the return body) is not cleared at `<ambient linear query
  statement>`; the refusal lands there. nothing in `tests/context_scope.rs`
  covers a star. not an extraction miss; the fix is scope's, one production
  and two pairs
- **a code concern, unproven**: `Extractor::search` in
  `src/context/extract.rs` (the conditionally resolved branch around lines
  434 to 461) leaves a conditionally resolved search's dependents in
  `by_depth[depth]`, and the next definitive failure at that depth settles
  them although they depended on another key. the 1-slot oracle being exact
  says it did not bite there; read it before trusting a 3-slot never list

## what 3 variables buy

predicted from the targets, not measured (the 3-slot cover phase stalls,
`three-variable-run-2026-10-23.md`): 153 never productions become 141 and
333 pairs become 305. what flips: the recursive `rep2` productions and their
`opt1` pairs of the lists that take three items (`LET x = 1, y = 2, z = 3`,
`RETURN 1 AS x, 2 AS y, 3 AS z` in four copies, `CALL (x, y, z) { .. }`,
`NEXT YIELD a, b, c`, `VALUE x { y PATH, z PATH, w PATH }` in four copies,
`{ a : 1, b : 2, c : 3 }`), three VALUE definitions in a block, and the
second LET definition, yield item alias or record field that references a
bound variable (`MATCH (x) LET y = 1, z = x`, `NEXT YIELD a, b AS c`, `{ a :
1, b : x }`). the four-item versions of the same lists need 4; a graph
pattern YIELD with two items needs 4, with three or four items 6 or 8. the
reading rows (135 productions, 281 pairs) stay never at any cap: they move
only by widening the types or scope readings, step 4 of the handoff
