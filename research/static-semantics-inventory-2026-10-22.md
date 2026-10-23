# static semantics: which syntax rules gql-proof models

> for agents: dated working notes, terse on purpose. people start at the [readme](../README.md)

every syntax rule of iso/iec 39075:2024, one by one, marked by what gql-proof
does with it. the question it answers: can we say static semantics is done? not
yet, and not only for completeness: some rules nobody models are broken by
sentences we generate today

per rule data: `research/static-inventory-2026-10-22.jsonl` (clause, rule
number, kind, status, file:line evidence, a one line note in our words). the
scripts that made it: `tools/inventory/`

## how it was made

- `tools/inventory/extract.py` reads the standard's extracted text (kept out of
  the repo) and lists every syntax rule by subclause and number: 1,025 rules in
  133 subclauses of clauses 5 to 22, numbered without gaps in each
- `tools/inventory/cites.py` indexes the rules the code cites, by component: 278
  distinct rules, most of them in the checkers
- six agents classified a share of clauses each, reading the rule, the cites and
  the code, and giving every rule a kind, a status and evidence
- `tools/inventory/merge.py` checks every rule got exactly one verdict and
  counts
- `tools/inventory/violations.py` looks for concrete violations of not modelled
  rules in generated sentence sets

kinds:

- definition: names or sets things up, nothing to violate
- constraint: something a program can break
- type: computes or requires a declared type
- catalog: needs the catalog, the session, a graph type or a procedure signature
- implementation: implementation defined or dependent

status, for everything that is not a definition:

- generated: every generated sentence keeps it
- grammar: the desugared bnf makes breaking it impossible
- reading: kept, but narrower than iso (forbids more)
- checked: only a checker enforces it, the generator may break it
- not modelled: nothing enforces it

## numbers

```
kind            rules  generated  grammar  reading  checked  not modelled
definition        482
constraint        168         84       11       39        0            34
type              258        183        0       55        4            16
catalog            66          1        0        0        0            65
implementation     51          1        0        1        0            35
```

(14 implementation rules have nothing to check, marked n/a)

of the 426 constraint and type rules:

- 278 (65%) are kept as iso says (generated or grammar)
- 94 (22%) are kept by a narrower reading
- 4 are checked only
- 50 (11%) are not modelled

all 66 catalog rules but one are not modelled: there is no catalog, session,
graph type or procedure signature in the generator, so every rule that needs one
is open as a whole

## what this says about "static semantics done"

two separate claims, and the inventory answers both:

- **sound**: every generated sentence keeps every syntax rule. not true today. a
  not modelled constraint is only harmless if the generator can't reach a
  violation, and `violations.py` finds reachable ones in every set we have: the
  typed two variable extraction (`tushar/prune`, 1,276 sentences) and the scope
  only purdom sets for the neo4j (481) and turbolay (790) claims

  ```
  21.3 SR 4   empty identifier       SESSION SET GRAPH ``
  16.11 SR 3  upper bound 0          MATCH ~ { , 0b0 } FINISH
  18.9 SR 7   zero length            VALUE x CHAR ( 0b0 ) = ...
  20.6        VALUE not one value    FILTER VALUE { FINISH } FINISH
  8.2 SR 2    two access modes       START TRANSACTION READ ONLY , READ ONLY
  20.24 SR 3  TRIM with bare FROM    TRIM ( FROM X'' )
  14.12 SR 7  SELECT * and GROUP BY  SELECT * FROM { FINISH } GROUP BY ( )
  22.1 SR 3   $$ with no request     SESSION SET GRAPH $$b
  ```

  the detectors are text level and approximate, so these are lower bounds, and
  an empty `""` is a string literal, not an identifier, so only empty backticks
  count for 21.3 SR 4

- **complete**: every statically valid sentence is reachable. not true, by the
  91 readings (each listed in the jsonl and in the scope and types module docs)
  and by the not modelled rules whose closing would add sentences

so the honest status line is: static semantics is 58% kept as written, 21% by a
narrower reading, and 80 rules open, some of them reachable and so unsound
today; catalog dependent rules are open as a family

## not modelled constraint and type rules

the agents' notes, in our words, regenerated from the jsonl on 2026-10-23 (the rules
closed on tushar/exists-table and tushar/soundness are gone from it); grouped by
area in the next section

- 5.3 SR 4 (constraint): No confusability check; numbered ASCII names (context.rs:2047) make clashes unlikely, not impossible by rule.
- 7.1 SR 6 (type): Session parameter initializer assignability and consistency with earlier sets; session commands untyped (verify/types.rs:49).
- 8.2 SR 2 (constraint): Grammar lists modes freely; READ ONLY, READ WRITE (two access modes) can be generated.
- 9.1 SR 5 (constraint): Catalog-modifying procedure bodies may mix in other statement kinds; nothing checks.
- 9.1 SR 6 (constraint): Data-modifying bodies may contain catalog statements; no rule tracks statement kinds.
- 9.1 SR 7 (constraint): Query specifications (subqueries, CALL bodies) may contain data-modifying or catalog statements unchecked.
- 9.2 SR 4 (constraint): A catalog-modifying statement may be followed by NEXT statements; no check.
- 9.2 SR 5 (constraint): Focused and ambient statements may be mixed across NEXT in one block; no check.
- 9.2 SR 6 (constraint): SELECT statements may be mixed with other linear query statements in one block; no check.
- 9.2 SR 7 (constraint): Blocks may mix statements with and without a primitive result statement; no check.
- 10.1 SR 5 (type): Graph initializer type equals its graph expression's; graphs are not typed (context/types.rs:869).
- 10.1 SR 8 (type): Initializer must be assignable to declared graph reference type; graphs are opaque, no check.
- 10.2 SR 5 (type): Table initializer type equals its table expression's; tables are not typed.
- 10.2 SR 8 (type): Table initializer must be assignable to declared table type; tables untyped, unchecked.
- 12.8 SR 2 (constraint): Inline CALL as catalog-modifying statement must have a catalog-modifying body; unchecked.
- 13.6 SR 2 (constraint): Inline CALL as data-modifying statement must have a data-modifying body; unchecked.
- 14.2 SR 3 (constraint): all conjunctions in one composite expression must be the same operator; mixing UNION/EXCEPT/OTHERWISE unchecked
- 14.2 SR 4 (constraint): focused and ambient operands may not be mixed in one composite expression
- 14.5 SR 2 (constraint): inline procedure in a query CALL must be a query, not data- or catalog-modifying
- 14.11 SR 4 (type): RETURN DISTINCT items must be groupable (22.15); unchecked in both type modules
- 14.12 SR 5 (type): SELECT DISTINCT items must be groupable (22.15); unchecked
- 14.12 SR 26 (constraint): FROM subquery: with graph expression must be ambient, without must be focused
- 17.6 SR 1 (constraint): parent reference solidus rule: none after root /, required otherwise
- 18.1 SR 8 (constraint): two node type specs in one body may not share an effective key label set
- 18.1 SR 9 (constraint): a node type spec implying another must be structurally consistent with it
- 18.1 SR 10 (constraint): local node type aliases must be unique within a graph type body
- 18.1 SR 11 (constraint): every edge type's source and destination node types must be declared in the body
- 18.1 SR 14 (constraint): edge type specs sharing a key label set must agree on direction, labels, properties
- 18.1 SR 16 (constraint): an implying edge type spec must be structurally and endpoint consistent
- 18.2 SR 7 (constraint): node key labels and implied labels must be disjoint
- 18.3 SR 8 (constraint): edge key labels and implied labels must be disjoint
- 18.3 SR 17 (constraint): source alias or key label set must resolve to a node type spec in the body
- 18.3 SR 18 (constraint): destination alias or key label set must resolve to a node type spec in the body
- 18.5 SR 1 (constraint): property type names in one property types spec must be distinct
- 18.9 SR 62 (type): closed node type's constraint ignored; treated as any node (context/types.rs:1122)
- 18.9 SR 65 (type): closed edge type's constraint ignored; treated as any edge (context/types.rs:1123)
- 18.9 SR 68 (constraint): GROUP list element type must be a node or edge reference type
- 18.9 SR 84 (type): closed union's components ignored; treated as fully dynamic (context/types.rs:1128)
- 18.9 SR 87 (type): component type set of a union not computed
- 18.9 SR 88 (constraint): union components must be all nullable or all NOT NULL
- 20.6 SR 5 (constraint): VALUE subquery's last statement must be a linear query statement
- 20.6 SR 6 (constraint): VALUE subquery's emitting result statement must not be omitted
- 20.8 SR 10 (type): dynamic-union source cast to static target needs a castable component; both leave it
- 21.2 SR 20 (constraint): approximate literal range never checked; generated literals are tiny so unlikely to bite
- 21.2 SR 73 (constraint): list literal elements may be any expression; verifier waives it via the alternate derivation (src/verify/types.rs:41)
- 21.2 SR 75 (constraint): record literal fields may be any expression, not just literals
- 22.10 SR 5 (type): any dynamic union target accepts everything; closed union components never checked
- 22.10 SR 6 (type): node vs edge base enforced, but closed object-type subtyping is not
- 22.19 SR 2 (type): dynamic operands are combined into dynamic instead of rejected (4.14.4 leniency)
- 22.19 SR 5 (type): material vs nullable result not tracked; only literal NULL kept from NOT NULL

## by area, and how each would close

- **statement composition** (9.1, 9.2, 11.2, 12.8, 13.6, 14.2, 14.5, 14.12 SR
  26, 19.4 SR 5, 20.6): what kind of statement sits where, and whether a body
  yields a table, a value or nothing. the most reachable gaps, and one rule
  family: a statement kind (query, data modifying, catalog) and a result shape
  (table, value, none) synthesized up, checked where a body is used. fits
  scope's label as a few flags
- **path patterns** (16.4 SR 12, 16.7, 16.11, 16.12): minimum lengths, node
  counts, quantifier bounds and nesting. the two already known gaps (16.7 SR 16,
  16.12 SR 4) plus their siblings. structural, so automata in `refine.rs` like
  16.4 SR 6 and 14, except the bounds, which need the leaf values
- **leaf values** (16.11 SR 3, 18.9 bounds, 21.2 SR 20, 21.3 SR 4, 20.24 SR 3):
  the leaf provider picks numbers and names without the rule's constraints.
  closing them is a filter on the provider (no zero bound, no empty identifier)
- **graph types** (18.1 to 18.5): consistency of a graph type body. needs a
  model of the body, close to a small catalog
- **typing gaps** (14.11 SR 4, 14.12 SR 5, 18.9 closed and union types, 20.8 SR
  10, 22.10, 22.19): groupability, closed types, unions, nullability. widening
  the types rule
- **catalog and session** (66 rules): references that must resolve, procedure
  signatures, parameters with a request behind them. needs a modelled catalog,
  the largest step and the one the cutoff doc already lists as a hypothesis

## caveats

- this is the 2024 text. cor 1 amends 13 of these rules (in 14.7, 14.10 to
  14.12, 15.1, 16.8, 18.1, 18.2, 18.9, 20.7 and 22.17); their classification was
  not redone against the amended text
- the extraction loses indentation, so a deep sub-item numbered like the next
  rule can be read as a rule: about a dozen such fragments were found (14.10 SR
  5 and 6, 17.2 to 17.4 SR 3, 17.6 SR 6, 17.7 SR 5, 20.24 SR 4, and three
  "evaluation is terminated" lines). none of them is a constraint, so they move
  the totals by about 1% and the constraint counts not at all
- the classification is the agents' reading with file:line evidence, checked by
  hand only where `violations.py` confirms it. a rule marked not modelled may be
  kept by code nobody found (for example statement boundaries in scope touch 9.2
  SR 7); a rule marked generated may be kept only in part, and the agents
  flagged those in the notes
- citation ranges like "16.10 SR 3, 16.9 SR 2" were parsed by `cites.py` as also
  citing 16.10 SR 16; the agents ignored such keys, the counts don't use the
  cites

## luck: a class of sentences gone by witness choice, not by a rule

the typed two variable list of `tushar/prune` was regenerated between two runs
(`258437a`: extraction over the claim refined grammar, the smallest context
first). `violations.py` on both:

```
                                     before    after
sentences                             1,228    1,310
21.3 SR 4   empty identifier             24       21
16.11 SR 3  upper bound 0                 1        1
18.9 SR 7   zero length                   3        3
20.6        VALUE not one value           1        1
8.2 SR 2    two access modes              4        3
20.24 SR 3  TRIM with bare FROM           2        2
22.1 SR 3   $$ with no request           10        8
14.12 SR 7  SELECT * and GROUP BY         1        1
22G11       variable used after DELETE   17        0
```

every static class survives the regeneration with new witnesses (`MATCH <- {
, 0b0 }`, `RETURN VALUE { FINISH } AS x`, `CALL $$b ( )`). only the use after
delete class is gone, and no rule took it out: nothing in scope, types or the
checkers tracks a deleted variable (the two commits in between are `c7b303a`,
which types what DELETE deletes, 13.5 SR 5, and `258437a`). it went because
the smaller witnesses happen not to put an access after a DELETE. the earlier
list had, among the 17:

```
START TRANSACTION USE CURRENT_PROPERTY_GRAPH INSERT ( x ) INSERT ( y )
DELETE y DELETE x SET x = { } , y : a
```

everything here is deterministic, so this is not randomness. it is a property
that holds of the current output and not of the generator: a different target
set, cap or tie-break can bring the class back and nothing would say so. a
property of the generator has to hold for every witness it could pick, and
only a rule in the label (here typestate: live, deleted or maybe deleted per
variable, and whether the table is surely not empty) makes it so

until that rule exists, two checks keep it visible:

- `violations.py` now flags a variable used after DELETE (4.4.4, 22G11), so a
  list that regains the class says so
- a witness shuffle: run extraction with the tie-breaks between equally small
  witnesses permuted by seed. a class that appears under some seeds and not
  others is one no rule governs; a rule enforced by construction keeps it out
  under every seed. that turns luck into a test
