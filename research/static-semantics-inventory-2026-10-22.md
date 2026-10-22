# static semantics: which syntax rules gql-proof models

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
constraint        168         60       11       37        0            60
type              258        182        0       55        5            16
catalog            66          1        0        0        0            65
implementation     51          1        0        1        0            35
```

(14 implementation rules have nothing to check, marked n/a)

of the 426 constraint and type rules:

- 253 (59%) are kept as iso says (generated or grammar)
- 92 (22%) are kept by a narrower reading
- 5 are checked only
- 76 (18%) are not modelled

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

the agents' notes, in our words; grouped by area in the next section

- 5.3 SR 4 (constraint): no confusability check on identifiers; numbered ascii
  names make clashes unlikely, not impossible
- 7.1 SR 6 (type): session parameter initializers are not typed
- 8.2 SR 2 (constraint): more than one access mode can be generated
- 9.1 SR 5, 6, 7 (constraint): procedure bodies may mix statement kinds (catalog
  in data modifying, data modifying or catalog in a query)
- 9.2 SR 4, 5, 6, 7 (constraint): statement blocks may mix catalog and other
  statements, focused and ambient, SELECT and other queries, statements with and
  without a result
- 10.1 SR 5, 8 and 10.2 SR 5, 8 (type): graph and table initializers are untyped
- 11.2 SR 2 (type): a nested table query need not yield a table
- 12.8 SR 2 and 13.6 SR 2 (constraint): an inline CALL in catalog or data
  modifying position need not have that kind of body
- 14.2 SR 3, 4 (constraint): one composite query may mix conjunctions, or
  focused and ambient operands
- 14.5 SR 2 (constraint): an inline CALL in a query need not hold a query
- 14.11 SR 4 and 14.12 SR 5 (type): DISTINCT items need not be groupable
- 14.12 SR 26 (constraint): a SELECT FROM subquery's focus is not tied to its
  graph expression
- 16.4 SR 12 (constraint): DIFFERENT EDGES with a selective path pattern allows
  other patterns
- 16.7 SR 8, 9, 16, 20 (constraint): minimum path length and node count rules,
  nested quantifiers
- 16.11 SR 3 (constraint): quantifier bounds
- 16.12 SR 1 to 4 (constraint): simplified path pattern contents and nesting
- 17.6 SR 1 (constraint): the solidus rule in a parent reference
- 18.1 SR 8, 9, 10, 11, 14, 16; 18.2 SR 2, 3, 7; 18.3 SR 2, 3, 4, 8, 17, 18;
  18.5 SR 1 (constraint): graph type bodies (key label sets, aliases,
  consistency, endpoints, distinct property names)
- 18.9 SR 7, 10, 13, 21, 28, 29, 38, 40 (constraint): length, precision and
  scale bounds of value types
- 18.9 SR 62, 65, 84, 87 (type) and SR 68, 88 (constraint): closed node and edge
  types, union types, GROUP list element types
- 19.4 SR 5 (type): an EXISTS body need not yield a table
- 20.6 SR 5, 6, 8, 10 (constraint): a VALUE subquery need not be single valued
- 20.8 SR 10 (type): casts from a dynamic union need no castable component
- 20.9 SR 3 (constraint): an aggregate's argument may hold a subquery
- 20.24 SR 3 (constraint): TRIM with a bare FROM
- 21.2 SR 20, 73, 75 (constraint): approximate literal range, list and record
  literal contents
- 21.3 SR 4 (constraint): empty delimited identifiers
- 22.10 SR 5, 6 and 22.19 SR 2, 5 (type): union assignment, closed type
  subtyping, dynamic combination, nullability of combined types

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
(`ef00fdb`: extraction over the claim refined grammar, the smallest context
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
checkers tracks a deleted variable (the two commits in between are `d831c27`,
which types what DELETE deletes, 13.5 SR 5, and `ef00fdb`). it went because
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
