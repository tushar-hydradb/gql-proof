# soundness: the first families closed, and the audit

> for agents: dated working notes, terse on purpose. people start at the [readme](../README.md)

branch `tushar/soundness`, from main at 51d059a (2026-10-23). the handoff is
`soundness-handoff-2026-10-23.md`; this note is what happened next. the goal
stays: every sentence the generator emits keeps every syntax rule, for the whole
language, with a proof that rests on stated hypotheses and not on which witness
extraction happened to pick

## step 1: the stale sets regenerated

at 51d059a, before any change (`sentences/README.md` has the lines):

- scope sets: turbolay 785, neo4j 463
- the whole grammar typed set at 2 variables
  (`typed-2vars-whole-grammar-51d059a.jsonl`): 3,508 rows, 437 s, 0 checker
  failures, 4,442 of 4,473 productions and 6,474 of 6,540 cdrc pairs

what the detectors and a text check found in the whole grammar set, each a
rule the generator broke with no checker reporting it:

| rule | sentences | example |
|---|---|---|
| 18.9 SR 7, 10, 13 (lengths) | 3 + 1 | `CAST ( NULL AS CHAR ( 0b0 ) )`, `STRING ( 0xA , 8 )` |
| 18.2 SR 2, 18.3 SR 2 (closed types) | 6 | `CAST ( NULL AS NODE TYPE IMPLIES AS a )`, `NODE TYPE a ( )` |
| 20.9 SR 3 (subquery in an aggregate) | 169 | `COUNT ( EXISTS { <- } )` |
| 8.2 SR 2 (two access modes) | 3 | `START TRANSACTION READ ONLY , READ ONLY` |
| 14.12 SR 7 b (`*` with GROUP BY) | 32 | `SELECT * FROM { FINISH } GROUP BY ( )` |
| 22.1 SR 3 (`$$` substitution) | 8 | `SESSION SET SCHEMA $$b` (an environment rule, see below) |

## step 2: what closed, and how

each with a probe in the tests and the checker reporting it first:

- **18.9 SR 7, 10, 13, 21, 28, 29, 38, 40** (lengths, precisions, scales):
  `tree::order_bounds` generalised from the quantifier bounds. the engine knows
  an integer is zero or not, never its value, so the value is settled at
  spelling time: the integer below what the rule asks is re-spelled with digits
  prefixed in its own radix, keeping every digit production the tree was found
  for. both generators run it; the checker (`verify::syntax_rules`) reads the
  values again, on `<character string type>`, `<byte string type>`, `<list
  value type>`, the exact and approximate numeric types. the checker now reads
  a digit of any script by its unicode run (`verify::digit_value`), where it
  used to count any non-ascii digit as 1: the automaton `PathMinimums` still
  counts an `<other digit>` as nonzero, which rests on the leaf provider
  spelling U+0663, and the checker is what would catch a provider spelling an
  Nd zero
- **18.2 SR 2, 3 and 18.3 SR 2, 3, 4** (node and edge type specifications):
  `refine::ElementTypeShape`, a tree automaton with synthesized facts only
  (named, keyed, aliased; edge named, edge keyed, endpoint aliased; edge kind
  and shape), consumed at the specification's parent: the closed reference
  value type rejects, the element type specification of a graph type body
  consumes. the first version was an inherited context ("inside a closed
  reference value type"), which copied the whole type subgrammar: 7,839 to
  10,586 productions under turbolay's claim. the synthesized version costs 134
  productions (7,973). "simply contains" is read as defined (no intervening
  instance of the container's definition); a specification nested in a
  property's type is judged by its own parent. reading for 18.3 SR 4: a
  pattern with no edge kind is not constrained (the rule's "otherwise" presumes
  UNDIRECTED is present). checker twin: `verify::syntax_rules`, with
  `simply_contains`
- **20.9 SR 3** (no procedure body in an aggregate): the scope engine's `QUERY`
  flag, which 14.10 SR 4 already raised at every subquery, is now read at
  `<aggregate function>` and rejects. reading: 19.4 SR 2 and 3 replace an
  EXISTS over a graph pattern or match block by one over a procedure body
  first, so every subquery counts. a hole found on the way: the flag was
  cleared at `<let variable definition>`, which a `LET .. IN .. END` expression
  shares with the LET statement, so a subquery under a LET inside an aggregate
  (or a sort key) slipped out; `LET_DEFINITIONS` now keeps the flag through
  to the statement. checker: `verify::scope` at `aggregate function`
- **8.2 SR 2** (one access mode): `refine::OneAccessMode`, counting at the
  characteristics' group nodes; checker counts the access modes
- **14.12 SR 7 b** (`SELECT *` bears no GROUP BY): the select statement arm of
  scope, and the checker's `select`, which had returned early on any FROM
  without checking anything

the never targets this adds under turbolay's claim, at 1 variable: 6
productions and 8 cdrc pairs, all copies of `<general set function>` whose
argument the claim rules mark as holding an EXISTS: 20.9 SR 3 makes them
unreachable, so they are iso-rule never targets. the whole grammar run at 1
variable loses nothing (69 productions, 144 pairs never, as before)

## the readings this adds

- 18.3 SR 4 applies to a specification with an edge kind
- 20.9 SR 3 is judged after 19.4 SR 2, 3's replacement: no subquery of any
  form inside an aggregate
- 18.9 SR 28 (a byte string type's minimum is at most its maximum) is the same
  check as SR 21 over the lengths and reported as 18.9 SR 21

## the environment rules (the catalog decision, step 5)

the rules that need something the sentence does not declare: a schema, graph,
graph type, procedure, binding table or parameter by name, a session or
transaction state. 65 catalog rules in the inventory, plus 22.1's parameters.
the decision: they hold given a hypothesis, stated with the claim, that the
engine's environment provides what the sentence names, with the shape the
sentence uses. the alternative, refusing every production that names an
environment object, would make most of clauses 7, 10, 12, 17 never targets
and the generator useless against a real engine. `$$` substitution (22.1 SR
3) is the one case the hypothesis cannot carry (the substituted text decides
validity); it is listed as such in the audit, and the claim leaves it out

## step 3: the audit

`research/audit/README.md` defines the rows; `research/audit/part-*.jsonl`
hold them, one part per group of clauses, written by agents reading the text.
the findings and the merged table follow in this note

## 2026-10-24: the audit closed, the claim

the audit (8 agents, one part per group of clauses, `research/audit/part-*.jsonl`)
found 60 open constraint and type rows, 38 reachable in a cached set. all are
closed; `research/soundness-table.md` is the per-rule table, generated from
`audit.jsonl` by `python3 -I tools/inventory/audit.py --table
research/soundness-table.md`

how they closed, by group:

- **statement kinds** (9.1 SR 5-7, 9.2 SR 4-6, 12.8, 13.6, 14.5 SR 2, 14.2 SR
  3-4, 14.12 SR 26): `refine::StatementKinds`, synthesized facts judged at each
  composite query expression, block and procedure kind. first version carried
  every subset of the seven conjunctions up a composite query (765 copies,
  22,059 productions); judged at each expression it is 5,968. 9.2 SR 7 is the
  checker's alone ("contains" reaches into nested bodies)
- **graph type bodies** (18.1 SR 8-16, 18.2 SR 7, 18.3 SR 8, 17, 18): the
  checker (`verify/graph_type.rs`) and the gate. the generator spells every
  alias, label and name `a`, so a body's consistency is a matter of which
  specifications sit together; not followed. the whole grammar run withholds
  the edge types whose endpoints name no node type: lost coverage of CREATE
  GRAPH TYPE bodies, the next lever there
- **types** (closed element types, unions, dynamic casts, combinations,
  composite columns, typed initializers, NULLIF and COALESCE): the types
  checker models them; the engine follows with readings (no dynamic operand in
  a combination, a dynamic value casts to scalars, no closed union target,
  closed element types opaque to properties, no bare NULL in COALESCE), and
  three automata (`PropertyValueTypes`, `ClosedInitializerTypes`,
  `UnionNullability`)
- **the rest**: `ParentSolidus` (17.6 SR 1, literal), `IntegerCount` (20.16 SR
  1), the KEEP prefix in `SelectiveAlone` (16.4 SR 12), distinct names at
  spelling time (18.5 SR 1, 18.10 SR 2), lexical limits under H2

holes the checker had, found by the audit's demand that every row name a check
and every check have a probe: a SELECT with FROM was never checked (scope or
types); SET and REMOVE took a value variable as target; a nested aggregate
slipped through when its variable was a group; field names were compared across
nested records; extended identifiers were not checked for reserved words

what makes it not luck: the gate (a flagged tree is never printed), the two
scripts (`shall_coverage.py`: every shall has a row; `audit.py`: no open row,
every row's rule string reported by the checker and probed, every `checked` row
gate-only), and `cargo test`. `soundness-claim.md` has the argument

the runs at the end (the gate in force; numbers in `sentences/README.md`):

| run | printed | withheld | of them generator bugs | productions never | cdrc never |
|---|---|---|---|---|---|
| 2 vars, turbolay claim | 3,966 | 0 | 0 | 156 | 335 |
| 2 vars, whole grammar | 3,928 | 135 | 0 | 30 | 79 |
| purdom cdrc, whole grammar | 569 | 21 | 0 | | |

the withheld trees break graph type body rules (an edge type whose endpoints
name no node type of the body) and 9.2 SR 7; both gate-only. that is the
remaining cost: coverage of CREATE GRAPH TYPE bodies, not soundness

## 2026-10-24: the independent review

a fresh agent, briefed with the claim and the materials only, tried to break it.
it found four classes, all fixed or stated:

- purdom and the scope-only sets never ran the types checker, while the theorem
  named them: the theorem now covers `context --rule types` output; the others
  claim the syntax and scope rows and say so on stderr
- a possibly null value into a NOT NULL site (4.17.4.2 alignment): the checker
  and the engine take the strict reading, no computed value to a NOT NULL site
- the 4.14.4 cure let dynamic operands meet every requirement under the name of
  a reading, though it lets more in than the text: it is now hypothesis H2'
  (an implementation's permission), with ID086 and the default collation named
  too
- 16.5 SR 6 c (an inserted property's type) was filed as implementation and
  never checked: now checked like 13.3 SR 3; 6 SR 4 reads delimited identifiers;
  4.17.4.2 and 4.14.4 have audit rows

it also named an H3 case (a union type whose two trees disagree), now stated in
the claim
