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

## 2026-10-25: the second review and the rewrite audit

the second review found three printed families (a HAVING with no aggregating
item; a SELECT beside a USE statement, ambient after its rewrite; a NOT NULL
graph type initializer), weak checks (16.4 SR 14 and 6 read per depth; an
EXISTS in a sort key) and holes in the argument (rewrites outside the gate,
`$$` printed though left out, H2's minima, the start symbol). it led to the
rewrite audit: every one of the 96 rules that rewrite text has a row
(`research/audit/rewrite-*.jsonl`, `tools/inventory/rewrites.py --check`), 18
were open, all closed. the decisions:

- no SELECT with a FROM is generated (`refine::NoSelectBody`): its replacement
  (a CALL of the body, a filter, RETURNs and a NEXT with fresh names) is not
  built by the checker, and seven open rewrite rows came from it
- no `$$` is generated (`refine::NoSubstitution`)
- 16.7 SR 10 makes each multiset alternation operand a named subpath, so SR 20
  applies to it: printed sentences like `MATCH ( <- ? |+| <- ? ) <- FINISH`
  broke it; the automaton and the checker keep it now
- under the portable default a missing match mode is read as DIFFERENT EDGES
  for 16.4 SR 12 (the strict side)
- a shadowed match arm had kept the 21.3 SR 5 check from ever running on
  delimited identifiers; `#![deny(unreachable_patterns)]` makes that a build
  error
- an automaton for HAVING carried an aggregate fact through every expression
  and stalled the 2-variable run (30 minutes); redundant once SELECT bodies were
  out, removed

## 2026-10-25: the third review

one printed family: a simple CASE whose operand is a CAST with an element
predicate as a when operand (`CASE CAST ( NULL AS EDGE ) WHEN IS DIRECTED ..`):
by cor 1's 20.7 SR 2 g the rewrite `operand IS DIRECTED` needs a singleton
element variable reference. no element predicate when operand is generated now
(`refine::NoElementWhen`), the checker reports one. weak checks closed:
SESSION SET GRAPH's expression typed (11.1 SR 3); a character string form takes
character strings and a byte string form bytes (20.23 SR 2, 4, each tree as
written). GG22 named in the claim (18.2 SR 9 a)

## 2026-10-25: the fourth review

two printed families, both in the whole grammar set, both sentences no
environment can make valid:

- a DROP parent holding an object name (`DROP GRAPH / a . a`): 12.5 SR 2 and
  12.7 SR 2 want a schema, and a schema holds no schema (4.2.5.3). the
  audit had closed them as environment. `refine::SchemaParents` refuses an
  object name in a CREATE or DROP parent; the checker reports it
- a name made and referenced at once (`CREATE GRAPH TYPE a COPY OF a`): 12.6
  SR 5 says it does not exist, 17.3 SR 1 that it does. H1 had said every named
  object exists, which contradicts every plain CREATE. H1 now splits references
  (exist) from made names (do not); `tree.rs:fresh_created_names` spells a
  made name apart from every other one (it appends, so the productions the
  name was chosen for stay); the checker reports a clash

weak checks closed: 10.3 SR 8 compared coarse classes only (`VALUE x CHAR =
SESSION_USER` passed): no length-bounded string type is declared now, at any
depth of the declared type, and ID061 is in H2. a list casts to a list only
(20.8 SR 11 a, literal now); its element types are the gate's (`20.8 SR 11 d`
in `GATE_ONLY`). 21.2 SR 42 rests on the leaf check refusing a reverse solidus,
not on the grammar alone. 17.6 SR 1 b turned out literal already (a stale note)

readings that let more in: nine rows moved from `reading` to a new status,
`permission`, each named in the claim's new H4 (the null type meeting a typed
site, a dynamic parameter typed by the request, the kind-less edge type
pattern, a supported string supertype). `audit.py` fails on a permission row
H4 does not name

## 2026-10-25: the fifth review

no printed sentence broke a rule (the regenerated sets and a fresh 1 variable
run). what it found was in the argument and the tools:

- the scope checker skipped session commands and catalog-modifying statements:
  their scope rules rested on the generator's engine, outside the trusted base.
  both are walked now (a session command in an empty scope, a catalog statement
  in its statement's); an untyped `SESSION SET TABLE` body is typed too
- 22.19 SR 2 was a `reading` the generator does not keep: a dynamic LET or
  VALUE variable meets a CASE, COALESCE, NULLIF or list element through the
  cure in `meet`, and the checker refuses it (33 trees withheld at 1 variable,
  0 at 2). now `checked` (gate-only); the generator's combine refuses a lone
  dynamic input as well
- cover does not stop on a generator bug, it counts it; the claim said it
  stopped. the claim says what it does now
- `audit.py` did not fail on open rows or unprobed strings, and did not look
  for a red probe; it does all three now (seven rules got tree-level probes:
  the statement kind rules, 12.7 SR 2, 16.9 SR 3)
- `shall_coverage.py` read only the 2024 text; it reads cor 1's syntax rules
  too. the 14.7 SR 11 rewrite row is restated for cor 1 (one CALL per
  definition)
- 20.8 SR 4 read strictly (no immaterial type anywhere in a cast target), so
  it is no permission
- a root used as a schema and as a directory in one program (17.1 SR 2 a i
  against SR 5) is checked, gate-only
- in the claim: one environment judged before execution, a parameter at two
  types needs the cure, IL020, the cure's run-time exception, the checker's
  `x . a` reading in graph expressions, and three insert or set rows under H2'

## 2026-10-25: the sixth review

no printed sentence clearly broke a rule. the nearest, printed: object names
in a reference parent (`CALL / a . a ( )`, `CREATE GRAPH ab / a . a`,
`SESSION SET GRAPH / a . a . a`) need a catalog object holding catalog
objects, which the text's catalog never has (4.2.5.3). as with the fourth
review's DROP case, refused now in every parent reference
(`refine::SchemaParents`, the checker's "17.6 SR 5")

closed:

- the types checker skipped `GRAPH x . a` and `VARIABLE "x"` in graph and
  table expressions (an old reading against H3); the printed tree is typed now
- 16.8 SR 4 a ii: a value given a closed graph type could become a working
  graph whose labels nothing follows; refused (gate-only, a list or record
  element left alone)
- one name at two kinds of object (17.2 SR 2 with H1), gate-only; name
  comparisons use representative forms (`"a"` is `a`), in the checker and in
  the generator's respelling
- `shall_coverage.py` split five clauses wrongly (a nested `1) .. N+1)` list
  read as the next rule) and passed by luck: each ambiguous split is resolved
  by hand in the tool now, and an unresolved one fails it (1,019 rules)
- `audit.py` refuses a `generated` row whose only rule strings are gate-only,
  as a generator miss there is never counted: ten rows are `checked` now
- a float's exponent scale is settled to at most 8 (`FLOAT ( 8 , 88 )` was
  printed); H2 states the printed lengths and precisions exactly

## 2026-10-25: the seventh review

a printed family: `RETURN COUNT ( ( ( GRAPH CURRENT_PROPERTY_GRAPH ) ) IS NULL
) AS x`, the inner parentheses under a numeric, character string or byte
string primary (20.21 SR 3, 20.23 SR 2, 4). the generator let an opaque value
(a graph, a table, a VALUE subquery) through every category site, and the
checker, by an old design note, never checked a bare category: it judged
categories only at operators. with H3 the printed tree is judged, so:

- the checker checks each category over a bare primary (numeric, character
  and byte string, list, path, boolean, node, edge, record) and each numeric
  term or factor on the printed tree, under per-tree strings (`20.21 SR 3
  primary` and the like) so the operator checks stay tree-independent
- the generator refuses an opaque child at a category site; a deferred
  variable still goes on, narrowed by the site
- a deferred class reaching a node that reads no class is settled on its
  variable instead of dropped (`push`)
- every per-tree site string is gate-only: the generator loses a deferred
  variable's narrowing when the variable is projected away at a RETURN (the
  closing check reads scope's view there, which carries no kind), so `MATCH (
  x ) RETURN x` is accepted on the trees reading x as a number, a string or a
  path; extraction picks such a tree mostly for `RETURN x` before `NEXT YIELD`
  (118 withheld at 1 variable). the gate keeps them out; fixing it means scope
  telling the types engine a projected variable's kind
- a VALUE subquery is opaque to the generator, so no category takes it now:
  `RETURN VALUE { RETURN count(*) AS y } AS x` is refused by reading

the second part of the seventh review (no printed sentence):

- an element variable reference naming a value variable of null or dynamic
  type passed (`LET y = x . a FILTER y IS DIRECTED`); the cure replaces value
  expressions, not a bare reference. the scope checker wants a node or edge
  variable now (16.10 SR 3)
- 16.3 SR 20's reading said same kind only, the checker let a value column
  join anything; same kind only now, and no value column (the generator's
  rule)
- the gate was traced: every printed tree passes the full checker, no other
  path prints
- stale notes fixed: 13.3 SR 3 a iii, 20.8 SR 4, 9, 20.16 SR 1 a

## 2026-10-25: the eighth review

a printed family: `SESSION SET GRAPH ( $b * + NULL )`. on its tree `$b * + NULL`
is a duration term, whose type is the duration operand's (20.28 SR 2 a), the
null type: no material graph type (11.1 SR 3 a ii). the generator typed the
term dynamic from $b; the checker typed arithmetic over two unknowns unknown.
now:

- an operator, a function, a concatenation or a literal at a graph or table
  expression is refused on its tree (`11.1 SR 3 primary`, gate-only: MIN or
  MAX of a dynamic value is still dynamic to the generator), as is a null or
  empty type there (material)
- the generator types a duration term by its duration operand and refuses a
  null or dynamic one there and in a duration addition; a datetime moved by a
  duration is a datetime, never dynamic
- a duration addition's operands are durations on its tree (`20.28 SR 1
  primary`, gate-only)
- ABS, MOD, ELEMENTS and an unwritten list element type keep a dynamic type
  dynamic, so 22.19 SR 2 sees it
- with GROUP BY the aggregating items are typed with the grouping aliases
  (14.11 SR 10 a ix)
- the property source of `9.M` is typed on the property tree (H3)
- ELEMENT_ID is refused under every category (ID076 in H2); H2' names 10.3 SR
  8, 7.1 SR 6, 10.1 and 10.2 SR 8
- a SELECT's WHERE to LIMIT come only with a FROM body, which the checker
  refuses, so the scope checker's skipping them is moot

## 2026-10-25: the ninth review

no printed sentence broke a rule (the sets, a fresh 1 and 2 variable run, 5,040
distinct sentences; about 1,440 traced by hand from their targets). six lenient
places in the checker, none reached by a printed sentence, all closed:

- a sign, LEFT, RIGHT, TRIM, UPPER, LOWER, NORMALIZE and TRIM of a list keep a
  dynamic or null operand's type (they gave unknown, so 22.19 SR 2 and the
  property sites missed it)
- arithmetic where several rows fit types the result by its node on the tree
  (numeric, datetime, duration), a dynamic operand keeping it dynamic
- variables are keyed by their representative form, as scope keys them
- no NOT NULL inside a list or record type, declared or cast to (nested
  nullability is not followed; reading)
- `- NULL` keeps the null type, so a property site refuses it
- ELEMENT_ID only directly as a RETURN or SELECT item (reading, ID076)

its second part (claim text, H):

- ID004 cannot rest on the implementation's one choice when printed casts of
  `[ ]` need different ones: `[ ]`'s element is read as ANY, a cast of it and
  a combination holding it are refused
- H2's property line names what S inserts, sets and assigns, not only casts
- a parameter an earlier SESSION SET of the program set has that type (22.1
  SR 5 d i); the checker had typed every `$b` unknown
- 20.26 SR 1 is a reading (the operator forms only), not as written

## 2026-10-25: the tenth review

- a printed family: `INSERT ( ) NEXT SELECT CURRENT_DATE AS x` (15 in the
  whole grammar set; the eleventh review showed it valid after all: 14.12 SR 1
  applies the SELECT rewrite before every other rule, so the stricter reading
  below is kept for safety, not to fix a break). 9.2 SR 5 names the grammar's focused and ambient
  statements, and a SELECT is a focused one as written; the checker and the
  automaton read it as its replacement, ambient, which lets this through. a
  SELECT is now both, so it stands beside no other focused or ambient
  statement (9.2 SR 5 and 14.2 SR 4), in the checker and in StatementKinds
- 16.7 SR 15 c i read literally ("contained in" the concatenation, through
  parentheses) gives `( ) <- *` a minimum node count of 0 and breaks SR 16; it
  can also go below 0, a defect. the touching-pair reading the checker and the
  generator use lets more in: 16.7 SR 16 and SR 20 are permissions in H4 now,
  and the SR 14 rewrite row's "the readings differ only above 0" is corrected
- the second part: H1's catalog argument corrected (refusing object names in
  a parent is a narrowing, the text lets a primary catalog object hold
  objects); IE001 named in H2 for `COPY OF urn:..`; a stale audit note on
  subqueries in graph patterns

## 2026-10-25: the eleventh review

no new printed family breaking a rule the checker reads strictly; one family
resting on a defect the claim had not named:

- 12.8, 13.6 and 14.5 SR 2 ask the nested procedure specification to
  immediately contain a kind of specification, which by 5.3.2.1 it never does:
  literally no inline CALL, OPTIONAL or LET is valid. the checker reads one
  level further down; a permission in H4 now. 13.1 SR 5's "STMSEQ shall
  contain" read with 5.3.2.1 containment is one too
- lenient places closed: a root schema beside a `..` step (17.1); bare names
  in graph and table expressions and directory names in the one-kind and
  created-name checks, in the checker and the generator's respelling (17.2,
  12.x); a LIKE source with a possibly open type (12.6 SR 7 b iv, gate-only);
  20.8 SR 5's "CO specifies NULL" as containing one, literal or keyword

its second part: the tenth review's SELECT family was valid (14.12 SR 1); the
no-subquery-in-a-pattern premise of three readings was false, and 16.6 SR 8
now refuses any subquery in a selective path pattern; 18.9 SR 11 read
literally bounds STRING too, so 10.3 SR 8 b i 1 is a permission in H4; 6 SR 4
is IW014 (H2), not a reading; `gql-proof cover` is noted as no check

## 2026-10-26: the twelfth review (a sweep of every relied-on row)

six agents, one per group of clauses, against the text. one printed family:
`[ - NULL ]` read as a list literal (21.2 SR 73: a literal signs only an
unsigned numeric literal), in all three sets; closed in the checker and in
refine::LiteralElements. the rest unprinted, closed:

- names: delimited identifiers refused as variables, fields, properties,
  parameters and aliases (one spelling for every comparison); delimited graph
  and table names in the created-name and one-kind checks and the respelling
- clause 18: a saturating length or precision is refused; a GROUP LIST of ANY;
  a nested union's NOT NULL components in the syntax-side SR 88; 18.9 SR 28
  joins the SR 11 permission
- clause 21: exact ISO shapes for date and time strings, a duration of at
  least one field, an interval of at most two leading digits, a URI scheme
- clause 14, 19, 22: a combination checks its known inputs past an unknown
  one; DURATION records get their unit from their fields; ELEMENT_ID in a set
  operation; singleton degree inside aggregates for element predicates; 14.10
  SR 4 reads an aggregate anywhere in the items
- clause 16: a nested KEEP search prefix; a value variable as a bound INSERT
  node; ABS keeps NULL; incoming names under a selective pattern or a
  parenthesized WHERE; every element variable reference, YIELD items
  included; YIELD in catalog statements; 16.7 SR 21 read deeply
- clause 20: a nested TRIM's outer source, a record's own fields, a nested
  table's rows, temporal functions' record arguments, immaterial and nested
  NOT NULL SESSION SET VALUE types, closed union cast targets (subtyping by
  kind only)
- clauses 7 to 12: a second SET of a table parameter, subquery statements in
  a catalog procedure's definitions (9.1 SR 5)
- claim: H1 states what a named procedure without YIELD returns; H2' names the
  rows resting on the cure in clause 20; H4 adds 18.9 SR 28

## 2026-10-26: the thirteenth review

the reviewer built a copy and ran every printed sentence through the checker.
a printed family from a fresh run: `SELECT LET VALUE x ANY = CURRENT_DATE IN [
CEIL ( x ) , .. ] END AS z`. 20.5 SR 5 types a LET .. IN name by its
initializer FE, so x is DATE and CEIL ( x ) breaks 20.21 SR 3; the checker and
the generator used the declared ANY, which the cure accepts. the checker binds
by FE now, and refine::UntypedLetValues writes no typed definition inside a
let value expression (its twin "20.5 SR 5" in the checker)

its second part: a fresh 2-variable run prints exactly the cached set; 110
hand-written probes in clauses 16 to 22 were all flagged as the text says.
fixed: quantifier bounds capped at 255 (IL018 in H2; `{ 888 }` was printed for
turbolay's claim); the claim's rule count (1,019) and grammar rows (10); H1
says which names a made name must differ from

## 2026-10-26: main merged, three variables

main's extraction speedups merged (0e30462): the whole grammar at 2 variables
in 45 s, at 3 variables in 34 min on a shared machine, 3,075 sentences, no
generator bug, 5,249 of 5,298 productions.

## 2026-10-26: the fourteenth review (several variables)

no printed counterexample at 1 and 2 variables, whole grammar and turbolay;
about 90 multi-variable sentences traced by hand. lenient places closed: a
schema dropped while AT sets it or the program names into it (12.3 SR 7); a
binary set function's independent value expression sees the record, not the
group table (20.9 SR 9 g, h); an earlier MATCH's variable is exterior to a
selective pattern (16.6 SR 7); no LET expression in a sort key (14.10 SR 4,
reading). H1 states the session state S needs

its second part: no printed counterexample at 3 variables either (whole grammar
3,075 lines, turbolay 3,473). the first round with none. 3 variables add 16
sentences in all, three-field or three-definition variants; the multi-variable
interactions are not printed at all, because the cover targets are met at 1
or 2. noted in the claim

## 2026-10-26: the fifteenth review (other claims, settings, the lexical layer)

two printed families, both resting on defects of the text read the lenient way:

- every SQL interval literal: 21.2 SR 72 makes `INTERVAL '1' DAY` the duration
  string `PD1`, designator before value, which SR 68 refuses; the rewrite row
  had said consequence none. none is generated now (refine::NoSqlInterval, the
  checker's "21.2 SR 72")
- a date moved by a duration (`DURATION_BETWEEN ( NULL + CURRENT_DATE ,
  LOCAL_TIMESTAMP )`): 20.26 SR 1 read literally makes it a local datetime, a
  defect an engine typing it DATE would not share. only a datetime is moved
  now, in the generator and the checker ("20.26 SR 1 moved", per tree)

its second part: other match-mode defaults, witness settings and the lexical
layer hold; the neo4j claim prints 41,802 sentences no round had seen. fixed:
H2's limits (quantifier bounds, lengths, precisions) are checked on the tree
(`verify::h2_bounds`, gate-only) instead of resting on the generator; the
theorem holds under any `--claim` and `--match-mode-default`
- a TRIM count over a parameter (`CARDINALITY ( .. ) + $b`) was typed a number
  of unknown scale when one operand was the environment's; it is unknown now,
  as two unknown operands were (260 neo4j trees had been withheld as generator
  bugs on it)
- the neo4j claim at 2 variables: 42,061 sentences, no rule broken by any
  printed one; 34 trees withheld as generator bugs on 12.8 and 13.6 SR 2
  (`CALL { CALL a ( EXISTS { CALL ( ) { FINISH } .. } ) }`, a kind no parse
  has): the generator misses them under that claim, the gate keeps them out

## 2026-10-26: the sixteenth review (the neo4j claim set)

no printed sentence of the neo4j set (42,061) breaks a rule: its new territory
(EXISTS in WHERE, property specifications, CASE and grouped items; GROUP BY on
variables; PROPERTY_EXISTS; label expressions in WHERE) hand-checked by class
and swept, about 70 probes flagged as the text says. closed (unprinted): one
named procedure called as two kinds (12.8, 13.6, 14.5 SR 3 with H1)

## 2026-10-26: the seventeenth review and the unknowns audit

the seventeenth review found two breaks. no other printed sentence broke a rule
across fresh runs (whole grammar and turbolay at 1 and 2 variables in three
modes, turbolay at 3, neo4j at 1 in three modes and at 2 under REPEATABLE
ELEMENTS). the reviewer checked the rarest targets by hand.
- `DURATION ( { } )` was printed in a duration addition (`ORDER BY NULL -
  DURATION ( { } )`). 20.29 GR 2 gives a record naming no unit field no type, so
  20.28 SR 1 a cannot hold. no DURATION takes a record now (`refine::NoDurationRecord`,
  the checker's "20.28 SR 1 record"). this also covers mixed and upper-case fields.
- a claim without GG22 printed graph type bodies with an omitted key label set,
  which 18.2 SR 9 and 18.3 SR 10 require under that claim. the gate checks them
  now ("18.2 SR 9", "18.3 SR 10", gate-only), and the audit rows are constraints.
  `shall_coverage.py` now also counts requirements worded as a syntax error or
  "is not omitted". four definitional rules are exempt.
- lenient checker places, none printed: a NOT NULL cast of NULLIF or of a CASE
  without ELSE ("20.8 SR 5 contains" counts their rewrite's NULL now).
- claim text: stdout, the purdom paragraph (its stderr note now says what
  `--rules` and `--grammar` checked), H2's property counts (up to four property
  types, one distinct label), H2' stated by the operand's type rather than an
  open list, H2''' and GG22, and a note that static validity leaves run-time
  failures (a node with two properties named alike) outside the theorem.

the unknowns audit (`research/audit/unknowns-2026-10-26.md`) classified every
source of the type checker's unknown. five let a broken sentence pass, none of
them printed: ELEMENT_ID's value through a column or a VALUE (now `Ty::Opaque`),
a table variable's row (tables now carry their columns), a FOR over a dynamic
source (its elements are dynamic), and a FOR over NULL and `NULL || NULL` (both
refused, gate-only).

runs after the fixes (`--join --keys --cdrc --deadline 3600`, different edges):
- whole grammar: 1 variable 3,265 rows (289 withheld); 2 variables 3,055 rows
  (523 withheld), 40 s
- turbolay: 2 variables 3,400 rows (186 withheld), 29 s; 3 variables 3,408 rows
  (198 withheld), 194 s
- neo4j: 1 variable 41,103 rows (1,580 withheld), 113 s

0 generator bugs, apart from neo4j's known 34 (12.8 and 13.6 SR 2). the
never-covered production counts are unchanged at 38, 160 and 150. the 47 lost
turbolay sentences that use DURATION are the record forms, now refused.

## 2026-10-27: the eighteenth review, part 1

no printed counterexample. fresh runs: the whole grammar and turbolay at 2
variables in all three modes; the whole grammar at 1 variable, portable; neo4j
at 1 variable in all three modes and at 2 variables, portable (40,892 rows). the
56 new sentences are mode-only pattern variants, all checked against 16.4 and
16.7. every printed sentence with `||` (48), CAST (414), NOT NULL (371) and TRIM
was read by hand. four gaps, none printed, all closed:
- binding tables combined whatever their columns (combine took the first's).
  a table type is closed by its columns (22.19 SR 4 n iv), so the known columns
  must agree; a set operation over them is refused too ("14.2 SR 10")
- a parameter at a material graph site and in a combination (`USE $b .. COALESCE
  ( $b , 1 )`): no request type serves both. H1 is satisfiable now: a parameter
  in a combination of unknown inputs is written once ("22.19 SR 2 parameter",
  gate-only), and a dynamic type serves every other use through H2'
- a list's maximum cardinality was unbounded (`LIST [ 99999999999999999999 ]`).
  h2_bounds caps it at 888 ("18.9 SR 73", gate-only), and H2 names IL015. the
  row's "reachable: no" was wrong: `LIST [ 8 ]` is printed
- 20.6 SR 10 a read `LIMIT 0x1` as `LIMIT 1`; it reads the spelling `1` now

runs after the fixes: counts identical to the seventeenth review's (whole
grammar 3,055 rows, turbolay 3,400, 3 variables 3,408, neo4j at 1 variable
41,103), with 0 generator bugs apart from neo4j's 34.
