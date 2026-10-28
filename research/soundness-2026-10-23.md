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

## 2026-10-27: the eighteenth review, part 2 (a clean round)

no printed counterexample in the round, so it counts as clean, as the
fourteenth and sixteenth did. part 2 closed the open gaps of the unknowns audit
(`research/audit/unknowns-2026-10-26.md`):
- no lost name over all whole grammar and turbolay sentences, or a 4,200
  sentence neo4j sample
- `Ty::Number` sound
- `Ty::Graph` adds nothing beyond part 1's tables

hand probes:
- 63 ELEMENT_ID forms
- 84 forms of FOR over a table
- CAST's table, cell by cell
- 66 pattern probes
- about 110 comparison and function probes

all were flagged as the text says. one tool fix: shall_coverage.py's cor 1 pass
now uses the wider requirement test (shall, a syntax error, not omitted).

## 2026-10-27: the nineteenth review, part 1

no printed counterexample, but the claim's H1 sentence ("some request type
serves every S") was false. this round is not clean. three unprinted gate holes,
all closed:
- aliasing defeated "22.19 SR 2 parameter". `USE $b LET y = $b .. COALESCE ( y ,
  1 )` passed, and no request type serves both uses. the same happened with a
  named procedure's YIELD column. the check reads every unknown input now: only
  a bare parameter written once may be one ("22.19 SR 2 unknown", gate-only,
  replacing the parameter string)
- 11.1 SR 3 a ii and 11.2 SR 4 b ii want a *material* reference type under
  VARIABLE. `SESSION SET GRAPH CAST ( NULL AS ANY PROPERTY GRAPH )` passed, and
  so did a LET or FOR variable holding a nullable graph or table type. the
  checker follows no nullability of static reference types, so only an unknown
  (H1) or dynamic (H2') value is taken there ("11.1 SR 3 material", "11.2 SR 4
  material", gate-only). no printed sentence uses a variable at a graph or table
  site, so this costs no coverage
- a closed graph type in a list or record reached a working graph (`USE CAST (
  NULL AS RECORD { g PROPERTY GRAPH { ( :a ) } } ) . g MATCH ( :b )`). the
  premise of the 16.8 SR 4 check, that such an element is never a graph
  expression, was false: a property reference is an object expression primary,
  and FOR binds list elements. the material check refuses every static graph
  type there now, so the premise holds by the gate

runs after the fixes: counts unchanged at 2 and 3 variables and for neo4j; the whole grammar at 1 variable withholds 34 more (323), the aliased parameter shapes, with no production lost; 0 generator bugs apart from neo4j's 34.

## 2026-10-28: the nineteenth review, part 2

no printed counterexample. the round's findings are the three unprinted holes of
part 1, so the round is not clean. part 2 adds no finding. its three argument
gaps (H1 for a procedure's column, the 16.8 comment, the material comment)
were written against the code before part 1's commit and are closed there.

runs by the reviewer, new territory: claims GC00 only (each match mode, 1-3
variables) and GC04 GG01 GG02 GG21, about 18,000 sentences no earlier set holds
(OPTIONAL MATCH, aggregates, EXISTS in element WHERE, CASE, LEFT, TRIM,
NORMALIZE, properties of open elements). checked by class against the text, no
break. under these claims the gate withholds about 6,400 trees per run on rules
outside GATE_ONLY, mostly 20.1 SR 7 (an aggregate under an inner value
expression): a generator gap, coverage not soundness, open.

also checked: graph type bodies (about 40 probes on 18.1-18.3), the scope
checker on 16.4, 16.6, 16.7, closed types through records, lists and FOR, the
lexical layer against clause 21, the 76 reading rows (all strict) and the 17
permission rows (all in H4). no requirement phrased without "shall" is uncovered.

a tool note: a 3 variable repeatable-elements run on a reviewer claim ran past
its --deadline 3600 by hours in the search phase and was stopped. the deadline
does not bound that phase. speed, not soundness.

## 2026-10-28: the twentieth review

no printed counterexample. two unprinted gate holes, each making a sentence of
the claim or the audit false, so this round is not clean. both closed:
- 14.10 SR 4 c reads "contains" for the return's DISTINCT, GROUP BY and
  aggregate alike, and the checker read only the aggregate through a subquery.
  `MATCH ( x ) , ( z ) RETURN x , EXISTS { RETURN DISTINCT 1 AS a } AS e ORDER
  BY z` passed, and so did a nested GROUP BY. a DISTINCT, a GROUP BY or a set
  operator (one without a quantifier is DISTINCT, 14.2 SR 1; found on the
  re-check) anywhere in the items now leaves the sort keys the returned columns
  alone, the meet of every reading. the audit row's "stricter" was false for
  these trees
- 22.19 SR 4 combines list elements, record fields and table columns again, so
  SR 2 holds at every depth, and "22.19 SR 2 unknown" read only an input's top
  type. `COALESCE ( RECORD { a : $b } , RECORD { a : 'a' } ) .. $b + 1` and a
  COLLECT_LIST column passed, which no request type serves. an unknown at any
  depth of an input or set-operation column is refused now (`nested_unknown`).
  the reviewer's splice harness, built from clean subtrees, finds 0 clean trees
  of 9,126 and 118,638 (2,106 and 4,212 before), and 0 for the CASE, NULLIF and
  UNION variants

also checked and found to hold: INSERT, SET, REMOVE, DELETE; ORDER BY, OFFSET,
LIMIT, GROUP BY and aggregates; session, transaction and catalog statements;
procedure calls and YIELD; value types (18.9, 18.10); CAST; CASE, NULLIF,
COALESCE; VALUE subqueries; TRIM; datetime and duration; record field names.

a method note from the reviewer: a probe flagged on every parse at the 2048
parse limit proves nothing when the limit is reached before the intended tree.
splicing clean subtrees into a host reaches the exact tree.

runs after the fixes: every count unchanged (1 variable 3,231 and 323 withheld;
whole grammar 3,055 and 523; turbolay 3,400 and 186; 3 variables 3,408 and 198;
neo4j 41,103 and 1,580); 0 generator bugs apart from neo4j's 34.

## 2026-10-28: the twenty-first review

no printed counterexample. two unprinted gate holes, each making the claim's
"H1 is never vacuous" false, so this round is not clean. both closed:
- a combination with an unknown input checked its known inputs only when there
  were two or more, and typed its result unknown, waiving every rule after it.
  `RETURN NOT COALESCE ( $b , 1 )` passed (39 of 507 parses), as did
  `COALESCE ( $b , CAST ( NULL AS LIST < ANY > ) )` and the CASE forms. no type
  of $b serves them. the known inputs now always combine, one alone included,
  and the result is theirs, which is what H1 gives the bare parameter
- a catalog table read as a value (`TABLE a`, columns unknown) combined with
  any column set and took it, so `COALESCE ( TABLE a , TABLE { RETURN 1 AS b }
  ) .. COALESCE ( TABLE a , TABLE { RETURN 1 AS d } )` passed (81 of 243
  spliced trees), and no table type serves both. a table of unknown columns
  counts as an unknown input now, at the top and at depth. all 507 parses of
  the single combination are refused, and the check is local to that node

also checked and found to hold, a sweep for checks that read only the top
level where the text says "contains" or recurses: 9.1 SR 5-7, 9.2 SR 4-7,
14.2 SR 3-5, 14.10 SR 4, 14.12 SR 19 and 27, 16.4 SR 6, 16.6 SR 8, 16.7 SR 9,
20.1 SR 7, 20.9 SR 3, 4, 7, and the recursion of assignable, subtype,
comparable and the CAST checks.

runs after the fixes: every count unchanged (1 variable 3,231 and 323 withheld;
whole grammar 3,055 and 523; turbolay 3,400 and 186; 3 variables 3,408 and 198;
neo4j 41,103 and 1,580); 0 generator bugs apart from neo4j's 34. (the neo4j
and 3 variable runs took 548 s and 873 s against 105 s and 193 s, with a
virtual machine on the same host using about two cores.)

## 2026-10-28: the twenty-second review

no printed counterexample. one unprinted gate hole, making "H1 is never
vacuous" false, so this round is not clean. closed:
- a combination whose material inputs are all unknown (`COALESCE ( $b , NULL
  )`, `COALESCE ( $b , $c )`, NULLIF, a CASE without ELSE) was typed unknown,
  and the unknown waived what followed: `LET y = COALESCE ( $b , NULL ) FOR x
  IN y RETURN y + 1` passed (13,182 clean of the first 30,000 parses). H1 must
  give $b one static type, list for the FOR and numeric for the `+`. such a
  combination is refused now ("22.19 SR 2 unknown"): 0 clean of 30,000 for
  each form, the controls (`LET y = $b ..`, `COALESCE ( $b , 1 ) + 1`) still
  pass

also checked and found to hold: a differential run of 103 probes over every
site class, each with the parameter typed unknown and again typed dynamic
(Dyn(Open)); the verdicts differ only at a combination (`LIST [ $b ]`). so
outside a combination a dynamic environment serves every use, which is what
H1's non-vacuity rests on. aliasing through session parameters is served by a
predefined session parameter (7.1 SR 6 d i, 22.1 SR 4 c i); procedure columns
without YIELD, procedure arity (a range, 15.3), catalog tables and LIKE
sources hold.

the four last rounds all found holes in the same place, how the checker types
the environment's unknowns at a combination. the differential run above is
the structural form of the argument and is worth keeping as a test.

### H1 made a check

after four rounds of H1 holes, the prose argument that some environment serves
every S is replaced by a check. `types::check` types S a second time in one
environment E: a parameter written once as a combination's input has the type
the other inputs combine to, every other unknown the environment gives is
dynamic (H2' cures it outside combinations). a rule broken only in E is
reported as "H1 environment" (gate-only).

cost: the 1 variable run withholds 1 more (3,230 rows), neo4j 220 more (40,883
rows, 1,800 withheld), the rest unchanged, no new generator bug. the 220 are
the TRIM count family, `TRIM ( NULL , $b + CARDINALITY ( MAX ( NULL ) ) )`: in
E, `$b + 1` with $b dynamic is a number of unknown scale, not the integer a
TRIM count needs, though $b INTEGER serves it. so E is stricter than needed
there, a coverage lever (type an arithmetic result over a dynamic operand
dynamic), not a soundness one.

## 2026-10-28: the twenty-third review

aimed at the second typing pass. no printed counterexample. one unprinted gate
hole and one false sentence, so this round is not clean. both closed:
- list concatenation dropped a dynamic or unknown operand before the 20.15 SR 2
  combination, and passed no input nodes, so neither "22.19 SR 2" nor the H1
  check saw it: `RETURN [ 1 ] || CAST ( NULL AS ANY )` (84 of all 4,368
  parses), `[ 1 ] || x . a`, and `USE $b RETURN [ 1 ] || $b`, which passed
  both passes and which no environment serves. both operands and their nodes
  now go to `combined`, as at the list constructor
- the claim says arithmetic over a dynamic operand keeps it dynamic, but `+`
  and `-` with a numeric operand, FLOOR and CEIL gave a number, so `COALESCE (
  x . a + 1 , 2 )` passed. they keep it dynamic now, which also makes E's
  `$b + CARDINALITY ( .. )` a cured TRIM count

checked and found to hold: every environment unknown is dynamic in the second
pass (parameters, unset session parameters, procedure columns with and
without YIELD, catalog table rows and fields, catalog tables and graphs); the
remap is sound at every combination site, types and nodes aligned, and
combine(T, known) is combine(known) for T = combine(known) in every class; set
operations refuse dynamic and unknown columns; the dedup only relabels. none of
the 1,524 distinct concatenation sentences in the neo4j sets has a dynamic or
unknown list operand.

runs after the fixes: neo4j back to 41,103 rows and 1,580 withheld (the 220 TRIM
count sentences are served in E now); whole grammar, turbolay and 3 variables
unchanged; the 1 variable run 3,227 rows (3 fewer than with the second pass
alone). the 3 are `SELECT LET x = $b IN [ [ CEIL ( x ) ] , .. ] END` and its
FLOOR and CEILING forms: valid with $b INTEGER, refused in E, where CEIL of a
dynamic $b stays dynamic and meets a list constructor. coverage, not
soundness: E types a parameter that is not itself a combination's input
dynamic. 0 generator bugs apart from neo4j's 34.

## 2026-10-28: the twenty-fourth review

two sweeps of types.rs: every site that filters, drops or defaults a type
before a check, and every site where the text applies 22.18/22.19. no printed
counterexample. one unprinted gate hole and one false sentence, so this round
is not clean:
- list concatenation with no operand of a known class (`$b || $c`, `x . a ||
  x . a`, `CAST ( NULL AS ANY ) || CAST ( NULL AS ANY )`) built a list of
  unknown or dynamic elements and never reached `combined`; `FOR x IN $b || $c
  FOR y IN x RETURN x + 1` passed both passes. a dynamic or unknown operand now
  goes to the combination there too (round 23 had fixed only the arm with a
  typed list). an instrumented run found the arm on 0 printed trees
- the claim said arithmetic over a dynamic operand stays dynamic, but a
  temporal row that fits alone (`LOCAL_TIMESTAMP + x . a`, a duration times
  or over a number) gives its fixed type. the verdicts are right by the text
  (every arm of the cure has that type); the sentence is corrected
- an observation, now stated in H2': the CASE 4.14.4 builds is itself a
  combination and is not judged again; the cured variant is how the
  implementation executes S

the sweeps list about 30 filter or default sites and 9 combination sites, all
others held; an instrumented copy flagging every arm that returns unknown
without a report fired 0 times over 7,139 printed sentences and four
generation runs.

runs after the fixes: every count unchanged (1 variable 3,227 and 327 withheld;
whole grammar 3,055 and 523; turbolay 3,400 and 186; 3 variables 3,408 and 198;
neo4j 41,103 and 1,580); 0 generator bugs apart from neo4j's 34.

## 2026-10-28: the twenty-fifth review

aimed at the argument's chain (gate wiring, coverage, the audit) and verify.rs.
no printed counterexample. three unprinted gate holes, each making "H1 is never
vacuous" false, and one false sentence, so this round is not clean. all closed:
- `procedure_kinds` keyed a procedure on its written reference, so `CALL a ( )`
  as a query and `CALL CURRENT_SCHEMA / a ( )` (or `. / a`, `"a"`) as a data
  procedure passed, one procedure of two kinds. it keys on the representative
  form of the procedure's own name now, parent left out (the strict side)
- `schema_drops` compared paths as written: `AT / "a" DROP SCHEMA / a` and
  `DROP GRAPH / "a" / b DROP SCHEMA / a` passed. it compares the dropped
  schema's own name by representative form against the working schema's last
  name and every name of a parent path
- a named procedure called without YIELD is assumed (H1) to return no column
  named like an incoming field, and a YIELD on another call of it can show such
  a column: `MATCH ( x ) CALL a ( ) .. NEXT CALL a ( ) YIELD x` passed (78 of
  4,563 parses). a procedure called both with and without YIELD is refused now
  ("15.1 SR 9 yield", gate-only)
- the claim said four rules are exempt from coverage; the tool exempts eight
  (the four more are definitional "not omitted" rules, sound). corrected
- from an observation: IL010 (an unsigned integer of at most 9 digits) rested
  on H2's general clause; it is checked on the tree now ("21.2 SR 14",
  gate-only), the written digits and the value a 0x, 0o or 0b form stands for

checked and found to hold: the gate wiring (every printed sentence is the
rendering of the tree all four checkers and both typing passes judged; no other
print path); shall_coverage.py's clause attribution and requirement wordings,
and its eight exemptions; audit.py's statuses, `generated` rows quoting
non-gate-only strings (fail-closed); the 137 environment, implementation and
hypothesis rows; verify.rs's 16.7, 16.11, 14.2 SR 10, created names, kinds per
name, LIKE sources, H2 bounds, delimited names, the catalog root and reserved
words.

runs after the fixes: every count unchanged (1 variable 3,227 and 327 withheld;
whole grammar 3,055 and 523; turbolay 3,400 and 186; 3 variables 3,408 and 198;
neo4j 41,103 and 1,580); 0 generator bugs apart from neo4j's 34.

## 2026-10-28: the twenty-sixth review

a sweep of every name and identity comparison in the four checkers. no printed
counterexample. two unprinted gate holes, each with a false premise, so this
round is not clean. both closed:
- a session parameter S sets counted as a parameter written once: `SESSION SET
  VALUE $b = $c SESSION SET VALUE $e = COALESCE ( $b , 1 ) SESSION SET VALUE
  $b = 'x'` passed both passes (4,563 of 4,563 spliced trees), and no type of
  $c serves both the string assignment and the numeric combination. a session
  parameter specification of the name counts as a writing now
- `..` steps under an AT that names a schema absolutely: `AT / s CREATE GRAPH
  .. / .. / t / g ANY` steps above the root (17.1 SR 6 d i), and the depth was
  S's, not H1's. any `..` in a program with such an AT is refused now ("17.1
  SR 6 at", gate-only; no set holds the two together). the audit note and the
  claim's working-schema sentence said the depth was always the environment's;
  both are corrected

the sweep marked about 40 comparison sites in verify.rs, scope.rs, types.rs and
graph_type.rs held: confusables, one kind per name, delimited names (every
variable-like node is a regular identifier in the BNF), procedure kinds and
yields, schema drops, rep_names and ident, LIKE sources, created names, the
pattern variable clashes, labels, properties and graph type bodies.

runs after the fixes: every count unchanged (1 variable 3,227 and 327 withheld;
whole grammar 3,055 and 523; turbolay 3,400 and 186; 3 variables 3,408 and 198;
neo4j 41,103 and 1,580); 0 generator bugs apart from neo4j's 34.

## 2026-10-28: the twenty-seventh review

aimed at scope.rs's pattern rules, data-modifying and catalog statements, and
the rewrites. no printed counterexample. one unprinted gate hole, so this round
is not clean. closed:
- 16.6 SR 7 counted only earlier statements and the same graph pattern's other
  path patterns as exterior or other-selective, so a mirror image passed:
  `MATCH ANY ( a ) -> ( m ) -> ( b ) MATCH ANY ( m ) -> ( c )` (and with a
  plain second MATCH, or `WHERE EXISTS { ( m ) }`) while the reversed order was
  refused. SR 6 and 7 set no scope, depth or order, so a declaration of the name
  anywhere else in the program now counts (the strict side). every probe 0
  clean on all parses; a reused boundary variable still passes. no printed set
  holds a selective pattern that declares a variable

checked and found to hold: 16.7 SR 22 a-i against `expose`, SR 10 c, 11, 21,
24; 20.12 SR 10-12; 16.4 SR 3-6, 12, 14; 16.6 SR 5, 8; 16.3 SR 4, 7, 9, 12, 16,
20 and the SR 21 rewrite; 16.8 SR 4 under a closed type; INSERT, SET, REMOVE,
DELETE and their interplay with CALL, NEXT, FINISH, YIELD; 12.x created names,
drops, LIKE sources, the catalog root; the 19.4, 14.12, 16.3 SR 21, 16.7 SR 12
and 14 rewrites.

runs after the fix: every count unchanged (1 variable 3,227 and 327 withheld;
whole grammar 3,055 and 523; turbolay 3,400 and 186; 3 variables 3,408 and 198;
neo4j 41,103 and 1,580); 0 generator bugs apart from neo4j's 34.

## 2026-10-28: the twenty-eighth review

a sweep for order and direction dependence in all four checkers. no printed
counterexample. two unprinted gate holes, both in types.rs `pattern_vars`, so
this round is not clean. both closed:
- a variable a singleton in one union operand and a group in another took the
  first operand's type: `MATCH ( x ) | ( ( x ) -> ( ) ) { 1 , 2 } RETURN CAST (
  x AS NODE )` passed (9 of 1,014), its mirror was refused. 16.7 SR 22 d makes
  it an effectively bounded group; a group declaration now wins
- a pattern inside a parenthesized path pattern WHERE leaked its declarations
  into the outer pattern's types (scope saw none), and a later MATCH binding the
  name kept the phantom type. that WHERE is skipped now, as the other two were

each probe 0 clean on all parses; a union of two singletons still types a
node. no printed set holds a union whose operands declare one variable, nor a
subquery declaring a variable in a parenthesized WHERE.

the sweep marked about 50 order-dependent sites in the four checkers held,
graph_type.rs's 18.1-18.5 pairwise and first-match checks included. an audit
note (16.5 SR 10 b "never redeclared") described the generator, not the
checker; clarified.

runs after the fixes: every count unchanged (1 variable 3,227 and 327 withheld;
whole grammar 3,055 and 523; turbolay 3,400 and 186; 3 variables 3,408 and 198;
neo4j 41,103 and 1,580); 0 generator bugs apart from neo4j's 34.

## 2026-10-28: the twenty-ninth review

facts scope.rs and types.rs each compute on their own. no printed
counterexample. three unprinted gate holes, all on group variables, so this
round is not clean:
- types.rs gave a group variable singleton type in a parenthesized WHERE of the
  pattern declaring it under a quantifier: `MATCH ( ( ( x ) -> ( ) ) { 1 , 2 }
  WHERE CAST ( x AS NODE ) IS NULL )` (9 of 1,014 clean)
- inside every aggregate, vertical too, a group variable was typed as its
  element: `RETURN SUM ( x . a )` over a group x passed, though a vertical
  aggregate's argument sees the whole list (20.9 GR 5 b); a reading the claim
  never named
- 20.1 SR 7 was judged by scope's degree bookkeeping, which follows only a bare
  reference: `LET y = ( x ) .. COUNT ( COALESCE ( y , x ) )` passed (2,187 of
  2,187 spliced), as did a CAST to a GROUP list type

no set prints a group variable (none declares an element variable under a
quantifier, over 49,673 distinct sentences) nor a GROUP list type. rounds 28
and 29 found four holes in this one family, so it is withheld whole now: an
element variable declared under a quantifier or a written GROUP list type is
refused on the tree ("16.7 SR 22 group", gate-only). the two readings the
types.rs header states for group variables are no longer relied on.

the comparison marked agree: bindings per statement, FOR over a group, LET
shadowing, columns after RETURN, GROUP BY and ORDER BY, set operation columns,
SELECT, union degree, `?`, subpath and path variables, subquery scope, a
variable's kind.

runs after the change: every count unchanged (1 variable 3,227 and 327 withheld;
whole grammar 3,055 and 523; turbolay 3,400 and 186; 3 variables 3,408 and 198;
neo4j 41,103 and 1,580), so withholding the group family cost no printed
sentence; 0 generator bugs apart from neo4j's 34.

## 2026-10-28: the thirtieth review (clean)

the first clean round since the eighteenth: no printed counterexample, no gate
hole, no false premise an argument step uses. the reviewer parsed all 50,823
distinct sentences of the sets (limit 64), grouped them by construct family,
probed about 120 printed-adjacent variations (CALL scope, YIELD, set operation
columns, LET, FOR, VALUE, SET and REMOVE, KEEP, graph type bodies, catalog
names across spellings, ELEMENT_ID through columns, element predicates,
session parameter typing, joins, named procedure columns in combinations) and
read combine, assignable, cast_fault, combined and parameter_once against the
text. all held. one stale clause in an audit note (16.7 SR 17, "no set holds
TEMP": an old set did) is corrected; no step used it.

a method note: the inherited probe harnesses build the verifier without the
claim's conformance devices, so TEMP, NO BINDINGS and one-component unions
look clean there; the real gate refuses them.

the round also mapped every family the checkers reason about that no current
set prints. five of them, where rounds 18-28 found their holes, are withheld
whole now ("withheld family", gate-only): a parameter inside a combination, a
session parameter set by one command and read by another, a named procedure
call with YIELD, a selective path pattern that declares an element variable,
and a path union or alternation that declares one. this only refuses more.

runs after the change: the first parameter detector (any parameter inside a
CASE) withheld 59 printed neo4j sentences (`CASE SESSION_USER WHEN ( $b ) .
a ..`, `CASE WHEN NULL = TRIM ( NULL , $b ) ..`), whose parameter is no
combination input; it now takes only an input that is a bare parameter (a CASE
result, a COALESCE or NULLIF operand, a list element, a concatenation
operand). every count is then unchanged (1 variable 3,227 and 327 withheld;
whole grammar 3,055 and 523; turbolay 3,400 and 186; 3 variables 3,408 and
198; neo4j 41,103 and 1,580); 0 generator bugs apart from neo4j's 34.

## 2026-10-28: the thirty-first review

not clean: one printed family resting on an unnamed lenient reading, and one
unprinted gate hole. both closed, and a third reading named:
- printed: `VALUE x DATE = CURRENT_DATE FINISH` and four ZONED TIME, LOCAL
  TIME and TIME forms of CURRENT_TIME (turbolay, 2 and 3 variables). 20.26 SR
  1 types every <datetime value expression> a zoned or local datetime, and a
  bare date or time primary derives only through one, so read literally no
  expression has a date or time type and these break 10.3 SR 8. the checker
  reads the rule as typing the operator forms (a reading since the ninth
  review), but that reading lets more in and was named nowhere; the audit
  row paraphrased the rule wrongly and said "read as written". it is an H4
  permission now (the defect: no date or time expression could exist), the
  row's status `permission`
- unprinted: a grouping element naming only a return alias (`RETURN 1 AS k
  GROUP BY k`) resolved to the alias; 16.15 SR 2 b ii 2 gives the element the
  RETURN's incoming fields. refused now (strict); every printed GROUP BY names
  an incoming column. tests that grouped on an alias now project first and
  group after NEXT
- 16.5 SR 11 read literally (no "another") forbids every insert edge; the
  reading "another" (NOTE 231) lets more in and 55 printed sentences rest on
  it, so it is an H4 permission too

checked and found to hold: the withheld-family detector (a parenthesized
parameter is refused by 22.19 SR 2 unknown instead), the whole 20.8 Table 4
matrix (361 pairs; L to P refused, the strict side), 20.9 SR 3, 16.4 SR 6, 12,
14 with KEEP, 13.3 SR 3-5, 16.5 SR 6, 21.2 numeric literal limits in every
radix, TRIM and string function operands, 14.11 SR 10.

runs after the fixes: every count unchanged (1 variable 3,227 and 327 withheld;
whole grammar 3,055 and 523; turbolay 3,400 and 186; 3 variables 3,408 and 198;
neo4j 41,103 and 1,580); 0 generator bugs apart from neo4j's 34.

## 2026-10-28: the thirty-second review

a sweep of the direction of every reading (the 75 `reading` rows, n/a rows
with reading notes, every "(reading)" in the checkers, the types.rs header
list). no printed counterexample. one unprinted gate hole, a lenient reading
named nowhere, so this round is not clean. closed:
- a datetime value expression whose primary is dynamic or unknown, moved by a
  duration, was typed dynamic or unknown: `VALUE v BOOL = CAST ( NULL AS ANY )
  + DURATION ( 'P1Y2M' ) FINISH` passed (28 of 84). 20.26 SR 1 types it a
  local datetime (a zoned one only for a zoned primary), and no rule of 20.26
  asks anything of its operands that the cure could meet, so 10.3 SR 8 fails
  on a static type. the datetime node is now typed by SR 1 before the dynamic
  and unknown arms. no printed temporal sentence has a dynamic instant

stale text corrected, none an argument step: FLOAT128's precision is 112 (18.9
SR 43 d), not 113, and the precision bound checked on the tree is now 112;
the scale of 8 is one past FLOAT32's 7, an H2 assumption, now said so; the
types.rs header line calling 21.2 SR 73 no violation (verify checks it); the
18.9 SR 85 note ("a union of several as nullable").

readings marked strict: about 90 rows across 4.17-22.19, every verify.rs and
scope.rs "(reading)", the types.rs header items. permission-named: the H4
list. lenient-unnamed: only the finding above.

the first fix typed every datetime node by SR 1, which dropped the 20.28 unit
check on two durations and typed `x + 1` (integers) a datetime on that tree;
it is limited to a dynamic, unknown or null operand, where the old arms gave up.
runs after the fix: every count unchanged (1 variable 3,227 and 327 withheld;
whole grammar 3,055 and 523; turbolay 3,400 and 186; 3 variables 3,408 and 198;
neo4j 41,103 and 1,580); 0 generator bugs apart from neo4j's 34.

## 2026-10-28: the thirty-third review

literal typing of printed sentences by hand, and the trusted base. no printed
counterexample. one unprinted gate hole, a lenient reading of 20.26 SR 1 named
nowhere, so this round is not clean. closed:
- `CURRENT_TIMESTAMP + DURATION ( 'PT1H' )` was typed zoned. 20.26 SR 1 makes
  a datetime value expression zoned only when the datetime primary it simply
  contains is zoned; `DVE + duration term` and `DVE - duration term` simply
  contain none (5.3.2.1), so read literally they are local, and `DURATION_BETWEEN
  ( CURRENT_TIMESTAMP + .. , CURRENT_TIMESTAMP )` breaks 20.28 SR 3 b. the
  operator forms are now typed literally (no permission added: every printed
  move is of a local datetime, where both readings agree). the audit row's
  paraphrase had dropped "simply contains"; corrected

checked and found to hold: the trusted base (printed text is the checked
tree's rendering, compared on the tree, "21.3 SR 13, 14"; check-grammar's
obligations; no comment opener outside quotes; separators between tokens;
byte string separators; the Cor 1 grammar diff, five items; synthetic node
names; leaf rules, other-script digits), and the hand typing of the printed
DURATION_BETWEEN, datetime and duration arithmetic, COALESCE and NULLIF, simple
CASE, GROUP BY items, LET, VALUE, FOR, session commands and graph type bodies.

weak points noted, not findings: 20.28 SR 2 names a duration term 2 that the
production lacks (the factor's type is used, as intended); IA019's row argues
from the generator; the plain (non-JSONL) output splits a byte string's
newline across lines (presentation only).
also: IA019 is checked on the tree now, every bidirectional control character refused in a character representation.

runs after the fixes: every count unchanged (1 variable 3,227 and 327 withheld;
whole grammar 3,055 and 523; turbolay 3,400 and 186; 3 variables 3,408 and 198;
neo4j 41,103 and 1,580); 0 generator bugs apart from neo4j's 34.

## 2026-10-28: the thirty-fourth review

literal declared types, value family by value family. no printed
counterexample. two unprinted gate holes, so this round is not clean. both
closed:
- a datetime operator form was typed by its operands' classes: on the
  <datetime value expression> tree of `1 + 1` (or `( DURATION .. ) +
  DURATION ..`) it was a number (a duration), but 20.26 SR 1 makes it a local
  datetime, so `VALUE x INT = 1 + 1`, `ABS ( ( 1 + 1 ) )` and `CAST ( 1 + 1 AS
  INT )` passed on that tree. every operator form on the node is typed by SR 1
  now. verdicts that depend on the tree because of it (`x + 1` then `y * 2`,
  two durations of different groups) are probed per parse; the type tests
  moved accordingly
- a declared list type's maximum cardinality was not followed at assignment:
  `VALUE x LIST < INT > [ 1 ] = [ 1 , 2 ]` passed (54 of 13,182). a list type
  with a written maximum cardinality is refused at a declared-type site, as a
  length-bounded string was, and in a binding table's declared columns too

families compared and held: numeric (20.21, 20.22), strings (20.23-20.25),
lists and paths (types), records (20.18, 20.19), durations (20.28 SR 1-4,
DURATION_BETWEEN), CASE and CAST, aggregates, value queries and LET,
predicates; store assignment (13.3, 22.10).

runs after the fixes: every count unchanged (1 variable 3,227 and 327 withheld;
whole grammar 3,055 and 523; turbolay 3,400 and 186; 3 variables 3,408 and 198;
neo4j 41,103 and 1,580); 0 generator bugs apart from neo4j's 34.

## 2026-10-28: the thirty-fifth review

assignability end to end, and parse dependence. no printed counterexample. one
unprinted gate hole, so this round is not clean. closed:
- closed node and edge types were compared by `Shape` (labels, property names,
  coarse property kinds), which drops an edge type's endpoints and direction
  and the exact property value types (INT8 against INT64, NOT NULL): `VALUE x
  ( :a ) -[ { } ]-> ( ) = CAST ( NULL AS ( :b ) -[ { } ]-> ( ) )` passed (42
  of 546), at 7.1 SR 6 too. a declared type containing a closed node or edge
  type is refused now, as length- and cardinality-bounded types are. printed
  sets use closed element types only as `CAST ( NULL AS .. )` under IS NULL or
  IS TYPED. the same coarse equality in `combine` only decides label and
  property checks, which such types share, and its result reaches no declared
  site now

checked and found to hold: assignable against 4.15.3, 4.15.4, 4.16.5, 4.16.6,
4.16.8, 4.17.3 (record field sets exact, list element nullability by
nested_not_null, bounds by the round 34 refusal at any depth, duration groups,
unions with 18.9 SR 85, 86, 88); casts between reference types (Table 4);
parse dependence: the gate exports, renders, verifies, scope- and type-checks
one tree and prints its rendering, and no checker re-parses.

runs after the fix: every count unchanged (1 variable 3,227 and 327 withheld;
whole grammar 3,055 and 523; turbolay 3,400 and 186; 3 variables 3,408 and 198;
neo4j 41,103 and 1,580); 0 generator bugs apart from neo4j's 34.

## 2026-10-28: the thirty-sixth review

comparison and ordering, graph type bodies, the claim's statement and H. no
printed counterexample. one unprinted gate hole and one false sentence in H1,
both on confusable names (IW014), so this round is not clean. both closed:
- H2 names UTS #39's ASCII confusables, but the checker's skeleton lacked
  three of its ASCII-to-ASCII pairs (`|` and `l`, `` ` `` and `'`, `"` and
  `''`): `MATCH ( :"|" | l ) FINISH` passed. the skeleton has them now, and H2
  lists the relation exactly (the checker's extra pairs, `vv`/`w`, `cl`/`d`,
  case, only report more)
- six environment rows (17.1 SR 2 b iv, 17.2-17.4 SR 2 d i 2, 17.5 SR 3 b
  iii, 22.9 SR 4 b) need no sibling of a resolved object to be named
  confusably with it, which H1 did not say though printed sentences (`USE
  """" FINISH`) rest on it. H1 says it now. the 6 SR 4 audit note's premise
  (names are one to three lowercase letters) was false too; corrected

checked and found to hold: 19.3 and 22.13-22.15 have no syntax rule with a
shall (comparability is conformance only, outside the theorem, as the claim
says), and every syntax rule that needs comparable types is checked (14.2 SR
10 a v and a vii, 20.28 SR 3 b, d, 20.24 SR 3, 4); duration units; graph
type bodies against 18.1-18.5 and all 43 printed bodies by hand; closed graph
types (16.8 SR 4, 20.11 SR 2, 3); the claim's run wiring.

runs after the fixes: every count unchanged (1 variable 3,227 and 327 withheld;
whole grammar 3,055 and 523; turbolay 3,400 and 186; 3 variables 3,408 and 198;
neo4j 41,103 and 1,580); 0 generator bugs apart from neo4j's 34.
