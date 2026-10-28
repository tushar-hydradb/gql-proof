# the soundness claim

> for agents: the argument, terse. people start at the [readme](../README.md)

## the statement

**theorem.** let S be a sentence `gql-proof context --rule types --rules all
--phase cover --sentences` prints on stdout (stderr also echoes some withheld
sentences, which are not printed in this sense), with the default `--start GQL-program` (another
start prints fragments, not programs, outside the theorem), under any `--claim`
that claims GV71 (every claim the runs use does: all, turbolay, neo4j; without
it a NULL whose context fixes no type has ID085's static type, which no
hypothesis names; the thirty-eighth review) and any `--match-mode-default` (the gate checks with both; H2'' and H2''' ask
the engine to match them). then S, read by the derivation tree it was
printed from, satisfies every syntax rule of iso/iec 39075:2024 with cor 1 whose
kind is constraint or type, under the readings listed below, given hypothesis H.

`purdom` and `context` without `--rule types` check the syntax and scope rules
only, and only with `--rules all` (`--rules syntax` adds no scope check,
`--rules none` no syntax rule) and the default grammar (`--grammar` swaps
the grammar the checker matches): their sentences satisfy every row the
checkers they ran report, not the type rows. both commands say on stderr
what they checked (purdom by its `--rules` and `--grammar`, since the
seventeenth review). (found by an independent review on 2026-10-24: the theorem had named
purdom while purdom never ran the types checker)

valid here means static validity: a sentence can still raise an exception
when it runs. `INSERT ( { a : CURRENT_DATE , a : CURRENT_DATE } )` is printed.
It names one property twice, so no node with those properties can be made.
No syntax rule refuses this (16.5 SR 9 covers only bound patterns, and SR 10 a iii
holds vacuously). It fails only under the general rules, which are outside the
theorem (the seventeenth review).

no part of the argument depends on which witness extraction picked: it is a
property of every printed sentence, by the gate in step 1

## the hypothesis H (what we do not control)

- **H1, the environment.** every catalog object, session parameter, dynamic
  parameter, graph, graph type, binding table and procedure that S references
  exists in the engine's environment, with the type S uses it at; every
  schema, graph and graph type a CREATE in S makes without IF NOT EXISTS or OR
  REPLACE does not exist. the two parts never meet on one name: no made name
  is spelled like another name in S that can identify a catalog object (a
  graph, graph type, table, procedure, schema or directory name, or a bare
  catalog name; a local alias in a graph type body is no such name) (the `same text` rows of 12.2 SR 5, 12.4
  SR 6, 12.6 SR 5, reported by the checker). a parent reference that cannot
  identify a schema in any environment (one holding an object name, 4.2.5.3) is
  not left to H1: no parent reference holds an object name (17.6 SR 5; a
  reading, the stricter side: the text lets a primary catalog object hold
  objects, 4.2.5.3, but S never relies on one doing so), no root is used both as a
  schema and as a directory, absolute or `..` (17.1 SR 2 a i against SR 5,
  6), no name is used for two kinds of object, bare names in graph and table
  expressions and directory names included (17.2 SR 2, a schema holds one
  object per name, a directory one schema or directory per name), and no
  LIKE source may have an open type (12.6 SR 7 b iv), and no named procedure is
  called as two kinds (12.8, 13.6, 14.5 SR 3: a procedure has one kind), all
  checked. H1 is one environment, and every syntax rule is
  judged against it before execution (`DROP GRAPH a NEXT DROP GRAPH a` needs
  graph a at both, as the text applies syntax rules to the whole program
  first). no object of a schema or directory S resolves a name through is
  named confusably (IW014, under H2's relation) with a name S uses there, so a
  reference resolves (17.1 SR 2 b iv, 17.2-17.4 SR 2 d i 2, 17.5 SR 3 b iii,
  22.9 SR 4 b; the thirty-sixth review: H1 said only which objects exist). a parameter has the type the request gives it; one used at two
  incompatible types (`$b * 2` used as a graph) holds only if that type is
  dynamic and H2' cures it. H2' cures every use but a combination's input. so
  the only unknown input a combination may take is a bare parameter written
  once in S. a variable or field of unknown type is refused there, and so is an
  operation over one, a column of a set operation, and an unknown at any
  depth of an input (a list element, a record field, a table column), since
  22.19 SR 4 combines those again. this is checked, as
  "22.19 SR 2 unknown", gate-only. the eighteenth review found `USE $b ..
  COALESCE ( $b , 1 )`, the nineteenth the alias `USE $b LET y = $b ..
  COALESCE ( y , 1 )` and a named procedure's column used both ways, the
  twentieth `COALESCE ( RECORD { a : $b } , RECORD { a : 'a' } ) .. $b + 1`. a
  catalog table read as a value (its columns unknown) counts as unknown here
  too, since no table type serves two column sets. a combination with a bare
  parameter takes the type its known inputs combine to, which they must (the
  twenty-first review: `NOT COALESCE ( $b , 1 )` passed), and one with no
  known material input (`COALESCE ( $b , NULL )`, `COALESCE ( $b , $c )`, a
  CASE without ELSE) is refused, as its type is one S cannot see (the
  twenty-second review). H1 is never vacuous for S, and this is checked, not
  argued: the type checker types S a second time in one environment E, where
  a parameter written once as a combination's input has the type the other
  inputs combine to (at least one is known, by the above), and every other
  unknown the environment gives (a parameter, a session parameter S does not
  set, a named procedure's column, a field of a catalog table's row) is
  dynamic, cured by H2' at every use but a combination's. a rule broken in E
  only is reported as "H1 environment", gate-only. so every printed S keeps
  every rule in E, and E serves it (four rounds running had found an S the
  prose argument missed). a named procedure called without YIELD returns no
  column named like a field of the call's incoming record or table (15.1 SR 9,
  the two amended under cor 1, through the
  procedure's signature, which only the catalog gives). the session has a
  current working graph, a current working schema and a home schema wherever
  S needs one (16.3 SR 23, 13.2 SR 5, 16.8 SR 2, 17.1 SR 4, 6, 17.6 SR 2 b i),
  where S does not fix it: a program whose AT names a schema absolutely takes
  no `..` step ("17.1 SR 6 at", checked, the twenty-sixth review);
  a schema S drops is empty and is not the session's working schema nor its
  home schema (`AT HOME_SCHEMA DROP SCHEMA / a`; spec audit batch 1), and a
  graph type S drops is no graph's type (12.3 SR 7, 12.7 SR 6), S itself never
  working in or naming into a schema it drops (checked). the `environment` rows of the audit hold under H1
  and only under it. the type checker's unknown type comes only from H1: a
  dynamic parameter, a session parameter S does not set, a catalog object, or
  a named procedure's columns. it also arises after a violation is already
  reported, or at sites the grammar never reaches. every source is classified in
  `research/audit/unknowns-2026-10-26.md`. the sources S itself fixes are typed:
  ELEMENT_ID's value (H2, ID076), a table variable's columns, a dynamic list's
  dynamic elements. two sources that have no type are refused: a FOR over NULL,
  and `NULL || NULL` (`14.8 SR 10 null`, `20.15 SR 2 null`)
- **H2, implementation-defined choices.** the implementation-defined rules
  S's validity depends on take the choice that does not raise a syntax error:
  listed per row (`implementation` kind) in the audit. S avoids every
  implementation-defined syntax it can avoid (prose leaves with no portable
  form are never generated, `tokens::EXCLUDED`), so the list is the
  implementation limits (IL0xx: label counts, lengths, precisions) the engine
  sets at least as large as S needs
- **H2', the 4.14.4 cure.** where an operand's type is dynamic (a property,
  `CAST ( .. AS ANY )`, a parameter) or open and a static type is required,
  the implementation executes the cured variant 4.14.4 permits ("may"). the
  checker lets such an operand meet the requirement on that assumption; rows
  resting on it: 20.1 SR 2-6, 11.1 SR 3, 20.20 SR 3, 20.21 SR 3, 20.23 SR 2, 4,
  16.5 SR 6 c and 13.3 SR 3 a iv, b iii 2 (a dynamic property value inserted or
  set), 10.3 SR 8, 7.1 SR 6, 10.1 SR 8 and 10.2 SR 8 (a dynamic initializer
  assigned to a declared type), 20.9 SR 8, 20.13 SR 2, 20.15 SR 1, 20.16 SR 1,
  20.24 SR 3, 4 and 20.28 SR 1, 3 (a dynamic operand of an aggregate, a path,
  list, string or duration operation), and the dynamic element of a path constructor
  (`PATH [ x . a ]`). a combination (22.19 SR 2: CASE, COALESCE, NULLIF, a list
  constructor, a list concatenation) is not cured: the checker refuses an
  input it types dynamic (a sign, ABS, MOD, LEFT, RIGHT, TRIM, UPPER, LOWER,
  NORMALIZE, numeric arithmetic over a dynamic operand, FLOOR, CEIL,
  ELEMENTS, an empty list and an unwritten list element type keep a dynamic
  type dynamic; a datetime or duration operation whose one fitting row fixes
  its result, an instant plus a duration or a duration times a number, has
  that type, the type every arm of its cure has); an input of unknown type
  passes only as H1 says, a parameter written once (the twenty-fourth
  review). the cured variant is how the implementation executes S, not a
  second program judged again: the CASE 4.14.4 builds is not itself held to
  the syntax rules (without GV65 it would be a static combination its arms
  may fail), and this is part of H2'. the
  cure never makes an operator's value a graph or a table: an operator, a
  function or a literal at a graph or table expression is refused on its tree
  the checker lets a dynamic operand meet every type
  requirement it checks (a dynamic type has no class to fail), so every row
  whose requirement a dynamic operand meets rests on this hypothesis, the
  ones named above and every other. the hypothesis is stated by the operand's
  type, not by a list of rows, so it needs no list to be closed: a row rests
  on it exactly when a dynamic operand meets its requirement (the twelfth
  review found 19.8 SR 3, 19.10 SR 2, 3, 20.11 SR 2 b and 14.2 SR 10 among
  them).
  the generator could avoid every dynamic operand at a large cost in coverage;
  this is the hypothesis that it need not. without the cure these sentences
  are invalid. the cure can turn an operand into a run-time exception when no
  static type survives (4.14.4: `SESSION SET GRAPH CAST ( NULL AS ANY
  PROPERTY VALUE )`, no property value type being a graph under H2): such a
  sentence is valid in the weak sense that it raises no syntax error
- **H2''', the claim's features.** a sentence that uses a feature-dependent
  form holds for an engine claiming that feature. the conformance rules are
  outside the theorem: the gate enforces those `features --claim` lists as
  enforced, not the rest (for neo4j, GE04's `USE $b` is printed; GP02 is read
  by 5.3.2.1 containment, so a scope clause nested in a CALL { } meets it).
  syntax rules that turn on a feature: 18.2 SR 9 a
  (an omitted key label set needs GG22) and 18.3 SR 10 a, likewise for edge
  types: under a claim without GG22 the gate withholds every node or edge type
  specification without a key label set (`Verifier::with_key_label_sets_required`,
  gate-only; the seventeenth review found 44 such bodies printed without it). 22.18 SR 2 (GV65), 22.18 SR 9 c (GV66, GV67), 20.17 SR 3 b (GV72)
  and every rule asking for comparable value types (4.4.2: GA04, GA09; 20.24
  SR 3, 4, 14.2 SR 10) turn on features too; the checker reads each as without the feature
  (static combination), the stricter side, and 20.17 SR 3 b stricter than
  either branch (`[ ]`'s element meets no type requirement, neither the empty
  type nor one implementation's choice being known to meet it), so they need
  nothing of the claim. 22.17 SR 2 (GG26) is read stricter than either branch
  too: only identical property value types combine (the thirty-eighth review)
- **H2'', ID086.** the sets are printed for an implementation whose default
  match mode is the one passed as `--match-mode-default` (the turbolay and
  whole grammar sets: DIFFERENT EDGES); 16.4 SR 14 d and 16.4 SR 12 read it
- **H3, the reading of an ambiguous grammar.** the bnf is ambiguous; S is
  valid when the tree it was generated from satisfies the rules (the standard
  states rules over a derivation, not over text). the engine is free to pick
  another tree; if that tree breaks a rule, that is the engine's
  disambiguation, not S's validity. a case the review found:
  `CAST ( NULL AS GRAPH NOT NULL | NOTHING LIST )` is valid as
  `LIST < GRAPH NOT NULL | NOTHING >` and breaks 18.9 SR 88 as the union of
  `GRAPH NOT NULL` and `NOTHING LIST`; the text has no rule choosing. a
  stronger claim (every tree of S valid) needs every tree checked, not built.
  the checkers judge the tree as printed, `GRAPH x . a` and `VARIABLE "x"`
  included (the sixth review found them skipped)

## the trusted base (what the argument assumes correct, and how it is tested)

- the iso bnf as read by `bnf.rs`, with cor 1's edits applied by
  `tools/corrigendum.py`
- the checker: `src/verify.rs`, `src/verify/scope.rs`, `src/verify/types.rs`,
  written from the text, never from the generator. tested by probes (each rule
  red on a violating tree, green on a valid one), and against the generator's
  automata over random unrefined trees (`automaton_and_verifier_agree`)

## also in the trusted base

- the audit's `grammar` rows (10) each name a mechanical check (the checker's
  ISO BNF match, its rendering check, or a test); the argument that the check
  implies the rule is the auditors'
- the rewrite audit (`research/audit/rewrite-*.jsonl`, checked by
  `tools/inventory/rewrites.py --check`): every rule that rewrites text has a
  row saying whether the rewrite can break a later rule and where the checker
  judges it
- `tools/inventory/shall_coverage.py`'s extraction of the rules from the text
  (it finds the 1,019 rules the inventory has, a check on itself)

## the argument

1. **the gate.** every printed tree passed the checker: purdom and `context`
   cover withhold every flagged tree (`withheld` on stderr). a flag on a rule
   the generator should keep (one not in `verify::GATE_ONLY`) is a generator
   bug: purdom stops, `context` withholds the tree too and counts it on stderr
   (`N of them on a rule the generator keeps`). either way nothing flagged is
   printed; the count measures the generator, not soundness. `context` refuses
   `--sentences` with no syntax-rule checker. so S's tree t
   has no violation the checker reports. this step needs nothing from the
   generator: whatever extraction picks, nothing flagged goes out
2. **the table is complete.** `tools/inventory/shall_coverage.py` reads every
   syntax rule of the text (1,019; 275 say `shall`) and fails unless each rule
   with a `shall` has a row in `research/audit/audit.jsonl` that is not a
   definition, and so does each cor 1 syntax rule with a `shall` (read from
   `grammar/corrigendum.json`). eight are exempt, each with its reason in the
   tool (two deleted by cor 1, one that defines how keywords are read, one
   applied only hypothetically by its importers, and four whose "not
   omitted" is a definition: 6 SR 5, 6, 8 and 18.1 SR 6). coverage is per rule, not per
   `shall` item: a rule with several items is covered by its rows together,
   which the review rounds read item by item
3. **the checker reports every row.** `tools/inventory/audit.py` fails unless
   every constraint and type row is closed (no `open`), and every row the claim
   relies on (`generated`, `reading`, `checked`) quotes the rule string the
   checker reports, that string is a literal in `src/verify*`, and a red probe
   in `tests/` expects it on a violating input (inside a `bad*`/`red*` call, as
   an expected violation, or asserted present; a bare entry of a rule list is
   no probe; three exempt where no text can break the rule). an open row or an
   unprobed string fails it. green probes exist for most rules but are not
   checked by the script. the probes run in `cargo test`
4. **what the checker does not report** is one of:
   - `grammar`: no derivation can break it (the row says why)
   - `hypothesis`: holds under H1 (an environment object, or a parameter's
     type, which is the request's), H2 (a named implementation choice, as
     IW014 for 6 SR 4) or H2' (the 4.14.4 cure)
   - `n/a`: a definition (no `shall`), or an implementation rule, H2
   - `permission`: a reading that lets in more than the text, so it holds
     under H4 and only there. the checker reports it under that reading;
     `audit.py` fails unless every permission row is named in H4
5. therefore S satisfies every constraint and type rule, under the readings,
   given H. ∎

the generator's own rules (automata in `refine.rs`, scope and types in
`context/`, spelling-time values and names in `tree.rs`) are not part of the
argument: they make the gate pass often enough that coverage survives, and the
withheld count measures how often it does not. soundness rests on the gate, the
checker and the table

## what each run shows

- `cargo test` passes: probes, the automaton and checker agreeing on random
  trees (`automaton_and_verifier_agree`), generated trees passing the checkers
- `python3 -I tools/inventory/shall_coverage.py` exits 0
- `python3 -I tools/inventory/audit.py` exits 0 (no open row, no unquoted or
  unprobed rule string)
- `python3 -I tools/inventory/rewrites.py --check` exits 0 (every rewrite rule
  has a closed row)
- a cover run's `withheld` line: the targets lost to the gate, which are lost
  coverage, never lost soundness
- what the variable count buys: the cover targets are productions in a
  context, each met at 1 or 2 variables, so a run at 3 adds a few sentences of
  three fields or definitions and no new interaction (the fourteenth review:
  7 new in the whole grammar, 9 in turbolay). joins across MATCHes, shadowing,
  OPTIONAL, CALL scope with element variables and group variables together are
  not printed, so the theorem says nothing about them; the checker's probes
  for them (`tests/scope_checker.rs`, `tests/probes_checker.rs`) are what
  stands behind a future set that prints them
- not a check: `gql-proof cover FILE` verifies sentences from elsewhere with
  the ISO grammar and the rendering only (no syntax rules, scope or types),
  and accepts a sentence when any tree passes; it says nothing about this
  theorem

## the readings

stricter or narrower than the text, each keeping out more than iso does, so a
sentence valid under the reading is valid under the text: the audit's
`reading` rows, with their notes (`python3 -I tools/inventory/audit.py --md`).
a reading that lets more in is not a reading but part of H: the 4.14.4 cure is
H2', the rest are the permissions of H4. the direction of each reading is the
auditors' judgement, checked row by row in the review rounds (the fourth
review moved nine rows from `reading` to `permission`). some families no set
prints are withheld whole instead of read, which keeps out more than any
reading: group variables and group list types ("16.7 SR 22 group": an element
variable declared under a quantifier, a written GROUP list type; the
twenty-ninth review found the checkers disagree on them), and five more the
thirtieth review mapped, where rounds 18-28 found holes ("withheld family"): a
parameter inside a combination, a session parameter set by one command and
read by another, a named procedure call with YIELD, a selective path pattern
or a path union or alternation that declares an element variable

## hypothesis H2, the implementation choices named

- IL001-IL003, IL011, IL013, IL015: the implementation's minimum label, key
  label and property counts at most what S uses, and the maxima at least: S
  declares node and edge types with no label at all (`( )`), so the minima are
  0 (18.2 SR 10, 12; 18.3 SR 11, 13). S names at most one distinct label in a
  label set (`a & a & a & a` is one label) and declares up to four property
  types in an element type (`{ a BOOLEAN , ab CHAR , abb CHAR , abbb BOOLEAN }`,
  the most the saved sets hold; the seventeenth review).
  lengths and precisions are spelled from the leaf digits: S writes string and
  byte lengths up to 888 (18.9 SR 25 guarantees 65,534), exact precisions
  up to 8, an approximate precision up to 88 bits (checked on the tree, and
  `tree.rs` lowers a raised one to it; FLOAT128 has 112, 18.9 SR 43 d), and
  an approximate exponent scale of at most 8, one past FLOAT32's 7, which H2
  assumes the implementation takes (`tree.rs` settles it;
  the sixth review found `FLOAT ( 8 , 88 )`). a list type's maximum
  cardinality is at most 888 (IL015, which no guarantee bounds; checked on the
  tree, "18.9 SR 73"), and so is a list constructor's element count and a
  record's field count (20.17 SR 3 c, 20.18 SR 4, 18.9 SR 79; checked on the
  tree, "20.17 SR 3 bound", "20.18 SR 4 bound"). a concatenation of
  fixed-length strings sums their lengths (20.23 SR 1 b, 3 b), at most the
  guaranteed 16,383 or 65,534: as string types carry no length in the checker,
  the longest fixed length written in the tree times one more than its
  concatenations is held to that ("20.23 SR 1 bound"; the thirty-ninth review
  found a length reaching `||` through a variable, and `STRING ( n , n )`). the implementation's
  maximum lengths, precisions, list cardinalities and record field counts are
  at least these (the thirty-seventh review found the constructor, field and
  concatenation limits resting on the generator)
- exact types of 18 decimal digits, an approximate literal type with the range
  of a 32 bit float (21.2 SR 18, 20; the checker reports past that)
- IW014: names are confusable only as UTS #39's ASCII-to-ASCII confusables
  are (`rn` and `m`, `1`, `I`, `|` and `l`, `0` and `O`, `` ` `` and `'`, `"`
  and `''`). the checker maps each character of a regular, extended (a
  parameter's) or delimited identifier, lowercased, by these and by `w` to
  `vv` and `d` to `cl`, in one pass; that map is a per-character function of
  UTS's skeleton, so two names UTS relates always share it, and the checker
  reports two names of one sentence that do (the thirty-sixth review found
  `|`, `` ` `` and `"` missing; the thirty-seventh an ordering that kept `c1`
  and `cl` apart, and parameter names never compared)
- ID061: SESSION_USER's character string type is a variable-length one,
  assignable to every character string type S declares for it; S declares no
  length-bounded one (10.3 SR 8 reading, at any depth of the declared type),
  and its concatenations (364 printed `SESSION_USER || SESSION_USER`) are then
  of variable length, which 20.23 SR 1 c truncates rather than refuses
- IE001: an external object reference (`COPY OF urn:example:graph`)
  identifies a graph or graph type of the kind the statement wants (17.8 SR
  4, 5); an external object is no catalog object, so H1 does not cover it
- ID004 (without GV72): an empty list's element type is the implementation's,
  one choice for every sentence, so nothing may rest on it: the checker gives
  `[ ]`'s element a type that meets no requirement, goes to no site but one of
  every type, casts to nothing and is refused in a combination, refuses every
  reference to a variable bound to it (20.1 SR 1: with GV72 it is the empty
  type; the fortieth review), and refuses a cast of `[ ]` (the ninth review found casts to lists of GRAPH NOT NULL and of
  ANY NOT NULL, each holding only for its own choice; the thirty-eighth
  `FOR x IN [ ] RETURN x + 1`, which the open dynamic union let pass)
- ID005: ELEMENTS' element type is the implementation's; the checker types it
  the open dynamic union, so 22.19 SR 2 refuses it in a combination
- ID076: ELEMENT_ID's type is whatever the implementation defines; the
  checker refuses it anywhere but directly as a RETURN or SELECT item or an
  IS NULL operand, where any type is taken, or in an equality of two of them
  (20.10 SR 3 gives its type an equality). the same holds for its value when a
  column, a VALUE subquery or a row field carries it on: the checker gives it its
  own type and checks where that type is taken (the unknowns audit of
  2026-10-26: `RETURN ELEMENT_ID ( x ) AS e NEXT RETURN e || 'x'` passed)
- IA014: a NULL whose context fixes no type does not raise a syntax error (21.2
  SR 67 b); S holds many (`NULL + NULL`)
- ID022, the default collation: two names compare equal only when their
  representative forms are equal strings; the checker refuses a delimited
  identifier wherever it compares names by spelling (variables, fields,
  properties, parameters, aliases), and compares graph, type, label and
  catalog names by representative form (18.1 SR 10, 18.5 SR 1 and the graph
  type rules; created names, one kind per name, procedure kinds and YIELD,
  schema drops, the last three by the object's own name, its parent left out,
  the twenty-fifth review)
- IL010: an unsigned integer has at most 9 digits, checked on the tree
  ("21.2 SR 14", gate-only), also as the 21.2 SR 12 and 13 rewrites write a
  numeric literal out (`1E9M` is a 10 digit integer; the thirty-seventh review)
- IE003: the identifier profile is UAX31's default (XID_Start, XID_Continue),
  the one the checker's leaf rules use; IA020: no private use character is in
  an identifier (21.3 SR 5 e), refused on the tree
- IW011, IW012: the declared type the implementation gives a graph pattern or
  insert variable is open (the node or edge reference type with no
  constraint); the checker types it so and lets a property or label of it pass
  (20.12 SR 13, 20.11 SR 3 a; the thirty-seventh review: this rested on no
  hypothesis)
- nothing about IW022 (nullability inference): a NOT NULL site takes no
  computed value (4.17.4.2, the checker's reading), so none is needed
- IL018: the maximum quantifier bound is at least 255
- the limits above are checked on the tree, not taken from the generator:
  a quantifier bound past 255, a character length past 16,383 or a byte
  length past 65,534 (the maxima 18.9 SR 17, 25 guarantee), an exact precision
  past 18, an approximate precision past 88 or a scale past 8 is withheld
  (`verify::h2_bounds`, gate-only; the generator settles values below them)
- IL020: the directory nesting depth is at least what S uses (S holds
  absolute paths of a few directories and `..` steps)
- IA023: the line feed ends a line (comments, byte string separators)
- IV001: the source repertoire holds the line feed; every other character of S
  is a GQL language character (ASCII letters, digits, special characters, other
  digits), which every repertoire holds, checked on the text ("4.7.1
  repertoire", gate-only; the forty-second review)
- IV023: truncating whitespace is the space
- the supported property value types include the predefined types S
  inserts, sets, assigns to a property value type or casts a property to
  (16.5 SR 6 c, 13.3 SR 3, 10.3 SR 8, 20.8 SR 10): the predefined scalars,
  DATE among them, and those a graph type declares for a property (18.6, 18.7
  SR 4); no reference value type is assumed supported
- `$$` substitution (22.1 SR 3): the substituted text decides validity (17.7
  SR 4), and no engine is told it, so no hypothesis carries it: the generator
  prints no `$$` (`refine::NoSubstitution`), the checker reports one

## hypothesis H4, the permissions

readings that let in more than the literal text, each a fix of what we take
to be a defect in it, or an assumption about the implementation the text
leaves open. S holds under H only where the engine reads these rules this way.
each line names its audit rows (status `permission`)

- **the null type meets a typed site.** a bare NULL, or a value of the null
  type, is taken to meet a required type wherever its context fixes a
  nullable one (21.2 SR 67 a reads every typed site as fixing one). literally
  the null type is no graph element, graph or binding table reference type.
  rows: 21.2 SR 67 a, 13.5 SR 5 (`DELETE NULL`), 20.1 SR 2, 20.1 SR 3 (`FOR x
  IN NULL`, `PATH [ NULL ]` and `SUM ( NULL )` rest on 21.2 SR 67 a too). IA014
  covers only 67 b, a NULL whose context fixes no type
- **a dynamic parameter's type is the request's.** `$b` as a graph or binding
  table is taken to have the type the request gives it (20.4 SR 2), which no
  checker sees. rows: 11.1 SR 3 a ii, 11.2 SR 4 b ii
- **a kind-less edge type pattern is free.** 18.3 SR 4 b's otherwise, read
  literally, demands an undirected shape of every edge type pattern written
  with no edge kind, `( ) -[ { } ]-> ( )` included; it is read as applying
  only when UNDIRECTED is written. row: 18.3 SR 4 b
- **the minimum node count counts touching node patterns.** 16.7 SR 15 c i
  takes 1 off when two successive element patterns "contained in" a path
  concatenation are node patterns; read literally, through parentheses and
  quantifiers, `( ) <- *` (after SR 14 adds `( () <-[ ]- () ) {0,}`) counts 0
  and breaks SR 16, and `( () <- () ) ? ( () <- () ) ?` counts below 0, a
  defect. it is read as two node patterns touching at the same level of the
  path term. rows: 16.7 SR 16, 16.7 SR 20
- **an inline procedure's kind is read through its specification.** 12.8,
  13.6 and 14.5 SR 2 ask the nested procedure specification to *immediately*
  contain a catalog-modifying, data-modifying or query specification; by
  5.3.2.1 it immediately contains only a <procedure specification>, so read
  literally no inline CALL is ever valid (and with it every OPTIONAL and LET,
  rewritten into one by 14.4 SR 4 and cor 1's 14.7 SR 12). read as one level
  further down. rows: 12.8 SR 2, 13.6 SR 2, 14.5 SR 2
- **a statement sequence contains what its elements contain.** 13.1 SR 5:
  "STMSEQ shall contain at least one <simple data-modifying statement>" is
  read with 5.3.2.1's containment, so a nested `{ INSERT ( ) }` standing alone
  holds; read as "has one as an element" it does not. row: 13.1 SR 5
- **an omitted fixed length is CHAR's and BINARY's.** 18.9 SR 11 makes a
  fixed length of 1 implicit whenever one is omitted; read literally that
  bounds STRING and VARCHAR too, and no declared string type would be known
  to take a longer value (10.3 SR 8). it is read as applying to the forms
  whose production holds a <fixed length>, CHAR and BINARY, which the checker
  then refuses as declared types. rows: 10.3 SR 8 b i 1, 7.1 SR 6 c iii 3 A I,
  7.1 SR 6 d ii 1 B (the same reading at a session parameter), 18.9 SR 28 (a byte
  string's min and max length, read without the implicit fixed length)
- **a supported string supertype exists.** CASE, COALESCE and list
  constructors over character or byte strings need a supported string type
  that is a supertype of every input; S's strings are short and every
  implementation is assumed to have one. rows: 22.19 SR 4 b ii, 22.19 SR 4 c ii
- **a bare datetime primary keeps its own type.** 20.26 SR 1 gives every
  <datetime value expression> a zoned or local datetime type; a bare
  CURRENT_DATE, CURRENT_TIME or date or time primary derives only through
  one, so read literally no expression ever has a date or time type and
  `VALUE x DATE = CURRENT_DATE` breaks 10.3 SR 8. it is read as typing the
  operator forms, a datetime moved by a duration, and a bare primary as its
  own type (the thirty-first review; five turbolay sentences rest on it).
  the operator forms follow SR 1 literally: one whose datetime is written
  first simply contains no datetime primary and is local, one whose duration
  is written first takes its primary's zone (the thirty-third review)
  rows: 20.26 SR 1
- **a second insert pattern is another one.** 16.5 SR 11 forbids an insert
  edge pattern's variable to be declared by an insert pattern, without
  saying "another"; after SR 2 every insert edge pattern declares one, so read
  literally no insert edge is ever valid. it is read as "another", as NOTE 231
  intends (the thirty-first review; 55 printed sentences rest on it). rows:
  16.5 SR 11
