# the soundness claim

> for agents: the argument, terse. people start at the [readme](../README.md)

## the statement

**theorem.** let S be a sentence `gql-proof context --rule types --rules all
--phase cover --sentences` prints, with the default `--start GQL-program` (another
start prints fragments, not programs, outside the theorem). then S, read by the derivation tree it was
printed from, satisfies every syntax rule of iso/iec 39075:2024 with cor 1 whose
kind is constraint or type, under the readings listed below, given hypothesis H.

`purdom` and `context` without `--rule types` check the syntax and scope rules
only: their sentences satisfy every row the syntax and scope checkers report
(the rows whose check names `src/verify.rs`, `src/verify/scope.rs` or
`src/verify/graph_type.rs`), not the type rows. both commands say so on
stderr. (found by an independent review on 2026-10-24: the theorem had named
purdom while purdom never ran the types checker)

no part of the argument depends on which witness extraction picked: it is a
property of every printed sentence, by the gate in step 1

## the hypothesis H (what we do not control)

- **H1, the environment.** every catalog object, session parameter, dynamic
  parameter, graph, graph type, binding table and procedure that S references
  exists in the engine's environment, with the type S uses it at; every
  schema, graph and graph type a CREATE in S makes without IF NOT EXISTS or OR
  REPLACE does not exist. the two parts never meet on one name: no made name
  is spelled like another name in S (the `same text` rows of 12.2 SR 5, 12.4
  SR 6, 12.6 SR 5, reported by the checker). a parent reference that cannot
  identify a schema in any environment (one holding an object name, 4.2.5.3) is
  not left to H1: the `object name` rows of 12.5 SR 2 and 12.7 SR 2 are
  checked; nor is a root used both as a schema and as a directory (17.1 SR 2 a
  i against SR 5, checked). H1 is one environment, and every syntax rule is
  judged against it before execution (`DROP GRAPH a NEXT DROP GRAPH a` needs
  graph a at both, as the text applies syntax rules to the whole program
  first). a parameter has the type the request gives it; one used at two
  incompatible types (`$b * 2` used as a graph) holds only if that type is
  dynamic and H2' cures it. the `environment` rows of the audit hold under H1
  and only under it
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
  set), and the dynamic element of a path constructor (`PATH [ x . a ]`). a
  combination (22.19 SR 2: CASE, COALESCE, NULLIF, a list constructor) is not
  cured: the checker refuses a dynamic input there.
  the generator could avoid every dynamic operand at a large cost in coverage;
  this is the hypothesis that it need not. without the cure these sentences
  are invalid. the cure can turn an operand into a run-time exception when no
  static type survives (4.14.4: `SESSION SET GRAPH CAST ( NULL AS ANY
  PROPERTY VALUE )`, no property value type being a graph under H2): such a
  sentence is valid in the weak sense that it raises no syntax error
- **H2''', the claim's features.** a sentence that uses a feature-dependent
  form holds for an engine claiming that feature (the conformance rules of the
  claim keep the others out). one syntax rule turns on a feature: 18.2 SR 9 a
  (an omitted key label set needs GG22); the sets that print graph type bodies
  claim every feature, and a claim with GG23 but not GG22 is outside the theorem
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
  one known exception in the checker: in a graph or binding table expression it
  types `x . a` as a catalog reference even where the tree holds a property
  reference; both are dynamic or opaque there and pass the same rules, so no
  verdict changes

## the trusted base (what the argument assumes correct, and how it is tested)

- the iso bnf as read by `bnf.rs`, with cor 1's edits applied by
  `tools/corrigendum.py`
- the checker: `src/verify.rs`, `src/verify/scope.rs`, `src/verify/types.rs`,
  written from the text, never from the generator. tested by probes (each rule
  red on a violating tree, green on a valid one), and against the generator's
  automata over random unrefined trees (`automaton_and_verifier_agree`)

## also in the trusted base

- the audit's `grammar` rows (11) each name a mechanical check (the checker's
  ISO BNF match, its rendering check, or a test); the argument that the check
  implies the rule is the auditors'
- the rewrite audit (`research/audit/rewrite-*.jsonl`, checked by
  `tools/inventory/rewrites.py --check`): every rule that rewrites text has a
  row saying whether the rewrite can break a later rule and where the checker
  judges it
- `tools/inventory/shall_coverage.py`'s extraction of the rules from the text
  (it finds the 1,025 rules the inventory has, a check on itself)

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
   syntax rule of the text (1,025; 275 say `shall`) and fails unless each rule
   with a `shall` has a row in `research/audit/audit.jsonl` that is not a
   definition, and so does each cor 1 syntax rule with a `shall` (read from
   `grammar/corrigendum.json`). four are exempt, each with its reason in the
   tool (two deleted by cor 1, one that defines how keywords are read, one
   applied only hypothetically by its importers). coverage is per rule, not per
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
     type, which is the request's) or H2' (the 4.14.4 cure)
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

## the readings

stricter or narrower than the text, each keeping out more than iso does, so a
sentence valid under the reading is valid under the text: the audit's
`reading` rows, with their notes (`python3 -I tools/inventory/audit.py --md`).
a reading that lets more in is not a reading but part of H: the 4.14.4 cure is
H2', the rest are the permissions of H4. the direction of each reading is the
auditors' judgement, checked row by row in the review rounds (the fourth
review moved nine rows from `reading` to `permission`)

## hypothesis H2, the implementation choices named

- IL001-IL003, IL011, IL013, IL015: the implementation's minimum label, key
  label and property counts at most what S uses, and the maxima at least: S
  declares node and edge types with no label at all (`( )`), so the minima are
  0 (18.2 SR 10, 12; 18.3 SR 11, 13), and uses one or two labels and properties,
  lengths and precisions under 256
- exact types of 18 decimal digits, an approximate literal type with the range
  of a 32 bit float (21.2 SR 18, 20; the checker reports past that)
- IW014: names are confusable only as UTS #39's ASCII confusables are (`rn`
  and `m`, `vv` and `w`, `cl` and `d`, `1`, `I` and `l`, `0` and `o`; the
  checker reports two such names in one sentence)
- ID061: SESSION_USER's character string type is assignable to every
  character string type S declares for it; S declares no length-bounded one
  (10.3 SR 8 reading, at any depth of the declared type)
- IA014: a NULL whose context fixes no type does not raise a syntax error (21.2
  SR 67 b); S holds many (`NULL + NULL`)
- ID022, the default collation: two names compare equal only when their
  representative forms are equal strings (18.1 SR 10, 18.5 SR 1 and the graph
  type rules)
- nothing about IW022 (nullability inference): a NOT NULL site takes no
  computed value (4.17.4.2, the checker's reading), so none is needed
- IL020: the directory nesting depth is at least what S uses (S holds
  absolute paths of a few directories and `..` steps)
- IA023: the line feed ends a line (comments, byte string separators)
- IV023: truncating whitespace is the space
- the supported property value types include the predefined scalar types S
  casts a property to (20.8 SR 10); no reference value type is assumed
  supported
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
- **a supported string supertype exists.** CASE, COALESCE and list
  constructors over character or byte strings need a supported string type
  that is a supertype of every input; S's strings are short and every
  implementation is assumed to have one. rows: 22.19 SR 4 b ii, 22.19 SR 4 c ii
