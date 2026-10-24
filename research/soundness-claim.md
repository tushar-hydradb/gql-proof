# the soundness claim

> for agents: the argument, terse. people start at the [readme](../README.md)

## the statement

**theorem.** let S be a sentence `gql-proof` prints (`purdom`, or `context --phase
cover --sentences`). then S, read by the derivation tree it was printed from,
satisfies every syntax rule of iso/iec 39075:2024 with cor 1 whose kind is
constraint or type, under the readings listed below, given hypothesis H.

no part of the argument depends on which witness extraction picked: it is a
property of every printed sentence, by the gate in step 1

## the hypothesis H (what we do not control)

- **H1, the environment.** every catalog object, session parameter, dynamic
  parameter, graph, graph type, binding table and procedure that S names
  exists in the engine's environment, with the type S uses it at. the
  `environment` rows of the audit hold under H1 and only under it
- **H2, implementation-defined choices.** the implementation-defined rules
  S's validity depends on take the choice that does not raise a syntax error:
  listed per row (`implementation` kind) in the audit. S avoids every
  implementation-defined syntax it can avoid (prose leaves with no portable
  form are never generated, `tokens::EXCLUDED`), so the list is the
  implementation limits (IL0xx: label counts, lengths, precisions) the engine
  sets at least as large as S needs
- **H3, the reading of an ambiguous grammar.** the bnf is ambiguous; S is
  valid when the tree it was generated from satisfies the rules (the standard
  states rules over a derivation, not over text). the engine is free to pick
  another tree; if that tree breaks a rule, that is the engine's
  disambiguation, not S's validity

## the trusted base (what the argument assumes correct, and how it is tested)

- the iso bnf as read by `bnf.rs`, with cor 1's edits applied by
  `tools/corrigendum.py`
- the checker: `src/verify.rs`, `src/verify/scope.rs`, `src/verify/types.rs`,
  written from the text, never from the generator. tested by probes (each rule
  red on a violating tree, green on a valid one), and against the generator's
  automata over random unrefined trees (`automaton_and_verifier_agree`)

## the argument

1. **the gate.** every printed tree passed the checker: purdom refuses to print
   anything when one tree fails (`main.rs`, "Nothing is printed unless every
   tree passes"); `context` cover withholds a flagged tree (`withheld` on
   stderr) and refuses `--sentences` with no syntax-rule checker. so S's tree t
   has no violation the checker reports. this step needs nothing from the
   generator: whatever extraction picks, nothing flagged goes out
2. **the table is complete.** `tools/inventory/shall_coverage.py` reads every
   syntax rule of the text (1,025; 275 say `shall`) and fails unless each rule
   with a `shall` has a row in `research/audit/audit.jsonl` that is not a
   definition. four are exempt, each with its reason in the tool (two deleted
   by cor 1, one that defines how keywords are read, one applied only
   hypothetically by its importers)
3. **the checker reports every row.** `tools/inventory/audit.py` fails unless
   every constraint and type row is closed (no `open`), and every row the claim
   relies on (`generated`, `reading`, `checked`) quotes the rule string the
   checker reports, that string is a literal in `src/verify*`, and a probe in
   `tests/` exercises it (red on a violating sentence, green on a valid one; two
   exempt where no text can break the rule). the probes run in `cargo test`
4. **what the checker does not report** is one of:
   - `grammar`: no derivation can break it (the row says why)
   - `hypothesis`: an environment rule, H1
   - `n/a`: a definition (no `shall`), or an implementation rule, H2
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
- a cover run's `withheld` line: the targets lost to the gate, which are lost
  coverage, never lost soundness

## the readings

stricter or narrower than the text, each keeping out more than iso does, so a
sentence valid under the reading is valid under the text: the audit's
`reading` rows, with their notes (`python3 -I tools/inventory/audit.py --md`)

## hypothesis H2, the implementation choices named

- IL001-IL003, IL011, IL013, IL015: label, property, key label counts, lengths,
  precisions and list cardinalities at least what S uses (S uses one or two
  labels and properties, lengths and precisions under 256)
- exact types of 18 decimal digits, an approximate literal type with the range
  of a 32 bit float (21.2 SR 18, 20; the checker reports past that)
- IW014: names are confusable only as UTS #39's ASCII confusables are (`rn`
  and `m`, `vv` and `w`, `cl` and `d`, `1`, `I` and `l`, `0` and `o`; the
  checker reports two such names in one sentence)
- IA014: a NULL whose context fixes no type does not raise a syntax error (21.2
  SR 67 b); S holds many (`NULL + NULL`)
- IA023: the line feed ends a line (comments, byte string separators)
- IV023: truncating whitespace is the space
- the supported property value types include the predefined scalar types S
  casts a property to (20.8 SR 10); no reference value type is assumed
  supported
- `$$` substitution (22.1 SR 3): the substituted text is what the position
  needs (17.7 SR 4). the claim leaves `$$` out: the hypothesis cannot be met
  by an engine that is not told the text
