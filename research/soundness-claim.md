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
   anything when one tree fails; `context` cover withholds a flagged tree
   (`withheld` on stderr) and refuses `--sentences` with no syntax-rule
   checker. so S's tree t has no violation the checker reports
2. **the checker reports every rule.** for each constraint and type row of the
   audit (`research/audit/audit.jsonl`), the `check` column names where the
   checker reports it. a rule the checker reports, and t does not violate, holds
   on t
3. **what the checker does not report** is one of:
   - `grammar`: no derivation can break it (the row says why)
   - `hypothesis`: an environment rule, H1
   - `reading` with a narrower generator rule and the checker checking the
     narrower form
   and no constraint or type row is `open`. the audit's merge
   (`tools/inventory/audit.py`) fails on a `generated` or `reading` row with no
   `check`, so the table cannot claim a rule nobody checks
4. therefore S satisfies every rule, under the readings, given H. ∎

the generator's own rules (automata, scope, types, spelling-time values) are
not part of the argument: they make the gate pass often enough that coverage
survives. soundness rests on the gate and the checker alone

## the readings

stricter or narrower than the text, each keeping out more than iso does, so
a sentence valid under the reading is valid under the text: the list is the
audit's `reading` rows, with their notes
