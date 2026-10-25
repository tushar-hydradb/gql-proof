# the rewrite audit

> for agents: the brief for auditing every effective replacement. people start at the [readme](../../README.md)

96 syntax rules say a text "is effectively replaced by", "is equivalent to", or
that something "is implicit" (the list: `python3 -I tools/inventory/rewrites.py`).
the standard judges every later rule on the rewritten text, so a rewrite can
break a rule the checker reads on the surface text. two such breaks were found by
review (14.12 SR 27: a HAVING with no aggregating item filters on an undeclared
name; a SELECT is ambient after its rewrite, 9.2 SR 5)

one row per rewrite rule, in `research/audit/rewrite-<part>.jsonl`, keys (all
strings but `sr`, an integer):

- `clause`, `sr`
- `rewrite`: what it replaces with what, in our words (never the standard's
  sentences)
- `introduces`: what the rewritten text has that the surface text does not (a
  statement, a name, a NULL, a CAST, a CASE, a nested query, a match mode, a
  different statement kind or focus)
- `judged_by`: the constraint and type rules that read what it introduces
- `consequence`: `none` (the rewrite can break no rule: say why), or the rule it
  can break and the surface shape that triggers it
- `checker`: where the checker evaluates that consequence (file:function and
  the rule string it reports), or `""`
- `status`: `closed` (consequence none, or checked), `open` (a consequence the
  checker does not evaluate)
- `example`: for an open row, a sentence (from `sentences/typed-2vars-*-soundness.jsonl`
  if one holds it, else written by you) that breaks the rule after the rewrite
- `note`

how to work: read the rewrite in `iso-text/39075-2024.txt` (header line `^X.Y <`,
the last hit; `Syntax Rules` follows), the rules that read what it introduces,
and the checker code (`src/verify.rs` syntax_rules, `src/verify/scope.rs`,
`src/verify/types.rs`, `src/verify/graph_type.rs`). grep the checker for the
rewrite's rule number and for the construct. `research/audit/audit.jsonl` has
the existing rows (its `replacement` column names some pairings). read-only:
write only your part file, run no cargo
