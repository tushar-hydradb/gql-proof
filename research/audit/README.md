# the audit: every syntax rule against the text

> for agents: terse on purpose. people start at the [readme](../../README.md)

the soundness claim is per rule: every sentence the generator emits keeps every
syntax rule of iso gql (39075:2024 with cor 1). the inventory
(`../static-inventory-2026-10-22.jsonl`) classified 1,025 rules once, by agents
reading the 2024 text; on 2026-10-23 two families were found broken that it had
right as "open" but nobody had measured reaching. this audit redoes every rule
with a column per thing the claim needs: what the rule says (our words), what
the generator does about it, where the independent checker reports it, and
whether a generated set reaches it

## the rows

one row per `shall` / `shall not` sentence of a syntax rule. a rule with several
constraining sentences gets a row per sentence, numbered as the text numbers its
items (`"sr": 7, "item": "b"`; `"item": "a ii"`). a rule with none gets one row
with `"kind": "definition"`. output: `research/audit/<part>.jsonl`, one json
object per row, keys:

- `clause`: `"16.7"`
- `sr`: the rule number, an integer
- `item`: the sub-item path, `""` for the rule itself
- `kind`: `constraint` (the text's shape), `type` (declared types, assignability,
  nullability), `environment` (a reference that must resolve to a catalog
  object, schema, graph, graph type, procedure, parameter, session or
  transaction state nobody in the sentence declares; was `catalog`),
  `implementation` (implementation-defined or -dependent limits and choices),
  `definition` (names things, defines a derived notion, says what an
  equivalent form is; nothing to violate)
- `sentence`: the constraint in our words, never the standard's sentence
- `replacement`: `""`, or the rule that rewrites the text this rule is judged on
  (`"19.4 SR 2: EXISTS { GP } is EXISTS { MATCH GP RETURN TRUE AS x }"`), so
  that a rule stated over the rewritten text is checked on it. list every
  "is effectively replaced by" / "is equivalent to" / "implicit" rule whose
  rewrite can introduce or remove what this rule looks at
- `enforced`: where the generator keeps the rule: `file:function` (line numbers
  drift; the function or rule struct name is the anchor), or `grammar: <why the
  bnf cannot express a violation>`, or `claim: <feature>` when only a claim
  excludes it (say which production), or `""` for nothing
- `check`: where the independent checker reports it (`src/verify.rs`,
  `src/verify/scope.rs`, `src/verify/types.rs`, `file:function` and the rule
  string it reports), or `""`. this is the column that matters: a rule the
  checker does not report is not known to hold whatever the generator does
- `reachable`: `yes: <set>: <sentence>` with a sentence from a cached set in
  `sentences/` holding the construct the rule talks about (a grep is enough to
  say yes), `no: <reason>` only with a grammar or claim reason (a production
  that is never generated, a prose leaf that is excluded), or `unknown`
- `status`: `generated` (kept as written and reachable), `reading` (kept by a
  stricter or narrower reading, which the note states), `checked` (the checker
  reports it, the generator does not keep it), `grammar` (unexpressible),
  `open` (reachable or unknown, nothing keeps it), `hypothesis` (an
  `environment` rule: holds given the hypothesis that the engine's environment
  provides what the sentence names), `n/a` (definition or implementation)
- `cor1`: `""`, or what cor 1 changed in this rule (`grammar/corrigendum.json`,
  13 rules: 14.7, 14.10, 14.11, 14.12, 15.1, 16.8, 18.1, 18.2, 18.9, 20.7,
  22.17), classified on the amended text
- `note`: anything the next reader needs, in our words

## how to read the text

- `iso-text/39075-2024.txt` is the standard's text, page by page (`just
  iso-text`; gitignored, licensed). find a clause by its header line, e.g.
  `grep -n "^16.7 <path pattern expression>$"`, the last hit is the clause (the
  first is the table of contents); the `Syntax Rules` line after it starts the
  rules. page breaks, licence lines and running heads interrupt sentences
- the extraction loses indentation: a sub-item can sit under the wrong number.
  read the items in order and by their letters
- `shall` inside a `definition` row is a constraint; reclassify it
- "simply contains" is: contains without an intervening instance of the
  container's definition or of the contained one (4.x, the containment
  definitions, `grep -n "simply contains"`). "directly contains": without an
  intervening <procedure body>. "immediately contains": a child
- a rule that says "the Syntax Rules of subclause X apply" imports X's rows:
  note the import in `note`, the rows stay under X
- nothing the standard owns goes in the repo: rule numbers and our words only

## where the code keeps rules

- `src/refine.rs`: tree automata compiled into the grammar (`all_rules`); each
  `impl Rule` cites its rules
- `src/context/scope.rs`: binding, scoping, statement shape, result shape
  (flags in `gf`, per-variable flags in `vf`, the arms of `finish_def`)
- `src/context/types.rs`: types of value expressions under scope
- `src/leaf.rs`, `src/tokens.rs`: prose leaves and token boundaries; `EXCLUDED`
  lists leaves never generated, with the rule
- `src/tree.rs` `order_bounds`: values settled at spelling time
- `src/features.rs` `ClaimRules`: conformance rules of unclaimed features
- the checkers: `src/verify.rs` (`syntax_rules`, `leaf_rule`, `token_rule`),
  `src/verify/scope.rs`, `src/verify/types.rs`. grep the rule's number
  (`"16.7 SR 16"`) in `src/verify*` first: the string the checker reports is
  the evidence for `check`
- the cached sets: `sentences/` (see its README); the whole grammar set
  `typed-2vars-whole-grammar-51d059a.jsonl` reaches the most

## what the previous inventory got wrong, so you look for it

- 18.2 SR 2, 18.3 SR 2: classified open, never measured reachable; the typed
  sets held 12 violations under turbolay's parse gap bucket
- 20.9 SR 3: "contains a procedure body" read on the surface text misses what
  19.4 SR 2 and 3 add (an EXISTS over a graph pattern holds one after
  replacement). list such rewrites in `replacement`
- 14.12 SR 7: marked generated; only item a was kept, item b (no GROUP BY with
  `*`) was not. one row per item finds this
- cor 1's 13 amended rules were classified on the 2024 text
