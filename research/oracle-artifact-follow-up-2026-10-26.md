# follow up: the oracle artifact as a thing turbolay runs on its own

> for agents: dated working notes, terse on purpose. people start at the [readme](../README.md)

not started. written 2026-10-26 on `tushar/oracle` (8c1e591) for whoever picks
it up after the soundness track. the oracle itself, what it computes and why,
is `oracle-witness-2026-10-23.md`; this note is only about packaging its
output so an engine's own test suite consumes it without gql-proof

## what the artifact is today

`gql-proof oracle --match-mode-default different-edges --declarations
claims/turbolay.declarations.json sentences/<set>.jsonl` writes one jsonl, one
object per sentence (10 MB for 3,800 sentences). per object:

- `sentence`: the query text. `parameters`: values to send with it
  (`{"b": 1}`); `parameters_unsendable`: a parameter whose site needs a class
  the harness has no values of (a list, a record, a duration), with the
  class; the record's expectation holds for any value of it
- `graph`: the state the query runs against, engine neutral: `nodes` (id,
  `labels` set, `properties`), `edges` (id, `source`, `target`, `labels`,
  `directed`, `properties`). every element carries an `_id` property equal to
  its id; returned elements compare by it, never by engine identity. ids
  number nodes first, then edges
- `setup`: the same graph compiled three ways, conveniences derived from
  `graph`: `gql` (one `INSERT`, nodes then edges by variable), `cypher` (one
  `CREATE`), `turbolay` (vertex and relationship records as
  `MemoryStorage::with_graph` takes them), and `unloadable` naming an engine
  that cannot hold the graph (neo4j and turbolay: an undirected edge, an edge
  with two labels) with the reason
- `expect`: `tier` (`bag`: the evaluator's whole answer; `witness`: a row
  that must appear or no row anywhere; `status`: nothing beyond completion;
  both sets are all `bag` now), `outcome` (`ok`, `exception`, `invalid`),
  `status` (the exception class, or `42000` for a refusal a syntax rule
  requires), `also` (the run time class an engine that cures a dynamic
  parameter raises instead of refusing), `rule` (the rule an `invalid` rests
  on), `result` (false for a `FINISH` sentence), `rows`, and one of `bag`
  (every row; `ordered` when the order is claimed, only when no adjacent sort
  keys tie) or `bag_from` (a `LIMIT` without an order: `rows` rows, each among
  these). `binding` is the witness record, `row` the witness tier's row,
  `evaluator` the reason the evaluator stopped where the tier is weaker
- `observe`: for a `FINISH` sentence, the same statements with the in scope
  variables returned (`RETURN 1 AS n` when none) and the bag that must come
  back: the one query in the artifact the generator did not make, resting on
  hypothesis H-observe (the engine evaluates the statements the same way
  whichever result statement ends them)
- `near_misses`: up to twelve one element edits of `graph`, each `{change,
  id, name?, value?}` with its own `outcome`, `status?`, `rows`, `bag`:
  `drop_edge`, `flip_edge` (a directed edge's ends swapped), `drop_label`
  (never the last), `add_label` (one the query names), `drop_property`
  (never `_id`), `change_property` (`value` is the new one, same class).
  applied to the loaded graph in place; graphs over 64 edges get none
- `why`: reasons the record is below the bag tier; empty on every row of
  both sets

values in rows are `{"kind": K, "value": V}`: `Node` and `Edge` by id, `Path`
as the alternating id list, `Int`, `Float`, `Str`, `Bool`, `List` (of values),
`Record` (name to value), `Null` (no value), and `Opaque` with a class hint
(`string`, `date`, `zoned time`, `local time`, `zoned datetime`, `local
datetime`, `duration`, `bytes`, `decimal`, `any`) for a value the standard
leaves to the engine: the claim is a non null value of that class

## what the consumer does

`tools/engines/turbolay_oracle_probe.rs` (484 lines) reads only the jsonl.
per record: skip it with verdict `unsendable` when `parameters_unsendable` is
non empty; build the storage from `setup.turbolay`; prepare the sentence with
`parameters`; run it; convert every `QueryValue` to the value shape above
(elements by id, a path by its ids, turbolay's temporal, bytes and decimal
values as `Other` with their debug text); judge:

- `invalid`: agree on a refusal whose status starts with `42`, or on a run
  time exception whose class matches `also`
- `exception`: agree on the same status, or on the same two character class
  with the subclass noted
- `bag`: multiset equality row for row, in order when `ordered`; floats
  within a relative 1e-9; `Opaque` by class and non null
- `bag_from`: the count, and every returned row among the given ones
- `FINISH` sentences: run `observe.query` instead and judge its bag
- then each near miss: apply the change to the storage json (`mutate`), run
  the sentence or the observation query again, judge its bag the same way

`just turbolay-oracle <worktree> [artifact]` copies the probe into a turbolay
worktree as `crates/cypher-engine/tests/zz_gql_proof_oracle.rs`, runs it with
`GQL_PROOF_IN` and `GQL_PROOF_OUT`, and prints the verdict counts; the results
jsonl keeps the first three returned rows per record for triage

## the three steps

1. **a lean writer.** `gql-proof oracle --artifact` writing only the engine
   neutral core: `format` (a version), `sentence`, `parameters`,
   `parameters_unsendable`, `graph`, `expect`, `observe`, `near_misses`. no
   `setup`, no `binding`, no `why`: the graph is the source and the consumer
   compiles it. about half the size. a `format.md` next to it stating the
   value shapes and the judging rules above, so a consumer in another language
   needs nothing from this repo. keep the full writer for our own triage
2. **the consumer in turbolay's repo.** the probe moved there as a permanent
   integration test (`crates/cypher-engine/tests/gql_proof_oracle.rs`),
   building storage from `graph` directly (not `setup.turbolay`), taking the
   artifact path from an env var with a checked in fixture directory as the
   default, reporting agree, disagree by family, refused, failed, unsendable
   and the near miss counts, and failing the test on a disagreement outside
   an allow list of known findings (the list in `oracle-witness-2026-10-23.md`
   under "what turbolay says": the `?` one iteration case, multiset
   alternation, the negated wildcard, `SUM ( NULL )`, the hop cap). the
   declarations file (`claims/turbolay.declarations.json`) is turbolay's own
   statement of its implementation defined choices and belongs beside the
   test
3. **publishing.** the two artifacts (two and three variables) as release
   assets of gql-proof, named by the sentence set and the commit, so
   turbolay's ci pulls a version rather than a worktree. regenerate when the
   generator or the oracle changes; the sentence sets themselves are cached in
   `sentences/`

## what to know before touching it

- the record's value shape and the probe's `to_json` must agree; change one,
  change the other. `tests/oracle.rs` pins the record side
- `_id` must never be a property name the generator spells; the leaf provider
  spells `a`, `ab`, ...; a generator change there breaks element comparison
- an engine with a different ID086 default needs its own run
  (`--match-mode-default`), and its own declarations file
- neo4j parses almost none of the gql sentences (its cypher has no `<-` edge
  abbreviation); `tools/engines/oracle_neo4j.py` is a witness row runner only
  and would need a gql to cypher rendering to be worth extending
