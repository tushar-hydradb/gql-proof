# gql-proof in five minutes

## the goal

evidence, per feature, that turbolay implements iso gql (iso/iec 39075) totally:
for every feature turbolay claims, every construct the standard defines for it
is exercised by some valid query, the engine accepts each one and answers it
correctly, and for every feature it does not claim, the engine rejects what it
should

"totally" is the hard word. a test suite usually shows the engine works on the
cases someone thought of. we want the cases to come from the standard itself, so
the claim is "nothing in the spec for this feature was left untested", and
anything we could not reach is listed with the reason

## the approach, as an analogy

think of the gql grammar as the road map of a city. every rule of the grammar is
a road, every query is a trip

- **the map comes from the standard, not from us.** we read iso's own grammar
  file and conformance rules by machine, so the set of roads is the spec's, not
  a list we picked
- **visit every road (production coverage).** like a postman's route, we plan a
  small set of trips that together drive down every road at least once (purdom's
  algorithm, 1972)
- **enter every road from every road that leads into it (cdrc).** a road can
  behave differently depending on where you came from, so each road is driven
  from every junction that feeds it
- **drive every sequence of k turns (k-paths).** bugs hide in combinations, so
  every chain of 2 and 3 consecutive roads gets driven too (havrikov and zeller)
- **obey the traffic laws (meaning).** some trips are on the map but illegal:
  using a variable before declaring it is like boarding without a ticket, adding
  a date to a node is driving the wrong way down a one-way street. the
  standard's syntax rules and typing rules are the laws, and every trip we
  generate must obey them. this is the part in progress
- **drive into every closed road too (negatives).** for each feature turbolay
  does not claim, a trip that uses it and nothing else unclaimed: the engine
  must turn it away with the right status
- **an independent inspector checks every trip.** a second, separately written
  checker re-reads each generated query against the standard. nothing goes out
  that it refuses, so a generator bug cannot turn into a false failure
- **the oracle says where the trip should end.** running the query is not
  enough, the answer must be right. today we check accept or reject and the
  status class; the plan is a reference reading of the semantics plus checks
  that compare equivalent queries (rewrite a query a different way, the answer
  must not change)

## a small example

a grammar for addition, subtraction and unary minus, in pest:

```
expr = { term ~ (op ~ term)* }
op   = { "+" | "-" }
term = { neg | num | paren }
neg  = { "-" ~ term }
paren = { "(" ~ expr ~ ")" }
num  = @{ ASCII_DIGIT+ }
```

**sentence generation, production coverage.** the roads are: `expr` with and
without a tail, `+`, `-`, `term` as `neg`, `num` or `paren`. one trip drives all
of them:

```
-(1 + 2) - 3
```

**cdrc.** `term` sits in three places: at the start of an `expr`, after an `op`,
after a unary `-`. each of its three forms is driven from each place:

```
1          -1          (1)            term at the start
1 - 2      1 - -2      1 - (2)        term after an op
--1        -(1)        - 1            term after a unary minus
```

**k-paths.** chains like `expr > term > neg > term > paren` get a trip each:
`-(1)`, `--(1)`, `(-1) + 2`

**meaning.** this grammar has none, so add one law: say the engine supports `let
x = 1 in x + 2`. then `x + 2` alone is on the map but illegal (x was never
declared), and every trip we generate declares what it uses

**negatives.** if unary minus were an unclaimed feature, the trip `-1` must be
rejected, with the status the standard prescribes for unsupported syntax. and
things off the map entirely: `1 +`, `+1`, `(1`

**the inspector.** a separately written checker re-reads `-(1 + 2) - 3` against
the grammar and the laws before it is sent

**the oracle.** a reference evaluator says `-(1 + 2) - 3` is `-6`; the engine
must answer `-6`. plus an equivalence check: `-(1 + 2) - 3` and `-3 - (1 + 2)`
must agree

## against vishal's approach (turbolay#261)

vishal (with devin) went the other way round: start from turbolay's own rules
ledger (266 rules marked for testing), write a generator per rule family that
fills query templates, and write an oracle model per rule that checks the actual
rows, statuses and diagnostics. about 11,500 distinct queries

measured with the same yardstick, the standard's grammar:
- productions: ours 1,604, his 1,096, out of 2,658
- cdrc: ours 2,474, his 1,435, out of 3,416
- 3-paths: ours 4,838, his 1,713, out of 6,956
- every production his queries reach, ours reach too

### where we beat it

- **the denominator is the standard.** his covers the rules someone put in the
  ledger; ours covers every production, context and path of the spec, and lists
  what is left
- **breadth.** 508 productions only we reach: data modification, yield, path
  unions, most value types, case, trim and normalize, byte strings, comments,
  offset and limit forms. we also hit lexical corners no template writes
  (`RETURN ٣`, `8.E8`, `LIST [ ]`), some of which turbolay gets wrong
- **it is honest about iso.** about 800 of his queries that count as passes are
  not iso gql at all (reserved words as names, cypher's `WITH` and `UNWIND`).
  turbolay accepts them as cypher extensions, which is fine, but they are not
  compliance evidence
- **negatives come for free.** a must-reject query per unclaimed feature,
  generated, not hand written
- **auditable and repeatable.** everything is derived from iso's files by
  machine; when the standard changes (we already applied corrigendum 1), we
  regenerate. his oracle models are llm-written readings of the spec, 14.8k
  lines that already needed one round of corrections after review

### where we lose, even once ours is complete

- **the oracle.** his checks rows with multiplicity and order, exact gqlstatus
  codes, diagnostic records, a test clock and session identity, on a graph built
  to have parallel edges and self loops. ours checks accept or reject and the
  status class until our oracle exists, and even then coverage of the grammar is
  not coverage of the data: a path query on a graph with no self loop never sees
  the self-loop bug
- **turbolay-specific behaviour.** his tests target what turbolay promises,
  extensions included. we only speak for iso
- **readability.** his queries read like real queries and fail with a clear rule
  name; ours are the shortest sentences that drive a road, which are strange
  looking and need the inspector's report to explain
- **runtime-only errors.** errors that depend on values at run time (a type
  error on actual data, 22G03) are reached by his models directly; grammar
  coverage only reaches them by luck until the oracle and test data exist
- **cost of meaning.** making every generated query obey the traffic laws is the
  expensive part, and we are still working out how to do it fast. his templates
  are valid by construction for the shapes they write, at no compute cost

the two fit together: his per-rule oracle models are the tier we lack, and his
~9,000 well-formed queries are a corpus our checker has to accept. the plan is
to take his oracle rather than rebuild it, and keep our generator as the source
of what to test
