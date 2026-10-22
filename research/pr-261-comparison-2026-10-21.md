# turbolay#261 against gql-proof

> for agents: dated working notes, terse on purpose. people start at the [readme](../README.md)

hydra-db/turbolay#261 ("complete generated models for all 266 ledger rules", vishal via devin, opened 2026-10-20, base `vishal/gql-procedures`, head 37f5216e) adds generated rule tests to turbolay. this compares the two approaches and measures its queries with our coverage

## the two approaches

#261:
- starts from turbolay's own rules ledger: 266 keys marked `Coverage::Test`, picked by hand
- one hand-written rust generator per rule family, queries from `format!` templates crossed in a bounded product, plus 64 seeded random interactions. 15,057 cases and 135 positive controls at the default budget, 11,493 distinct queries
- an oracle model per rule written in the test: paths enumerated on a fixed 3-node graph with parallel edges and a self-loop, exact gqlstatus, prepare against execute, rows with multiplicity and order, diagnostic records, a test clock and session identity
- 397 known failures pinned by exact snapshot, 232 of 266 keys with every sample passing

gql-proof:
- starts from iso's own artifacts, read by machine: the bnf, the conformance rules, table 10, cor 1
- coverage criteria over the grammar: purdom, cdrc, k-paths
- negatives per unclaimed feature, an independent verifier
- checks accept or reject and the status class. no semantics yet, so most sentences are invalid in meaning

where each is stronger:
- denominator: #261 has the rules someone put in the ledger, we have every production and feature of the standard
- meaning: #261 is valid by construction for the shapes its templates write, ours is wide in syntax and mostly invalid in meaning
- oracle: #261 checks rows, statuses and diagnostics, we have none yet
- risk: #261's models are llm-written readings of the spec, already corrected once after review (literal, cast, temporal, session and clock, warnings), 14.8k lines to audit. ours misses meaning, so many rejections are right for the wrong reason

## coverage, measured

`gql-proof cover` parses each sentence with the iso grammar (2024 + cor 1) into a derivation tree, runs the verifier on it, and measures it like our own trees. #261's queries were dumped with a local-only test in a checkout of the pr, never pushed. ours are `purdom --claim claims/turbolay.claim --cdrc --k 3`

| | #261, default budget | ours | both |
|---|---:|---:|---:|
| distinct sentences | 11,493 | 1,076 | |
| iso parse | 10,319 | 1,076 | |
| productions (of 2,658) | 1,096 | 1,604 | 1,604 |
| cdrc (of 3,416) | 1,435 | 2,474 | 2,478 |
| 1-paths (of 2,087) | 1,028 | 1,566 | 1,566 |
| 2-paths (of 3,590) | 1,379 | 2,591 | 2,595 |
| 3-paths (of 6,956) | 1,713 | 4,838 | 4,866 |

- every production #261 reaches, ours reaches
- only #261: 4 cdrc targets and 32 k-paths, all value expression nesting (a reference value in a comparison, a parenthesized duration, `FOR` heading a query), partly down to which tree the parser keeps
- only ours: 508 productions. data modification, yield, simplified paths and path unions, most value types, case, trim and normalize, byte strings, comments, offset and limit forms
- the measure runs a little low for both: the iso grammar is ambiguous and the parser keeps the first tree the verifier takes. ours parsed back gives 1,604 productions where the generator counts 1,620

## what has no iso parse

1,174 distinct queries:
- 581 expected to succeed use a reserved word as a name, which 21.3 SR 18 forbids unless delimited: `:Start` 264, `{year: ...}` 155, `offset` 84, `hour` 28, `:Number`, `AS exact`, `$upper`
- 165 write `CURRENT_DATE IS :: DATE`. `IS` needs a `<value expression primary>` before it, so iso wants `(CURRENT_DATE) IS :: DATE`
- 58 use cypher's `WITH` and `UNWIND`
- about 30 use a lower-case exponent or suffix (`1e308`, `1.25m`). the bnf has `E`, `M`, `D`, `F` only, and 21.3 SR 25 folds case for keywords only. a reading, not settled
- 1 expects `MATCH (`x`:M ...)` to succeed, but a `<binding variable>` is a `<regular identifier>` only
- the rest are deliberate bad inputs expected to be rejected (`0b12`, `0x 1`, `42AS v`, a separator inside a literal)
- about 150 are our parser being stricter than iso: backslash escapes in `<character representation>`, and the sql interval forms (`DAY(1)`, `MONTH TO YEAR`) the verifier's leaf rule does not take

so about 800 queries #261 counts as normative passes are not iso gql. turbolay accepts them as cypher compatible extensions

720 queries parse but fail the verifier, nearly all the verifier's stricter iso 8601 forms (it refuses `TIME '12:00'` and `P2D`, which iso allows) and deliberate invalid dates (`DATE '1999-00-00'`). they still count for coverage

## overlap with our reported gaps

- found by both: a byte string continued across a comment (#261's K19, our #241 comment)
- only ours: `RETURN ٣`, `8.E8` and `9.D`, `LIST [ ]` and `ARRAY [ ]`, `EXISTS ( MATCH ... )`, `LET VALUE`. lexical and syntactic corners a template never writes
- only #261: most of its 31 gap rows are about meaning (wrong rows, diagnostic fields) or syntax rules that should reject (K8, K10, K11, K13, K14, K22), which our roadmap lists as syntax rule negatives
- `8.M` and `8.E8` are ambiguous in the iso grammar itself: a decimal literal with a suffix, or a property of a number. only typing (20.11) rules the property out
- #261's K12 lists the 135 refused simplified path compositions as a gap, while deviations.md L4 calls the refusal deliberate

## what we take from it

- #261's per-rule oracle models are the tier we do not have (rows, multiplicity, diagnostics, clock and session context). once the context provider makes our sentences valid in meaning, they are worth absorbing as the oracle rather than rebuilding
- its ~9k iso-parseable queries expected to succeed are well typed by construction, so they are a corpus our context provider has to accept: any it refuses is a bug in ours, or in its oracle
