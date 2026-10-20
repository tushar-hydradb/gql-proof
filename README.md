# gql-proof

grammar driven conformance evidence for gql (iso/iec 39075). the target is the iso grammar itself, vendored in `grammar/`, not any engine's antlr grammar

roadmap:
- purdom 1972 covering trees from the iso bnf, seeded and depth capped. this is what is here today
- k-path coverage with a tunable k, purdom is roughly k=2
- a context provider driven by the spec's syntax rules (binding, typing, scoping), plus negative tests
- the claim written as bernot, gaudel and marre test hypotheses: correct up to the bound, given regularity and uniformity

## purdom

```
cargo run --release -- purdom --seed 1 --format sentence
```

builds a set of derivation trees from `<GQL-program>` that together use every production at least once. the grammar is desugared first, so every `[..]` is seen both present and absent and every `...` both once and repeated

- `--seed` only breaks ties between equally cheap choices. same seed, same trees. different seeds, same coverage
- `--max-depth` caps tree height. it defaults to the reference height, the smallest cap under which every production that can appear does, computed from the grammar: 46 for `<GQL-program>`. each `[..]`, `{..|..}` and `...` adds a level after desugaring. productions that need more are listed with the depth they need
- `--length reference|unbounded|<N>` caps sentence length, measured as purdom does: nodes in the derivation tree, desugaring groups not counted. `reference` (the default) is zheng & wu's reference length, the longest of the shortest sentences covering each production, computed under the height cap. no covering set can do with a smaller maximum, and every sentence stays within it. `unbounded` is closest to purdom's original: few, long sentences. a number caps harder, and productions whose shortest covering sentence is longer are listed with that length
- `--format tree|sentence|both|summary|jsonl`, `--tree N` for one tree, `--expand-lexical` to show identifiers and literals down to characters
- `--summary` adds the coverage summary after the trees, off by default
- `--start` picks another start symbol, e.g. `token` for the lexical layer

`!! See the Syntax Rules` alone means a definition is given in prose (16 of them); after real content it only points at extra rules (7). the prose ones are filled by `StubProvider` in `src/leaf.rs`, each stub citing the iso rule it follows. `<implementation-defined access mode>` has no portable form (8.2 SR 3), so the 2 productions needing it are excluded and reported. date, time, datetime, time zone and duration strings get fixed iso 8601 contents, derived through the grammar so they stay real derivations

with the defaults (seed 1, depth 46, reference length 92), 288 sentences cover 2139 of 2660 desugared productions, lengths 4 to 92, 67 on average. `unbounded` covers the same with 88 sentences up to 3951 long; `--length 60` takes 394 sentences and leaves 32 productions that need more than 60. the other 521 are the 2 excluded ones and 519 not reachable from `<GQL-program>`, mostly the lexical layer and definitions only referenced from prose

## checks

nothing is printed unless it passes two checkers that depend only on the iso xml, never on the desugaring or the generator

`gql-proof check-grammar` proves once for the whole grammar that printing tokens joined by one space is gql source text (21.3 SR 13, 14). every chunk printed as one token is either a literal derivable from `<token>` or a subtree of a definition that can only ever derive a single token. today: 640 syntactic definitions, 67 printed as one token, all obligations hold. assumed, with the rule behind each: `<SQL-datetime literal>`, `<SQL-interval literal>`, `<external object reference>`

`src/verify.rs` checks every generated tree:
- each node's children, with desugaring groups flattened away, match the iso ebnf of its definition
- each prose leaf satisfies its rule (xid identifiers, unicode digits and whitespace, comment contents, ...)
- token internal rules: byte string continuations contain a newline (21.2 SR 57), identifiers are not reserved words (21.3 SR 18), duration, date, time and time zone strings hold iso 8601 values (21.2 SR 59-68)
- the printed sentence is exactly the tree's tokens joined by one space

not checked yet: the syntax rules above the token layer (binding, typing, scoping). that is the context provider's job

## checking against opengql

rendered sentences parsed with opengql's `GQL.g4` (python target): 81 of 114 parse. every failure is a sentence that passes the checks above, so opengql is stricter than the iso bnf there:
- non-ascii `<other digit>` in numeric literals
- byte string literals continued after a newline
- `INTERVAL '1' DAY`, which 21.2 SR 70 takes from sql
- `TEMP` in an element variable declaration, `RETURN NO BINDINGS`
- a relative schema path with no trailing solidus (`AT .. a`)
