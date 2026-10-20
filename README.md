# gql-proof

grammar driven conformance evidence for gql (iso/iec 39075). the target is the iso grammar itself, vendored in `grammar/`, not any engine's antlr grammar

roadmap:
- purdom 1972 covering trees from the iso bnf, seeded and depth capped. this is what is here today
- k-path coverage with a tunable k, purdom is roughly k=2
- a context provider driven by the spec's syntax rules (binding, typing, scoping), plus negative tests
- the claim written as bernot, gaudel and marre test hypotheses: correct up to the bound, given regularity and uniformity

## purdom

```
cargo run --release -- purdom --seed 1 --max-depth 50
```

builds a set of derivation trees from `<GQL-program>` that together use every production at least once. the grammar is desugared first, so every `[..]` is seen both present and absent and every `...` both once and repeated

- `--seed` only breaks ties between equally cheap choices. same seed, same trees. different seeds, same coverage
- `--max-depth` caps tree height. each `[..]`, `{..|..}` and `...` adds a level after desugaring, so 46 is the smallest cap that covers everything reachable from `<GQL-program>`. productions that need more are listed with the depth they need
- `--max-new-per-tree` stops a tree chasing new productions after that many, for smaller trees
- `--format tree|sentence|both|summary|jsonl`, `--tree N` for one tree, `--expand-lexical` to show identifiers and literals down to characters
- `--start` picks another start symbol, e.g. `token` for the lexical layer

the 23 definitions the standard gives in prose ("!! See the Syntax Rules") are filled by `StubProvider` in `src/leaf.rs`. three are left as `<name>` on purpose since they are implementation defined or have no sensible default

with seed 1 and depth 50, 2144 of 2663 desugared productions are covered. the other 519 are not reachable from `<GQL-program>`, mostly the lexical layer and definitions only referenced from prose

## checking against opengql

rendered sentences parsed with opengql's `GQL.g4` (python target): 81 of 116 parse. the failures are mostly opengql being stricter than the iso bnf:
- non-ascii `<other digit>` in numeric literals
- spaces and separator continuations in byte string literals (`X'AE BC' 'DC'`)
- `TEMP` in an element variable declaration
- a relative schema path with no trailing solidus (`AT .. a`)

still unexplained: union value types inside record and node types, and our `INTERVAL '1' DAY` stub for sql interval literals
