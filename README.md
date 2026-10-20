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

## syntax rules compiled into the grammar

some syntax rules are not about binding or typing at all: they forbid combinations a grammar could rule out but iso chose to state in prose. `src/refine.rs` writes each as a tree automaton (a bottom-up pass with finitely many states) and compiles it into the grammar, one copy of a nonterminal per state, so the generator only builds queries that satisfy them and everything else keeps working unchanged:
- 16.4 SR 14: an unbounded quantifier (`*`, `+`, `{n,}`) is inside a restrictive path mode, a selective path pattern, or under `DIFFERENT EDGES`
- 16.4 SR 6: with `KEEP`, no path pattern has its own search prefix
- 13.1 SR 5: a data-modifying statement modifies something. without it a bare `MATCH` is a whole program in the bnf

`--match-mode-default portable|different-edges|repeatable-elements` sets ID086, the match mode a pattern without one gets. `portable` (default) assumes neither, so queries are valid on any engine. `--rules none` turns the layer off

`verify.rs` checks each rule again, written from the rule text and sharing no code with the automata, and every printed query passes it. a test runs both over unrefined trees, about a fifth of which break a rule, and requires the same verdict on every one

readings we chose, where the text is open:
- 16.4 SR 6 and 14 say "contain", which in iso is transitive and would let an outer `MATCH` reach into subqueries nested in it. we apply them per depth of graph pattern matching, the notion 16.4 SR 2 sets up
- 13.1 SR 5 counts a data-modifying statement in the statement's own sequence, or in a nested `{ ... }` procedure that is one of its elements, following 13.1's function text. one buried in a subquery elsewhere does not count

with the rules on (seed 1): reference height 49, reference length 99, 327 sentences, iso coverage unchanged at 2139, and 2372 of 2902 productions covered in context, i.e. each production in each state the rules tell apart

not checked yet: binding, typing and scoping. that is the context provider's job

## cdrc and k-paths

purdom covers each production once, in whichever context is cheapest. two criteria cover constructs in context, both counted on occurrences (positions on right hand sides, so the same symbol in two places is two things to cover):
- `--cdrc`: context-dependent rule coverage (lämmel 2001): every production of X used at every place X occurs. empty alternatives count, so every optional is seen absent in every context
- `--k N`: k-path coverage (havrikov, kampmann & zeller, tosem 2022): every chain of up to N symbol occurrences along a root path, desugaring groups skipped. empty alternatives have no symbols, so cdrc and purdom cover what k-paths cannot

token-level definitions are leaves unless `--k-lexical`. after purdom's trees, each target not yet covered gets the shortest tree within the height cap that contains it (their algorithm 1, longest targets first), and every target that tree happens to contain is dropped. targets are counted on the unrefined grammar and built on the refined one, so the compiled syntax rules still hold and every tree still passes the verifier

seed 1, rules on, default depth 49:
- `--cdrc --k 3`: 1737 trees in under a second. cdrc 3414 of 3418, 3-paths 6952 of 6956
- `--cdrc --k 4`: 4251 trees. 4-paths 16139 of 16149
- `--cdrc --k 5`: 10539 trees in 1.3s. 5-paths 40761 of 40835

what is left is reported with a reason: the implementation-defined access mode (no portable form), one cdrc pair inside the fixed time zone string token, and a few deep chains in simplified path patterns that need more height than the production-based reference height gives

## checking against opengql

rendered sentences parsed with opengql's `GQL.g4` (python target): 81 of 114 parse. every failure is a sentence that passes the checks above, so opengql is stricter than the iso bnf there:
- non-ascii `<other digit>` in numeric literals
- byte string literals continued after a newline
- `INTERVAL '1' DAY`, which 21.2 SR 70 takes from sql
- `TEMP` in an element variable declaration, `RETURN NO BINDINGS`
- a relative schema path with no trailing solidus (`AT .. a`)
