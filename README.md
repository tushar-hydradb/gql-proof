# gql-proof

grammar driven conformance evidence for gql (iso/iec 39075). the target is the iso grammar itself, not any engine's antlr grammar. what is left is in `roadmap.md`

## setup

nothing iso-owned is in the repo. iso publishes the grammar and its other digital artifacts for download, the standard itself is licensed per user:

```
just fetch      # the iso artifacts into grammar/, needed to build
just venv       # python for tools/
just features   # grammar/conformance.json from your copy of the pdf at papers/iso/
just test
```

everything in `grammar/` except its README is gitignored

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

with `--rules none` (seed 1, depth 46, reference length 92), 288 sentences cover 2139 of 2660 desugared productions, lengths 4 to 92, 67 on average. `unbounded` covers the same with 88 sentences up to 3951 long; `--length 60` takes 394 sentences and leaves 32 productions that need more than 60. the other 521 are the 2 excluded ones and 519 not reachable from `<GQL-program>`, mostly the lexical layer and definitions only referenced from prose

## checks

nothing is printed unless it passes two checkers that depend only on the iso xml, never on the desugaring or the generator

`gql-proof check-grammar` proves once for the whole grammar that printing tokens joined by one space is gql source text (21.3 SR 13, 14). every chunk printed as one token is either a literal derivable from `<token>` or a subtree of a definition that can only ever derive a single token. today: 640 syntactic definitions, 67 printed as one token, all obligations hold. assumed, with the rule behind each: `<SQL-datetime literal>`, `<SQL-interval literal>`, `<external object reference>`

`src/verify.rs` checks every generated tree (and, under a claim, the conformance rules in force, below):
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

with the rules on and every feature claimed (the default, seed 1): reference height 49, reference length 104, 476 sentences, 2134 iso productions covered (5 fewer than without rules: the conformance rules every claim keeps, below), and 2936 of 3515 productions covered in context, i.e. each production in each state the rules tell apart

the automata have two passes: a state inherited from the parent and one synthesized from the children. a state is a set of facts

not checked yet: binding, typing and scoping. that is the context provider's job

## cdrc and k-paths

purdom covers each production once, in whichever context is cheapest. two criteria cover constructs in context, both counted on occurrences (positions on right hand sides, so the same symbol in two places is two things to cover):
- `--cdrc`: context-dependent rule coverage (lämmel 2001): every production of X used at every place X occurs. empty alternatives count, so every optional is seen absent in every context
- `--k N`: k-path coverage (havrikov, kampmann & zeller, tosem 2022): every chain of up to N symbol occurrences along a root path, desugaring groups skipped. empty alternatives have no symbols, so cdrc and purdom cover what k-paths cannot

token-level definitions are leaves unless `--k-lexical`. after purdom's trees, each target not yet covered gets the shortest tree within the height cap that contains it (their algorithm 1, longest targets first), and every target that tree happens to contain is dropped. targets are counted on the unrefined grammar and built on the refined one, so the compiled syntax rules still hold and every tree still passes the verifier

seed 1, rules on, every feature claimed, default depth 49:
- `--cdrc --k 3`: 1824 trees in under a second. cdrc 3409 of 3418, 3-paths 6928 of 6956

before the conformance rules (same seed and depth): k 3 gave 1737 trees, k 4 4251 trees with 16139 of 16149 4-paths, k 5 10539 trees with 40761 of 40835 5-paths

what is left is reported with a reason: what the always-kept conformance rules exclude, the implementation-defined access mode (no portable form), one cdrc pair inside the fixed time zone string token, and a few deep chains in simplified path patterns that need more height than the production-based reference height gives

## feature claims

iso defines each optional feature by its conformance rules: 5.3.7 makes every normative statement that begins "Without Feature nnn," one. `tools/conformance.py` extracts all of them from the pdf, and `conformance.lark` parses each sentence. the parsing uses the containment words 5.3.2.1 defines (contain, immediately, simply and directly contain, "is", followed by), giving a tree pattern over the bnf's names. text comes from pypdfium2 by position: running heads and the licence banner are cut by height, spaces put back from glyph gaps, superscripts read as `^`. nothing is tagged by hand, and the run fails unless:
- every one of the 270 statements in conformance rules sections is recapitulated word for word in annex a, and the other way round
- every feature code is in iso's `features.xml` and its quoted name matches
- every sentence parses, as a pattern or as a named shape owned by something other than the grammar
- every feature has a statement (ga01 and gg26 are defined only by "if ... supports" text)
- table 10 (implied features, read by position) only names known features and has no cycles

result: 280 statements over 228 features. 234 are patterns; 10 typed, 15 context and 4 structural rules are kept for the context provider and later pattern forms; 2 lexical and 15 semantic rules go to the leaf provider and the oracle. on top: 5 rules every claim keeps, 71 implications and 6 rules on claims (24.2, 24.3). where a sentence reads several ways, every parse is tried, the ones claiming containment the grammar cannot have are dropped, and the most deeply nested of the rest wins

`--claim all|none|<file>` on `purdom`: a claim is closed under table 10 and checked against 24.2 and 24.3. the conformance rules of every unclaimed feature, and the 5 every claim keeps, compile into one more automaton:
- an outer definition sends a flag down to as much of its subtree as the containment word reaches, and a matching inner definition sends a hit back up, so the cost stays under real outer instances
- keyword phrases are matched over the yield with facts for "ends with the first j words", "starts with the rest", "is a middle piece"
- a rule "X contains Q" where every Q can only be inside an X is the same as forbidding Q. these are found from the grammar and rewritten, which matters because subqueries make almost everything reachable from almost everything. the same goes for a phrase that can only sit inside definitions that all forbid it

`verify.rs` reads every pattern again straight from 5.3.2.1 over the whole tree, sharing nothing with the automaton. tests run both over 799 unrefined trees: 225 of the 236 rules of the smallest claim are broken by some tree, and the two agree on every rule and tree, one rule at a time and all at once

`--claim none` (only gg01, which 24.2 requires, and gc04, which it implies) refines in about a second to 43k nonterminals. 4976 trees cover the 670 iso productions it allows, all verified, in about two minutes

readings:
- keywords after a definition (`<query conjunction> EXCEPT`, `<for ordinality or offset> that is WITH OFFSET`) mean its yield holds them in a row. `that is WITH OFFSET` could never hold of `WITH OFFSET <binding variable>` read as equality. with table 10, which makes gq05 imply gq04 and gq07 imply gq06, this also gives `EXCEPT ALL` to both features
- "is" holds when the yield of an instance of the other definition is the whole yield

`gql-proof features --claim X` checks every name against the grammar, lists the rewrites, and lists what stays enforced elsewhere. it also tries to break each pattern once. six cannot be broken as written, because the prose skips a level of the bnf:
- gs16: `<parameter name>` is not immediately in `<session reset arguments>`
- gq14 (twice) and gf20: `<sort key>` holds an `<aggregating value expression>`, not a `<value expression>`
- gf10, gf11: the set function types are inside `<general set function>` and `<binary set function>`, not immediately in `<aggregate function>`

## negatives

```
cargo run --release -- negatives --claim none
```

for every pattern of every unclaimed feature, the shortest query that breaks it and no rule of another unclaimed feature, e.g. `MATCH DIFFERENT EDGE ( ) FINISH` for g002 and `FINISH EXCEPT FINISH` for gq04. the verifier confirms exactly that before anything is printed. iso leaves nonconforming language to the implementation (IE005), so the expected status is `--unsupported-status`, default 42000, declared like ID086. `--format jsonl` gives `{negative, phase, feature, rule, expect, sentence}`

the shortest query with only the always-kept rules usually works. otherwise every other unclaimed feature is forbidden as well. for `none`: 122 of 256 patterns get a negative in about 3.5 minutes on 15 cores. the rest are reported with the features their shortest query needs too: a value type needs `CAST` (ga05) or a graph type (gg02) to appear at all, `DELETE` needs gd01, a search prefix needs an abbreviated or explicit edge form. those become negatives under a claim that includes what they need. a negative is only rejected for its feature if the rest of the query is meaningful, which is the context provider's job

## checking against opengql

rendered sentences parsed with opengql's `GQL.g4` (python target): 81 of 114 parse. every failure is a sentence that passes the checks above, so opengql is stricter than the iso bnf there:
- non-ascii `<other digit>` in numeric literals
- byte string literals continued after a newline
- `INTERVAL '1' DAY`, which 21.2 SR 70 takes from sql
- `TEMP` in an element variable declaration, `RETURN NO BINDINGS`
- a relative schema path with no trailing solidus (`AT .. a`)
