# feature tagging: what we collect and how

> for agents: dated working notes, terse on purpose. people start at the [readme](../README.md)

goal: given a set of claimed features, generate only conforming gql for that set, and for every unclaimed feature generate queries the engine must reject. everything is derived from iso's own data, nothing is tagged by hand

## sources

machine readable, from https://standards.iso.org/iso-iec/39075/ed-1/en/:
- `features.xml`: 228 feature codes and names
- `bnf.xml`: every `<name>` a rule mentions must resolve here
- `conditions.xml`: the gqlstatus classes and subclasses, needed for negative labels and later the oracle
- `implementation-defined.xml` (117 entries) and `implementation-dependent.xml` (20), needed for parameters like ID086 and IE005

none of them are stored in the repo. a `just` recipe downloads them where they are needed and they stay gitignored

nothing machine readable maps features to grammar. opengql's `GQL.g4` has no feature annotations, vendors (neo4j, fabric, ultipa) only publish supported-feature lists, and no other public extraction turned up. so the mapping has to come from the pdf. it is regular enough that a parser can extract it:
- 5.3.7: a standard-defined feature is defined by its conformance rules, explicit or implicit, and "an implicit conformance rule is any normative statement that begins 'Without Feature nnn,'". so the set of statements to collect is defined by the spec itself: every sentence starting "Without Feature"
- 5.3.2.1 defines the vocabulary those sentences use: contain, immediately contain, simply contain (no intervening `<A>` or `<B>`), directly contain (no intervening `<procedure body>`), with or without an intervening `<C>`, and "is" (a chain of unit productions). each one is a regular tree property
- annex a restates every rule grouped by feature and subclause, and puts the implicit ones that live outside conformance rules sections first (GA01, GP18, GG22, GG26, GV65, GV67, GV70, GV72, GT03). first pass: 268 "Without Feature" statements in the body, 268 in annex a. the mismatches left are extraction noise (page footers inside sentences, dropped spaces), not content
- 24.7 table 10: implied features, one row per pair of codes. text order is scrambled, so extract by position
- 24.2 and 24.3: rules on the claim itself. minimum conformance needs GG01, or GG02 plus one of GG20 to GG23. GL04 to GL10, GV45, GV65 and GP01 each need "at least one of" some other features

## the rules, by kind

first-pass classification of the conformance rules sections:
- **containment patterns, about 200.** e.g. "shall not contain a `<different edges match mode>`", "a `<keep clause>` that simply contains a `<path search prefix>`", "a `<graph pattern quantifier>` that immediately contains an `<asterisk>`, a `<plus sign>` ...", "SESSION RESET SCHEMA". all regular tree properties
- **specification devices, 4, apply to every claim.** `NO BINDINGS` in a `<return statement body>` and in a `<graph pattern yield item list>`, `TEMP` in an `<element variable declaration>`, `GROUP` in a `<list value type name>`. these are syntax iso uses internally and never lets users write, which is why opengql rejected them. today our generator emits them, so this is a bug to fix
- **typed, 12.** declared type of a value expression, comparable operands, graph or binding table reference types (GV60, GV61, GP14, GP15, GE04, GE05, GP08, GP11, GV46, GA04, GA09). record them now; the context provider enforces them
- **other structure, about 10.** fixed length path pattern operands (G031, G033), node and edge adjacency (G046, G047), "is not one of" (G045, G081), "followed by" (GL08). regular, but each needs a small extra pattern form. G041 and GQ17 talk about which variable is referenced, so they belong to the context provider
- **not about syntax.** GA01 (ieee 754 results), GA08 (diagnostic records), GP18 and GT03 (what a transaction may contain), GG22, GG26, GV65, GV67 (type and catalog semantics), GB01 (identifier length limit). they belong to the oracle and the claim, not the grammar

## what we collect, per statement

```
{ feature, name, subclause, rule, origin: conformance-rule | implicit,
  kind: pattern | device | typed | semantic,
  pattern,          // for pattern and device: the tree pattern over bnf names
  reading }         // for anything typed or semantic: who enforces it
```

plus:
- `implies: [(feature, feature)]` from table 10
- `claim_rules`: the at-least-one constraints from 24.2 and 24.3

nothing derived is stored either. the map is generated locally from the pdf and the downloaded artifacts, gitignored like them, and carries a hash of each source sentence so a changed pdf shows up

## pattern language

one constructor per term in 5.3.2.1, nothing more:
- `contains(A, B)`, `immediately(A, B)`, `simply(A, B)`, `directly(A, B)`, `is(A, B)`
- `without(C)` on any of these, for "without an intervening `<C>`"
- leaves: a nonterminal, a keyword sequence, `not_one_of([..])`, `followed_by(A, B)`
- `any_of([..])` for "a X, a Y, or a Z"

each pattern compiles to a tree automaton that implements the existing `Rule` trait, so a claim needs no new machinery: refine with "this pattern never matches" for every unclaimed feature, plus the 4 specification devices for all claims. verify.rs gets a second implementation of each pattern, written straight from the 5.3.2.1 definitions, and a differential test keeps the two in agreement, as with the syntax rules today

this replaces the earlier plan of putting tags only on optional elements. an automaton handles a mandatory position too: the productions that need the feature just become unproductive and drop out. if a claim leaves something unreachable, we report it

## what comes out

- `gql-proof features`: the extracted map, its checks, and per-feature counts
- `--claim <file>` on `purdom`: the claim is a list of codes, closed under table 10 and checked against 24.2 and 24.3. it generates conforming queries for that claim, and the coverage report is counted over the claimed sublanguage
- negatives, one unclaimed feature at a time: a tree that matches that feature's pattern and no other unclaimed one, built with havrikov's targeted search. iso has no "feature not supported" status. what an engine does with nonconforming language is implementation-defined (IE005), so the expected outcome is a declared parameter, defaulting to a class 42 syntax error or access rule violation
- per feature: its patterns, how many trees cover it, the shortest witness

## checks, all mechanical

- every feature code in a statement is in `features.xml`, and the quoted name matches its description
- every `<name>` in a pattern resolves in `bnf.xml`
- the body statements equal annex a's, as normalised multisets
- every one of the 228 features has at least one statement, or is listed by kind with where it is defined
- every statement parses into a pattern, or is classified typed or semantic. nothing is left unparsed
- table 10 codes are in `features.xml` and the implication graph has no cycles
- every pattern matches some tree of the base grammar. a pattern that matches nothing is an extraction bug
- claiming every feature leaves the grammar unchanged except the 4 specification devices, and claiming none gives minimum conformance

## extraction

- pypdfium2 is already in `.venv-pdf`. extract text with character positions, drop the header and footer bands by their y coordinate, keep the soft hyphens and join lines
- split on numbered items inside "Conformance Rules" sections. for implicit rules, scan every sentence starting "Without Feature"
- parse sentences with a small grammar over this fixed vocabulary, e.g. `pest` or `chumsky` in rust, or a python script that writes json. the sentence shapes are few: 86 distinct 14-word prefixes, most only differing in a/an and spacing
- read table 10 from text positions: two codes per row, one per column

## decided

- the extractor is python in `tools/`, next to `pdfindex.py`, using pypdfium2
- no iso file or derived file in the repo: a justfile fetches the artifacts, the extractor writes the map, both gitignored

## later

- edition 2 is at committee draft (ballot from nov 2025). since the extraction is mechanical, rerunning it on the new pdf should be all a new edition needs
