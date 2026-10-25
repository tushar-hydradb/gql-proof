# gql-proof

gql-proof generates gql queries straight from the iso standard (iso/iec 39075:2024, with technical corrigendum 1:2026 applied), so running them against a database says which parts of gql it handles. what it cannot reach is listed with the reason, so the list of what is left comes from the standard and not from us

it was built for turbolay and runs against neo4j too. anything that takes gql text can be tested with it

## what it does today

- reads iso's own grammar and the standard's conformance rules by machine. nothing is tagged by hand, and corrigendum 1's edits are applied on top
- generates queries that use every rule of the grammar, every rule in every place it can appear, and every short chain of rules. with every feature claimed that is 2,133 grammar productions and 3,408 of 3,416 production-in-place pairs, and what is left out comes with a reason
- the queries mean something, not just parse: every variable is bound before it is used and every expression is typed, at up to 2 variables
- of the standard's 426 syntax rules that constrain a query, 253 are kept as written, 92 by a stricter reading, 5 are checked after the fact and 76 are open, each listed in `research/static-semantics-inventory-2026-10-22.md`
- every query is checked by a second, separately written checker before it goes out, so a generator bug does not turn into a false failure for the engine
- feature claims: give it the features an engine supports (`claims/turbolay.claim`) and it generates only those. for every feature left out, it generates a query the engine has to reject
- measures someone else's test suite with the same yardstick (`cover`). turbolay#261's 11,500 queries were measured this way

on turbolay #243 (484d1a72), turbolay accepts 1,401 of the 2,243 typed queries. take out the queries that are our own mistakes, turbolay's documented deviations and the ones needing parameters, and turbolay handles 1,420 of 1,707 (83%). most of the rest is two turbolay parse gaps, and on our side one rule family about path patterns that we do not enforce yet

not yet:
- answers for what the standard leaves to the implementation. for 3,604 of the 3,800 typed queries a graph is built from the query's patterns and the whole result on it is computed from the general rules (`gql-proof oracle`, `research/oracle-witness-2026-10-23.md`); the 180 left are queries whose result is implementation-defined (SESSION_USER, the clock, byte strings) or that modify data, and a run checks only that the engine accepts or rejects them and with which status
- 3 variables, which the coverage argument needs for productions
- a catalog, so nothing refers to a named graph, a graph type or a procedure

## where it is going

the end goal is evidence, per feature an engine claims, that the engine is total over it: every construct the standard defines for the feature is used by some valid query, and the engine answers each one right, with the right rows or the right error. anything that could not be reached is listed with the reason

the claim gets written the way bernot, gaudel and marre frame testing: a set of hypotheses (the bound on variables is enough, the test graphs are representative, and so on), each one either proven, built in, or stated as an assumption. so the claim says exactly what it rests on

## roadmap

in the order they block the claim, details in `roadmap.md`:
1. static semantics sound: close the open syntax rules our queries still break, starting with path patterns
2. 3 variables, which needs the engine faster
3. graphs to run against and the first answer checks: a witness graph per query, and checks that compare equivalent queries
4. negatives at the parse and syntax rule level, labelled with what they should fail with
5. a reference evaluator for the read-only core, exception conditions included
6. the claim for that core, written out in bernot's terms
7. grow outward: the catalog, data modification, value edge cases

## how it differs from a fuzzer and a tck

a fuzzer generates random inputs from a seed, or mutates a corpus, and reports the input that broke something. classic fuzzers only notice crashes. database fuzzers like sqlancer and gdsmith add logic checks that compare equivalent queries or several engines, which catches inconsistency but not an engine that is consistently wrong. none of them can say how much of the language they tested

a tck (the opencypher one, or the one opengql has started) is hand written scenarios with expected results. good at checking answers, but it covers what its authors thought of, and nothing says how much of the standard that is

gql-proof sits between them:
- the targets come from the standard, every grammar rule in every place, so coverage has a denominator and what is left is listed. a fuzzer has no denominator, a tck's is whatever got written
- it is deterministic. same inputs, same queries, and each query says which targets it covers
- there is an argument for why the bound is enough (a fixed number of variables covers everything more variables would), instead of "we ran it for a day"
- the weak spot today is the answer check. a tck checks rows and gql-proof does not yet, and the planned checks start with the same comparisons the database fuzzers use

so they fit together. a tck's scenarios are the answer checks we lack, and our queries are the coverage a tck lacks

## getting the iso material

nothing iso owns is in this repo, in any commit. you need three things, and you need your own copy of the two pdfs:

1. **iso's published grammar files.** free to download from https://standards.iso.org/iso-iec/39075/ed-1/en/ under iso's customer licence. `just fetch` downloads them into `grammar/` and checks them against `grammar/SHA256SUMS`, so a changed file stops the build instead of quietly changing what gets generated
2. **the standard, iso/iec 39075:2024 (first edition, 2024-04).** buy it from iso, https://www.iso.org/standard/76120.html, or from your national standards body. the licence is single user, so each person running this needs their own copy. save it as `papers/iso/ISO_IEC_39075_2024.pdf`
3. **technical corrigendum 1, iso/iec 39075:2024/cor 1:2026 (2026-07).** from https://www.iso.org/standard/93701.html. save it as `papers/iso/ISO_IEC_39075;2024_Cor_1;2026_en.pdf`

why the pdfs: iso's grammar files are still the 2024 ones, and corrigendum 1's grammar edits only exist in its pdf. the conformance rules, which say what each feature means, only exist in the standard's pdf. so the build needs both

the extractors were written against copies from the iso store. a copy laid out differently should fail loudly, since the extraction checks itself against annex a, the feature list and table 10

everything made from these stays local and gitignored: `papers/` holds the pdfs, `grammar/` the downloads and what is derived from them (only its README and the checksums are committed), `iso-text/` the standard's text for the inventory tools

## setup

needs rust 1.85 or newer, a c compiler (libmarpa builds from source), [just](https://github.com/casey/just), [uv](https://github.com/astral-sh/uv) and python 3. docker for the neo4j runs, a turbolay checkout for the turbolay runs

```
just venv        # python env for the pdf tools
just grammar     # downloads iso's files, reads cor 1, writes the corrected grammar
just features    # the conformance rules, from the standard's pdf
just test        # everything above, then the test suite
```

`just iso-text` writes the standard's text to `iso-text/`, only needed for the syntax rule inventory (`tools/inventory/`)

## running it

the binary is `gql-proof`, `cargo run --release -- <command>` or `target/release/gql-proof <command>`. `--help` on any command lists its flags

queries that use every grammar rule, then every rule in every place, then chains of 3:

```
gql-proof purdom --format sentence
gql-proof purdom --cdrc --format sentence
gql-proof purdom --cdrc --k 3 --format sentence
```

only what an engine claims, shortest query per target, as jsonl:

```
gql-proof purdom --short --claim claims/turbolay.claim --format jsonl
```

typed queries, every variable bound and every expression typed, one per target. about 10 minutes and 1.3 gb at 2 variables:

```
gql-proof context --rule types --slots 2 --join --keys --phase cover --cdrc --sentences --jsonl --rules all --claim claims/turbolay.claim
```

the generated sets are cached in `sentences/`, so run against those unless the generator changed

queries an engine has to reject, one per unclaimed feature:

```
gql-proof negatives --claim claims/turbolay.claim
```

someone else's queries, measured with the same coverage:

```
gql-proof cover their-queries.jsonl
```

against engines:

```
just neo4j                              # a throwaway neo4j in docker, every short query with EXPLAIN
just turbolay ~/code/turbolay           # short queries through a probe test in a turbolay checkout
just turbolay-typed ~/code/turbolay     # the typed set, same way
python3 -I tools/engines/breakdown.py target/engines/turbolay-typed-results.jsonl
```

the witness graphs and expected rows, and a run that loads each graph and compares:

```
gql-proof oracle --match-mode-default different-edges --declarations claims/turbolay.declarations.json sentences/typed-2vars-turbolay-claim-vars.jsonl > target/engines/oracle-typed.jsonl
just turbolay-oracle ~/code/turbolay     # each graph loaded, the query run, the whole result compared, then every near miss
```

`breakdown.py` sorts every refusal by cause: our invalid query, an engine parse gap, a documented deviation, a data error raised as it should, a bug already reported. its rules match turbolay's messages at #243, a new engine needs its own

## docs

two kinds, and the first line says which:
- for people, written to be read: this readme, `approach.md` (the idea in five minutes, with a worked example and a comparison to turbolay#261), `roadmap.md`, `research/progress-2026-10-22.md`, `grammar/README.md`
- for agents, terse on purpose and marked `> for agents` at the top: `reference.md` (every command, flag, reading and measurement), `algorithm.md` (how generation computes and what it costs), `research/` (dated working notes), `sentences/README.md`
