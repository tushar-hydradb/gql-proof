# the three variable run, as it stalled

> for agents: dated working notes, terse on purpose. people start at the [readme](../README.md)

one run of the typed pipeline at `--slots 3`, on `tushar/exists-table` (commit
64603f0, the path pattern automata in), alone on the machine, 2026-10-23
01:12 to 02:44. it did not finish: the ground walks stalled in one target.
everything the run printed is below so the next agent can start from the
numbers instead of repeating the 90 minutes. the two variable baseline on the
same commit is in `research/static-semantics-path-minimums-2026-10-23.md`
(559 s, 1.57 GB, 3,843 trees)

## the command

```
./target/release/gql-proof context --rule types --slots 3 --join --keys \
  --phase cover --cdrc --sentences --jsonl --rules all \
  --claim claims/turbolay.claim --match-mode-default different-edges \
  --deadline 10800
```

under `/usr/bin/time -l`, stdout to a jsonl, stderr to a log, detached with
`nohup` and a done marker (a background shell here dies at 10 minutes).
killed with SIGTERM after 1 h 31 min; exit 143; the jsonl stayed empty since
sentences are written at the end of the cover phase

## the phases

| phase | 2 variables | 3 variables |
|---|---|---|
| refined grammar | 2,972 nts, 7,854 prods | same |
| fixed point | 47 s, 34,663 labels (types 1 slot: 3.7 s) | about 5 min, 266,464 labels, 52 rounds |
| extraction layers | 24 s | 214 s, 446,805 made labels |
| reach closure | 163 s, 38,362 live labels | 1,098 s, 103,087 live labels |
| ground walks | 3,843 trees in about 5 min | 41 of 6,942 targets in 29 s, then 65 min in the 42nd |

the ratios: labels 7.7x, live labels 2.7x, closure 6.7x. the closure is the
`follow-ups-2026-10-22.md` lever (it repeats whole backward passes when the
pending table refills) and it held at 18 minutes here, so it is not what
stopped the run. the ground walks did

## the fixed point's widest nonterminals, by round

the progress line names the nonterminal with the most labels every 5 s. the
sequence: `<simple case/rep1>` (2,880 to 3,256 labels, rounds 17 to 21),
`<comparison predicate part 2>` (3,986 at round 22, 8,892 at round 52, the
widest at the end: `:bool; :bool; :exact; :exact` shapes), `<statement
block/rep2>` and `<statement block>` (4,957 to 5,285, rounds 24 to 26,
labels like `out-path#7; out-path+out-path#7`), `<procedure body>` (5,468,
rounds 27 to 28). rounds 33 to 52 added 15,000 labels in 50 s: the tail is
long and flat

## the stall, line by line

the searching lines, each followed by its `failing most` (w = failed witness
searches, c = failed context searches):

```
witness 56 (0 failed), context 37 (0 failed), 2 in progress, 34 ahead tables;
  ground 117 narrow / 0 wide / 0 failed, candidates 163 (0 no witness, 2 no context), 13.7 s
extracting: cdrc 40 of 6942, 14 trees, 13.6 s
witness 114 (0 failed), context 60 (23 failed), 0 in progress, 35 ahead tables;
  ground 178 narrow / 1 wide / 1 failed, candidates 627 (44 no context), 29.2 s
  failing most: <statement block> 0w/23c
extracting: cdrc 41 of 6942, 15 trees, 29.1 s
witness 535 (14 failed), context 712 (504 failed), 64 in progress, 80 ahead tables;
  ground 846 narrow / 5 wide / 88 failed, candidates 7,049,997 (3,455,733 no context), 59.8 s
  failing most: <statement block> 0w/461c, <let variable definition list/rep2> 0w/40c,
    <binding variable definition> 0w/2c, <node reference value expression> 2w/0c,
    <edge reference value expression> 2w/0c
witness 536 (15 failed), context 712 (504 failed) ... candidates 20,442,180, 130.6 s
witness 626 (41 failed), context 712 (504 failed), 121 in progress ... candidates 27,077,038, 150.1 s
  failing most: <statement block> 0w/461c, <let variable definition list/rep2> 0w/40c,
    <cast operand> 6w/0c, <parenthesized value expression> 5w/0c, <value expression> 4w/0c
witness 627 (42 failed) ... candidates 209,402,295 (52,079,446 no context), 1,215 s
witness 628 (43 failed) ... candidates 394,423,508 (96,008,147 no context), 2,276 s
witness 715 (49 failed), 86 in progress ... candidates 557,917,007, 2,367 s
witness 718 (51 failed), context 712 (504 failed), 85 in progress, 80 ahead tables;
  ground 966 narrow / 10 wide / 141 failed,
  candidates 737,732,700 (305 no witness, 150,072,233 no context, 1,258 narrowed), 3,175 s
  failing most: <statement block> 0w/461c, <let variable definition list/rep2> 0w/40c,
    <cast operand> 6w/0c, <value expression> 5w/0c, <common value expression> 5w/0c
```

the full log is reproduced from
`scratchpad/baseline/typed3var/stderr.txt` of session d607e2fe (gone with
the session); the lines above are verbatim but for thousands separators

## what it says

- **the context searches are what fail**: 504 of 712, and 461 of those at
  `<statement block>`. the witness searches mostly succeed (51 of 718
  failed). a context search climbs from a target to the start symbol through
  labels that admit it; at 3 variables the labels above a statement block
  (the `out-path+out-path#7` family) are many and most admit nothing from
  below. `<let variable definition list/rep2>` is the same shape one level
  down
- **the candidate count is the cost**: 737 million candidates in 53 minutes,
  150 million dropped for having no context, the rest for other reasons,
  while the counts of searches barely moved (712 context searches from the
  60 s mark to the end). one or a few targets fan out over the whole label
  space above a statement block. the counters do not say which target; the
  42nd cdrc target is the one in flight when it stalled
- **memory was fine**: no growth beyond the closure's; the stall is CPU
- **the fixed point and the closure finish** at 3 variables, 5 and 18
  minutes. a run that only did those, with `--phase` short of cover, would
  give the label counts in 25 minutes

## levers, in the order to try them

1. **name the target**: `GQL_DEBUG_FAILS=n` prints the failing searches with
   their nonterminal, label, hit and depth (`src/context/extract.rs`, the
   `failed {} search` line); `GQL_DEBUG_NT=<nt>` narrows to one nonterminal.
   run with `GQL_DEBUG_NT="statement block"` and a 10 minute deadline; the
   first 460 failures come in the first minute
2. **the context memo**: 712 context searches with 504 failing and 150
   million "no context" candidates means the failures are not memoised at
   the level the candidates are generated at. a failed `(nt, label)` climb
   should be a table hit on its next ask (`up` and `under` in `extract.rs`,
   the `above` table for the smallest context from the start symbol). check
   whether the memo is keyed by the joined label or by the label before
   joining; at 3 variables the joined labels multiply
3. **the narrowness cut** (`ground ... narrowed`): 1,258 narrowed against
   737 million candidates. the cut fires late. a cost bound from the
   `above` table (the smallest context size from the start) before expanding
   a candidate would drop the ones that cannot beat the current best
4. **statement block labels**: the fixed point's widest nonterminals are the
   statement blocks and procedure bodies with `out-path` columns; the
   equality groups plan (`~/.claude/plans/indexed-cuddling-ember.md`) was
   deferred until the 3 variable measurement said the label count hurts. it
   does not, directly: the closure took 18 minutes, the walks took the rest.
   so the groups are not the first lever
5. **parallel targets** only after the above, per
   `research/follow-ups-2026-10-22.md` (reduce the work first)

## what not to redo

- the 2 variable run is the regression gate (under 11 minutes); any change
  to extraction is measured there first, with `extraction_matches_emission`
  and `joined_grounds_are_exact` (ignored tests, about 3 minutes)
- do not run 3 variables blind or in a foreground shell: `--deadline`, the
  progress lines, `nohup` with a done marker
- the scope engine's 3 variable fixed point is a separate question
  (`--rule scope`), not measured here
