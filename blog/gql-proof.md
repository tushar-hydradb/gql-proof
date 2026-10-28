---
title: Testing a graph database against the GQL standard, all of it
publishDate: 2026-10-28
tags: ["rust", "gql", "testing", "graph-databases"]
summary: |
  GQL became an ISO standard in 2024 and every graph database now says it
  "supports GQL". Nobody can say how much. gql-proof generates queries straight
  from the standard, so the answer has a denominator. This post walks through
  how it works, and the papers each piece was borrowed from.
---

In April 2024, ISO published
[ISO/IEC 39075](https://www.iso.org/standard/76120.html), better known as GQL:
the first new ISO database language since SQL. Graph databases have been
adopting it since, and each one ships a page saying which parts of GQL it
supports.

The trouble is that "supports" is doing a lot of heavy lifting in that sentence.
Supports according to whom? Tested how? Against which parts of a standard that
runs to several hundred pages?

At HydraDB we build [hydradb](https://github.com/hydra-db/hydradb), a graph
engine with a GQL frontend, and we wanted an honest answer to that question for
ourselves. Not "we wrote a lot of tests", but "here is every construct the
standard defines for the features we claim, here is a valid query using each
one, here is what our engine did with it, and here is the list of things we
could not reach and why".

This post is about the tool we built to get that answer, [gql-proof](TODO-link).
It reads the standard by machine and generates queries from it, so the yardstick
is the standard itself and not whatever we happened to think of. It walks
through the pipeline stage by stage, and since almost every idea in it was
borrowed, it points at the paper each one came from.

---

## Motivation: the missing denominator

There are two well known ways to test a database's query language today, and
both have a hole in the same spot.

**Fuzzers** like [SQLancer](https://github.com/sqlancer/sqlancer) and, for
graphs, [GDsmith](https://arxiv.org/abs/2206.08530) generate random queries and
look for crashes or inconsistencies, for example two equivalent queries that
return different rows. They are great at finding bugs. But an engine that is
consistently wrong passes every consistency check, and a fuzzer cannot tell you
how much of the language it has exercised. "We ran it for a day" is not a
coverage number.

**Conformance suites** (a TCK, like the
[openCypher TCK](https://github.com/opencypher/openCypher/tree/master/tck) or
the one the GQL community has started) are hand written scenarios with expected
results. They are great at checking answers. But they cover what their authors
thought of, and nothing tells you how much of the standard that is.

What both are missing is a **denominator**. To say "we support 83% of GQL" you
need to know what 100% is. So the first design decision was simple: the targets
come from the standard, every target is either covered or explained, and nothing
is tagged by hand.

> [!NOTE]
> Nothing ISO owns is in the repository. ISO's grammar files are a free
> download under its customer licence, and the standard itself is a paid, single
> user PDF. gql-proof reads your own copies and keeps everything derived from
> them local.

---

## The running example

Throughout this post I'll use a tiny grammar to show what each stage does before
showing what it does to GQL. Addition, subtraction and unary minus:

```text title=toy.bnf
expr  ::= term (op term)*
op    ::= "+" | "-"
term  ::= neg | num | paren
neg   ::= "-" term
paren ::= "(" expr ")"
num   ::= digit+
```

Think of the grammar as a road map of a city. Every rule is a road, and every
query is a trip through the city. Testing a language then becomes a question
about trips: which set of trips is enough?

## Step 1: the map comes from the standard

ISO publishes GQL's grammar as an XML file of BNF definitions. That file is
still the 2024 one, while
[Technical Corrigendum 1](https://www.iso.org/standard/93701.html) (2026)
changed parts of the grammar, and its edits only exist in a PDF. So the first
stage downloads ISO's files, checks them against pinned checksums (a changed
file should stop the build, not quietly change what we generate), pulls the
corrigendum's grammar edits out of its PDF, and applies them.

The result is desugared into a plain context free grammar: every `[optional]`,
`{group}` and `repetition...` becomes ordinary nonterminals. For GQL that is
1,266 nonterminals and 2,658 productions.

The same goes for features. GQL is split into optional features (`G035`, `GQ15`,
...) and the standard ties each to the grammar with conformance rules of the
form "without feature X, conforming GQL language shall not contain Y". gql-proof
reads those rules out of the standard's PDF and checks the extraction against
the standard's own feature list and tables, so a copy laid out differently fails
loudly instead of silently tagging the wrong thing.

One more thing has to be settled before generating anything: how to print a
derivation tree as text. We always put one space between tokens. That sounds
obviously safe, but it is not free. Two tokens glued or split the wrong way can
lex as something else. So `gql-proof check-grammar` proves, once for the whole
grammar, that every chunk we print as a single token really is a single token,
and therefore that one-space rendering is always valid GQL source text.

## Step 2: drive down every road

The oldest idea in the pipeline is from 1972.
[Paul Purdom's sentence generator](https://doi.org/10.1007/BF01932308) finds a
small set of sentences that together use every production of a grammar at least
once. It precomputes, for every nonterminal, its shortest derivation and the
cheapest way to reach it from the start symbol, then builds sentences greedily,
each one picking up as many unused productions as it can.

For our toy grammar one sentence is enough:

```text
-(1 + 2) - 3
```

`expr` with and without a tail, both operators, and all three forms of `term`:
every road, one trip.

The only thing we added is a length budget. Purdom's sentences can get long, and
long queries are hard to read when they fail. Zheng and Wu's reference length
([as described by Xu, Zheng and Chen](https://doi.org/10.1109/SEFM.2010.21))
gives a principled cap: take, over all productions, the length of the shortest
sentence that covers it. No covering set can do better than that maximum, so it
is the tightest cap that loses nothing.

This step is cheap. On the whole GQL grammar it takes milliseconds, because it
never searches: everything is a lookup in two precomputed tables.

## Step 3: from every junction, and every short chain

Production coverage is a weak criterion. A road can behave differently depending
on where you came from: `term` at the start of an expression is not the same
test as `term` after a unary minus. So the next two criteria count contexts.

**Context dependent rule coverage** (CDRC), from
[Ralf Lämmel's "Grammar Testing"](https://doi.org/10.1007/3-540-45314-8_15),
asks for every production of `X` at every place `X` appears. For `term` that is
three forms times three places:

```text
1          -1          (1)            term at the start
1 - 2      1 - -2      1 - (2)        term after an op
--1        -(1)        - 1            term after a unary minus
```

**k-path coverage**, from
[Havrikov, Kampmann and Zeller](https://doi.org/10.1109/ASE.2019.00027), asks
for every chain of k symbols along a root path of a tree. Bugs like to hide in
combinations, and k-paths are a tidy way to ask for combinations without asking
for all of them. `expr > term > neg > term > paren` gets a trip of its own:
`-(1)`.

Their paper also gives the algorithm we use for both: for each uncovered target,
the shortest tree that contains it is the shortest context down to the target,
the target itself, and the shortest subtree everywhere else. Again, table
lookups. With every feature claimed, GQL has 3,416 CDRC targets and we reach
3,408. The other eight are listed, with the reason.

## Step 4: the rules a grammar could have said

So far everything is syntax. But a lot of what GQL forbids is not in its
grammar. The standard has around a thousand **syntax rules**, written in prose,
and 426 of them constrain what a query may contain. Some of those are things a
grammar could have expressed but the authors chose to write as prose. For
instance, the standard requires a path pattern to contain at least one node, so
`MATCH <- ?` (an edge that may be absent) parses fine but is not valid GQL.

Rules like that are structural: they only look at the shape of the tree. Each
one becomes a small **tree automaton**, with a state passed down from parent to
children and a state passed up from children to parent, and a way to reject a
node outright.

The nice part is a classic result: the derivation trees of a context free
grammar, intersected with what a finite tree automaton accepts, are again the
derivation trees of a context free grammar
([Thatcher](<https://doi.org/10.1016/S0022-0000(67)80022-9>); see
[TATA](https://inria.hal.science/hal-03367725) for the modern treatment). So
instead of filtering bad queries after the fact, we multiply the rules into the
grammar. Each nonterminal gets one copy per pair of states the rules can reach,
and Steps 2 and 3 run on the refined grammar unchanged. Every query they produce
obeys the rules by construction.

Feature claims work the same way. A claim is a list of feature codes, say
`claims/turbolay.claim`, and every unclaimed feature becomes an automaton that
says "this never appears". Generate from that grammar and you get only what the
engine claims. Flip it around, one unclaimed feature at a time, and you get a
query the engine **has to reject**. Those negatives come for free.

> [!NOTE]
> The discipline here comes from software product lines:
> [Kästner et al.'s CIDE](https://doi.org/10.1007/978-3-642-02571-6_11) only
> lets you tag parts of a grammar that are already optional, so removing a
> feature never leaves broken syntax. The standard's conformance rules turn out
> to follow the same discipline, which is what makes extracting them by machine
> work.

## Step 5: obeying the traffic laws

Here is where it gets hard. Most of the rules that matter are not structural. A
variable has to be bound before it is used. Adding a date to a node is a type
error. Boarding without a ticket, driving the wrong way down a one way street:
the trip is on the map, but it is illegal.

Purdom on the raw grammar ignores all of that. Hennessy and Power ran it on the
ISO C++ grammar and
[got 81 sentences, 7 of which were valid programs](https://doi.org/10.1007/s10664-008-9067-7).
That number is the whole motivation for this step.

### Attempt one: multiply everything

The obvious move is to treat scoping and typing like Step 4: compile them into
the grammar. A nonterminal becomes a triple of (nonterminal, what it inherits,
what it synthesizes), where the state is a set of facts per variable name: bound
as a node, bound as an edge, used, declared, of type string, and so on.

It works. With two variable names it produced 1.7 million productions (from
2,658), took five minutes and 2.3 GB, and every query it generated was valid.
With three names it never finished in four hours. Every fact is per name, so a
third name multiplies every state set. The input algebras of
[Gopinath, Nemati and Zeller](https://doi.org/10.1109/ICSE43902.2021.00070)
rewrite the grammar the same way and hit the same wall.

> [!NOTE]
> This is where everybody else takes a different road.
> [Xsmith](https://doi.org/10.1145/3624007.3624056), Csmith, SQLancer and
> GDsmith carry an environment beside the derivation and consult it while
> choosing. ISLa and Fandango solve constraints over an untouched grammar. All
> of them get valid programs, and none of them keeps a systematic coverage
> criterion over the valid ones. The closest precedent is
> [Harm and Lämmel's two-dimensional approximation coverage](https://www.informatica.si/index.php/informatica/issue/view/96/84),
> from 2000, which says outright that some targets become infeasible and leaves
> them to the user.

### Attempt two: only what can actually happen

The fix came from an unexpected place: train timetables.
[RAPTOR](https://doi.org/10.1287/trsc.2014.0534), the round based public transit
router, makes a point that maps onto our problem exactly. The time expanded
graph of a transit network is far too big to build, so RAPTOR never builds it.
It works in rounds over the timetable itself, and in each round it only rescans
the routes through stops that improved in the last one.

The grammar version of "cheapest route" is older still.
[Knuth's grammar problem](<https://doi.org/10.1016/0020-0190(77)90002-3>) (1977)
generalises Dijkstra to grammars: the cheapest derivation of every nonterminal.
Purdom's first pass is exactly this, with cost being size.

Put together, the context engine looks like this:

- A **label** summarises a subtree: what it needs from outside (references),
  what it binds, and its type. Only synthesized information, nothing inherited,
  so a subtree's label does not depend on where it ends up.
- Variables are **slots, not names**. Labels are kept up to renaming, so
  `MATCH (a) RETURN a` and `MATCH (b) RETURN b` are the same label. Names are
  handed out at the very end. This is the idea behind data independence
  ([Wolper, 1986](https://doi.org/10.1145/512644.512661)): a program that only
  compares values for equality behaves the same under any renaming.
- Labels are computed bottom up in **rounds**, each round rescanning only
  productions whose children gained a label (semi-naive evaluation, or RAPTOR's
  marking).
- A production is scanned **left to right**, like a RAPTOR route: a binding from
  an earlier child discharges a requirement of a later one, and combinations
  that can never work are dropped on the spot.
- Labels that differ in ways no ancestor will ever look at are **joined** into
  one, the way tabled logic programming does answer subsumption
  ([Swift and Warren](https://doi.org/10.1007/978-3-642-15675-5_26)). Extraction
  later makes them concrete again.

Then, per coverage target, we walk back down and extract the smallest valid tree
that contains it.

The difference is not subtle. At two variables the typed run went from 526
seconds to 19. At three it went from never finishing to about two and a half
minutes on a single machine. Along the way, making it faster flushed out three
bugs where the engine said "no valid tree exists" for a target that had one,
which is the worst kind of bug for a tool whose whole pitch is honest reporting.

## Step 6: how many variables is enough?

Capping the number of variables makes everything finite, but it raises the
obvious question: what does a bigger cap find that a smaller one does not?

Testing theory has a name for "we tested up to size n and assume that's enough".
[Bernot, Gaudel and Marre](https://doi.org/10.1049/sej.1991.0040) call it the
**regularity hypothesis**, and in their framework it is an assumption you choose
from knowledge of the program.

Here it can be more than an assumption. Because labels only compare variables
for being the same one, two variables a rule does not force apart can be merged
into one without changing which grammar rules a tree uses. Fold enough and the
only variables left are ones the standard says must be distinct, and those come
in lists (`RETURN a, b, c`). Counting how many such variables a list needs at
its widest point gives a cutoff: 3 variables are enough to cover every
production, 4 to cover every production in every context. This is the same shape
as cutoffs in model checking, where a register automaton with k registers is
nonempty iff it accepts a word over k + 1 values
([Kaminski and Francez](<https://doi.org/10.1016/0304-3975(94)90242-9>)).

And then we measured one past the bound, because a theorem is only as good as
its assumptions. It caught one we had missed: a `YIELD` list costs two slots per
item, not one. The theorem now counts slots per item.

## Step 7: never is an answer

Some targets cannot be covered by any valid query. A production that only exists
to spell something a syntax rule then forbids, for example. For a fuzzer those
are invisible. For a tool whose job is to say "this much of the standard", they
are the most important line in the report.

So every target ends up in one of three states, a shape borrowed from code
coverage
([Bardin et al., ICST 2015](https://doi.org/10.1109/ICST.2015.7102607)):
**covered**, **proven infeasible** (no valid tree exists, and the labels say
why), or **unknown**. At three variables, with hydradb's claim, that is 4,399 of
4,540 productions covered and 141 never, and an audit at two variables had
predicted exactly those counts before the three variable run ever finished.

## Step 8: trust nothing, check everything twice

A generator bug is dangerous here. If we generate an invalid query and the
engine rejects it, it shows up as a failure for the engine. That is the fastest
way to lose the trust of the people whose engine you are testing.

So every query goes through a **second checker**, written separately from the
generator, that re-reads the query against the grammar and the syntax rules,
straight from the rule text. Nothing goes out that it refuses, and a test keeps
the two in agreement. It is the same instinct as N-version programming, and the
same instinct behind [JEST](https://doi.org/10.1109/ICSE43902.2021.00015), which
runs JavaScript engines against a mechanised spec and blames whichever side
disagrees, the spec included.

It pays off in both directions. Running the generated set against hydradb has
found queries that hydradb refused rightly, because the generator broke a rule
we had not modelled yet. Each of those became a rule, not a patch.

## Step 9: the right answer, not just an answer

Accepting a query is not the same as answering it correctly. The latest stage
gives every query a graph to run on and the answer it must produce there.

The graph comes from the query itself. The generator already knows, for every
variable, whether it is a node, an edge or a path, and what type it has. A
**witness graph** is built from the query's patterns so that a known row has to
come back. This is
[reverse query processing](https://doi.org/10.1109/ICDE.2007.367896) (Binnig,
Kossmann and Lo) for graph patterns: start from the result you want and build
the database that produces it.

The answer comes from a **reference evaluator** written from the standard's
general rules, the part of the text that says what a query means. It is slow and
literal on purpose. The method follows
[Guagliardo and Libkin's formal semantics of SQL](https://doi.org/10.14778/3151113.3151116):
write the semantics executably, run it against real engines, and use the
standard to settle every disagreement.

Run against hydradb, this found bugs no amount of "does it parse" testing would
have. A quantified `?` that dropped its one iteration case, so `( <- ? )` did
not mean `{0,1}`. A multiset alternation `|+|` counted as a union with a
remainder. `SUM(NULL)` answering 0 where the standard says null. Each one was
checked by hand against the text and on a three node graph before it was called
a bug.

## Step 10: saying exactly what the claim rests on

All of this adds up to a claim, and a claim is only as strong as what it rests
on. We write it the way Bernot, Gaudel and Marre frame testing
([and Gaudel and Le Gall revisit](https://arxiv.org/abs/0804.0970)): passing an
exhaustive test set is equivalent to correctness, and every step down from
exhaustive is a stated **hypothesis**. The variable bound is enough. The witness
graphs are representative. The engine's answers are observable as tables and
status codes. Each hypothesis is marked as proven, built in by construction, or
assumed, and the assumed ones are listed.

That is the end goal: per feature an engine claims, evidence that every
construct the standard defines for it is used by some valid query, and the
engine answers each one right, with the right rows or the right error, plus an
honest list of what we could not reach.

---

## Where this leaves hydradb

Running this against our own engine was humbling in a useful way. On the first
typed set, hydradb accepted 52% of the queries. Some of the rest were our
generator's mistakes, which became rules. Some were hydradb's parse gaps and
planning gaps, which became fixes. Some were documented deviations, which is
fine, as long as they are documented. Today it accepts 73% of the three variable
set, and handles 89% of the valid queries that sit outside its documented
deviations.

The numbers matter less than the fact that every refusal has a cause attached,
and the list of causes comes from the standard, not from us.

## Why this matters beyond one engine

Nothing in gql-proof is specific to hydradb. Anything that accepts GQL text can
be tested with it, and it already runs against Neo4j too.

- **For engine developers**, it is a conformance yardstick you can run in CI and
  a list of exactly what is left, per feature.
- **For test suite authors**, `gql-proof cover` measures any suite of queries
  against the same targets. We measured an 11,500 query suite with it: 508
  productions our set reaches were never touched by it.
- **For the standard itself**, generating from the text finds places where the
  text is ambiguous or where the corrigendum changed a rule's meaning. Those
  readings are written down, one by one.
- **For other languages**, nothing here is specific to GQL either. Any language
  with a published grammar and conformance rules could be tested the same way.
  SQL/PGQ shares GQL's pattern language and is the obvious next candidate.

And it is complementary to what exists. A TCK checks answers we do not check
yet, and our queries are the coverage a TCK lacks.

## What we would love help with

I'm quite sure exposing this to the public will bring in some valuable scrutiny,
and that is exactly what it needs.

- **Our readings.** Where the standard can be read more than one way we picked a
  reading, and each one is written down. If you know the text, tell us where we
  read it wrong.
- **The cutoff argument.** That 3 variables are enough is a theorem with
  assumptions. Poke holes in it.
- **Engines.** Run it against yours. Every false failure is a rule we have not
  enforced yet, and every true one is a bug you would rather hear about from us
  than from a user.
- **The open parts.** A catalog (named graphs, graph types, procedures), data
  modification against a real engine, and the remaining syntax rules we do not
  model yet. Contributions very welcome.

The code is at [TODO-link](TODO-link).

Thank you for reading.

---

## References

Grammar coverage

- Paul Purdom. A sentence generator for testing parsers. BIT 12(3), 1972.
  https://doi.org/10.1007/BF01932308
- Lixiao Zheng, Duanyi Wu. A sentence generation algorithm for testing grammars.
  COMPSAC 2009. https://doi.org/10.1109/COMPSAC.2009.193
- Zhiwu Xu, Lixiao Zheng, Haiming Chen. A toolkit for generating sentences from
  context-free grammars. SEFM 2010. https://doi.org/10.1109/SEFM.2010.21
- Ralf Lämmel. Grammar testing. FASE 2001.
  https://doi.org/10.1007/3-540-45314-8_15
- Nikolas Havrikov, Andreas Zeller. Systematically covering input structure.
  ASE 2019. https://doi.org/10.1109/ASE.2019.00027
- Nikolas Havrikov, Alexander Kampmann, Andreas Zeller. From input coverage to
  code coverage: systematically covering input structure with k-paths. Preprint.
  https://publications.cispa.saarland/3572/1/tosem-codeine-arxiv.pdf
- Mark Hennessy, James F. Power. Analysing the effectiveness of rule-coverage as
  a reduction criterion for test suites of grammar-based software. Empirical
  Software Engineering 13(4), 2008. https://doi.org/10.1007/s10664-008-9067-7

Syntax rules, features and negatives

- J. W. Thatcher. Characterizing derivation trees of context-free grammars
  through a generalization of finite automata theory. JCSS 1(4), 1967.
  https://doi.org/10.1016/S0022-0000(67)80022-9
- H. Comon et al. Tree Automata Techniques and Applications. 2008.
  https://inria.hal.science/hal-03367725
- Christian Kästner, Sven Apel, Salvador Trujillo, Martin Kuhlemann, Don Batory.
  Guaranteeing syntactic correctness for all product line variants: a
  language-independent approach. TOOLS Europe 2009.
  https://doi.org/10.1007/978-3-642-02571-6_11

Valid programs and context

- William Hatch, Pierce Darragh, Sorawee Porncharoenwase, Guy Watson, Eric Eide.
  Generating conforming programs with Xsmith. GPCE 2023.
  https://doi.org/10.1145/3624007.3624056
- Rahul Gopinath, Hamed Nemati, Andreas Zeller. Input algebras. ICSE 2021.
  https://doi.org/10.1109/ICSE43902.2021.00070
- Jörg Harm, Ralf Lämmel. Two-dimensional approximation coverage. Informatica
  24(3), 2000.
- Donald E. Knuth. A generalization of Dijkstra's algorithm. Information
  Processing Letters 6(1), 1977. https://doi.org/10.1016/0020-0190(77)90002-3
- Daniel Delling, Thomas Pajor, Renato F. Werneck. Round-based public transit
  routing. Transportation Science 49(3), 2015.
  https://doi.org/10.1287/trsc.2014.0534
- Terrance Swift, David S. Warren. Tabling with answer subsumption:
  implementation, applications and performance. JELIA 2010.
  https://doi.org/10.1007/978-3-642-15675-5_26
- Pierre Wolper. Expressing interesting properties of programs in propositional
  temporal logic. POPL 1986. https://doi.org/10.1145/512644.512661
- Michael Kaminski, Nissim Francez. Finite-memory automata. Theoretical Computer
  Science 134(2), 1994. https://doi.org/10.1016/0304-3975(94)90242-9
- Sébastien Bardin et al. Sound and quasi-complete detection of infeasible test
  requirements. ICST 2015. https://doi.org/10.1109/ICST.2015.7102607

Checking and answers

- Jihyeok Park, Seungmin An, Dongjun Youn, Gyeongwon Kim, Sukyoung Ryu. JEST:
  N+1-version differential testing of both JavaScript engines and specification.
  ICSE 2021. https://doi.org/10.1109/ICSE43902.2021.00015
- Carsten Binnig, Donald Kossmann, Eric Lo. Reverse query processing. ICDE 2007.
  https://doi.org/10.1109/ICDE.2007.367896
- Paolo Guagliardo, Leonid Libkin. A formal semantics of SQL queries, its
  validation, and applications. PVLDB 11(1), 2017.
  https://doi.org/10.14778/3151113.3151116

The claim

- Gilles Bernot, Marie-Claude Gaudel, Bruno Marre. Software testing based on
  formal specifications: a theory and a tool. Software Engineering Journal
  6(6), 1991. https://doi.org/10.1049/sej.1991.0040
- Marie-Claude Gaudel, Pascale Le Gall. Testing data types implementations from
  algebraic specifications. Formal Methods and Testing, 2008.
  https://doi.org/10.1007/978-3-540-78917-8_7
