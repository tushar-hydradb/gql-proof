# the day the checker caught the rule

> for agents: dated working notes, terse on purpose. people start at the [readme](../README.md)

a short account of one bug, kept because it shows why the pipeline has two
readings of the standard and what each is for. the engine is
`src/context.rs`, the types rule `src/context/types.rs`, the independent
checker `src/verify/types.rs`

## what happened

the first full typed extraction from a joined fixed point (one variable,
`gql-proof context --rule types --slots 1 --join --keys --phase cover
--cdrc`) produced 1,288 sentences. 25 of them failed the types checker.
every one had the same shape: a variable bound as a node or an edge by a
pattern, then used as the source of a TRIM, which needs a string

```
START TRANSACTION USE CURRENT_PROPERTY_GRAPH
INSERT ( x )
DELETE CURRENT_DATE , ELEMENT_ID ( x ) , x ,
       GRAPH CAST ( NULLIF ( NULL ,
                             CHAR_LENGTH ( TRIM ( SESSION_USER FROM x ) ) )
                    AS EDGE ) . a

<trim function> > <single-character trim function> > <trim operands>
  > <trim source>: 20.23 SR 2, 4: x has type NODE, not Char or Bytes
```

the first question was whether extraction had combined children that do not
fit together. it had not: the typed rule itself, rerun over the named tree
(`context::accepts`), accepted all 25. the rule was wrong, the checker was
right, and the sentence was the evidence

## why the rule missed it

the rule is a synthesized automaton: a node's label depends on its
production and its children's labels, never on anything above it. so when
`TRIM ( SESSION_USER FROM x )` is labelled, nothing knows what `x` is. the
rule copes by deferring: a bare reference carries its class undecided
(`Ty::Slot`), every site it passes narrows the set of classes it may still
have (the string site under TRIM leaves {str}), and whichever node finally
drops the deferred class is meant to write what is left as a need on the
variable, for the binder to check many nodes later

only the branch that chooses a class did that. `trim operands` has two
classed children, the trim character and the trim source, and no arm of its
own; its class is "none", so it took the other branch, and the {str} mask
evaporated. `x` left TRIM with no need at all, and the node binder it met
later had nothing to contradict. from the rule's own point of view nothing
was wrong: the label it handed up was one it could have made

the fix is general: in `finish_node`, a deferred class a node does not pass
upward now turns the sites' mask into a need (`meet(vars[s], Allow(m))`),
because the reference went through those sites and its variable must be one
of the classes they let through, whatever else is chosen. plus an arm for
`trim operands` (20.23 SR 2, 4; 20.24 SR 3). after it: 1,288 trees, 0
failures, and a fixed point a few hundred labels smaller

## why the checker saw it

`verify::types` answers the same question from the other direction. it walks
the finished tree with an environment in hand: the types that patterns and
statements bind are threaded through the sentence (16.3, 14.7, 14.8, 14.10,
9.2, 15.1), so by the trim source it knows `x` is a node. it computes each
expression's type bottom up from its own operator and operands, and applies
the standard's requirement at the site directly: the trim source demands
Char or Bytes, citing 20.23 SR 2, 4. the demand and the fact meet in one
place; there is nothing to carry and nothing to forget

two properties make it a judge rather than a second opinion. it is written
separately from the rule, straight from the ISO text, and shares no code with
the automaton, so a shortcut taken in one is not mirrored in the other. and
it takes a type from the operator, never from the grammar category a parse
put the expression in: `x` derives as a numeric primary, a string primary and
a node reference alike, and the rule's deferred classes exist to navigate
that ambiguity; the checker's verdict is the same on every parse tree of a
sentence

## why it surfaced now

the probes and the generated-tree test had never reached this shape, and the
extraction without joins did not either: its smallest witnesses routed
around it. joins change which witness is smallest, and the first joined run
walked straight into it. a different search order over the same exact fixed
point is, in effect, a different test generator, and the checker is the part
of the pipeline that does not care which one produced the sentence

## what each half is for

the rule decides validity for every tree at once, before any tree exists:
that is the proof, and nothing else can do it. the checker cannot prove
anything in advance, but it audits every witness the proof produces against
the standard with the whole sentence in view. when they disagree the
sentence is the evidence and the standard is the referee. nothing is printed
unless both agree, which is the whole reason a rule written to be sound but
only tested can be trusted at all
