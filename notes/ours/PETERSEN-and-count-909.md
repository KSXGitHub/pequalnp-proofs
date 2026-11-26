# The AND-count row on Petersen: what is settled, what is not

L-meta-909 asked for an `AndCount.AndCountCircuit` of **at most 6 AND gates** recognising
the maximal independent sets of the Petersen graph, under a read bound of 2 per vertex.
The row closed as `not_open` before we finished it - checked by someone else, or stood
down by the fleet - so nothing here was claimed. The findings outlive the row, so they
are recorded rather than discarded.

## First: the model is not what a cover count measures

This is worth stating plainly because our own screening tool got it wrong and printed
`AT FLOOR - exactly constructible by a minimum cover, the best kind of target`, which
sent a worker after a target that was not there.

An `AndCountCircuit` is **not** a gate list over variables. Each AND gate has a left and
a right *side*, and a side is a pair: some variables, plus some **earlier gates**, which
it ORs in. Clause (c), the read bound, counts `leftVars` and `rightVars` **only**. So a
side may read as many earlier gates as it likes, at no cost. The object is a DAG with
unbounded free internal fan-in.

Two consequences:

* the star-cover count has no purchase on it, and `floor.py` now refuses to give these
  rows a verdict at all;
* `outVars` exists but is **forced empty**, since every vertex lies in some maximal
  independent set, where `eval` must be false.

A third simplification: `eval` is monotone, so the 115 constrained points collapse to
**85** - the 15 maximal sets, plus only the 70 *minimal* true points `T union {p}` for
`T` a maximal set of size 3. The 30 size-5 true points each contain one of the 70, so
checking them is redundant. Sound and complete, and it shrinks every search by a quarter.

## The graph facts, independently re-derived

3-regular, 15 edges, independence number 4, vertex cover number 6, exactly **15** maximal
independent sets (10 of size 3 and 5 of size 4), and exactly **5** minimum vertex covers.

## Three structural results, by exhaustive machine check

These are finite exhaustions over the whole domain, not Lean proofs. They are stated as
such. Each is checkable by `decide` in principle, and the first has a one-line reason
behind it as well.

1. **Every admissible gate on Petersen is a star.** A gate whose two sides are `L` and `R`
   is false on all 15 maximal independent sets exactly when `L` and `R` are disjoint and
   `L x R` is complete bipartite - verified over all 10^6 side pairs with no mismatch.
   Girth 5 forbids `K(2,2)`, so one side must be a single vertex: every such gate is a
   star `({t}, S)` with `S` inside the neighbourhood of `t`.

2. **A circuit with no gate reads needs at least 10 AND gates**, against a posted budget
   of 6. For each vertex `w`, the 10 maximal sets avoiding `w` cannot be covered by two
   or fewer gates unless one of them is `({w}, S)` with `|S| >= 2`, and such a gate has a
   unique centre; checked for all 10 choices of `w`. So **any 6-gate solution must use
   gate reads**, and in the sharper form: some gate must be true at some maximal
   independent set.

3. **The star route has no slack.** Ignoring the read bound entirely, the minimum number
   of star *output* gates is exactly 6, and the only centre sets that work are exactly
   the 5 minimum covers. So there is no room to spend a gate on a helper.

## The exhaustion, and where it stopped

Faithful encoding of `sideTrue` / `gateValFuel` / `eval` / `WellFormed` with clause (c)
by gate index. The tight variant adds three breaks, each sound because it maps any
solution to one of the same or smaller size, and every smaller size was run: every gate
reachable from the output; no identically-false side; left side no later than right in
lexicographic order.

| size | verdict | time |
|---|---|---|
| 1, 2, 3, 4 | UNSAT (tight) | 0.0 s, 0.0 s, 0.1 s, 8.6 s |
| 5 | UNSAT (tight) | 671.2 s |
| **6** | **did not return** | ~13 min loose, plus three shorter runs |
| 7 | SAT, verified | 381.5 s |
| 10 | SAT, hand-built, verified | - |

So **no circuit of size 5 or less exists**, by genuine exhaustion. **Size 6 is open.**
The size-6 runs reached about 3 million conflicts without a result; none of them is an
UNSAT and none may be reported as one.

## The 7-AND witness, now checked

The desk's own record carried a 7-gate circuit as *computed, not checked*. This one is
re-simulated independently of the solver that produced it: reads
`[2,2,2,2,2,1,2,2,2,2]`, all at most 2, and **zero violations across all 115 points**.

```
g0 = ({6})             and ({3})
g1 = ({2})             and ({9} or g0)
g2 = ({0,7,8})         and ({5})
g3 = ({1,4} or g2)     and ({0} or g0 or g1)
g4 = ({1} or g0 or g2) and ({4} or g1)
g5 = ({7} or g0 or g4) and ({2,9} or g1 or g2 or g3)
g6 = ({8} or g1..g5)   and ({3,6} or g2 or g3 or g5)
outVars = empty,  outGates = {g6}
```

Its shape is the honest measure of the difficulty: one output gate and deep sharing -
nothing star-like, nothing flat.

## A hunt that found nothing, and proves nothing

Restricting to pure products, `eval = OR_j AND_t OR(F_jt)`, every 6-gate shape came back
UNSAT - and so did every 7-gate shape. Since a 7-gate circuit demonstrably exists, that
restricted space is **provably incomplete**, so its UNSATs are evidence of nothing except
that sides must mix bare variables with gate reads. Recorded as a dead end, not as a
result. It is also the cleanest illustration of why a positive control at a size known to
be satisfiable is mandatory before any UNSAT is believed.

## If anyone finishes it

Size 6 under the tight encoding is the only thing left, and it wants hours. The
accelerant worth trying is cube-and-conquer over the 63 choices of `outGates` rather than
over the roughly 4400 orbits of gate 0, seeded with result 2 above - that some gate is
true at some maximal independent set. A gate-reordering symmetry break was deliberately
**not** added: together with the lexicographic break it is not obviously orbit-complete,
and a false UNSAT here would have been reported as `statement_seems_false`.
