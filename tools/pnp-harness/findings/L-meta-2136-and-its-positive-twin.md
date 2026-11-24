# L-meta-2136 is false, and its positive twin has a short proof

`L-meta-2136` asked for a circuit: some monotone fan-in-two AND/OR circuit with at most 3 gates
computing the edge function of the bipartite graph g2x3-3f (2 points, 3 lines, 6 edges). Its own
sketch records that it is the exact negation of another step on the desk, so a proof of it would
have been one explicit counterexample, and none is expected if the positive statement is true.

Released as `statement_seems_false`. The positive statement is true, and the argument is short
enough to be worth writing down, because the POSITIVE TWIN is still an open step on the desk.

## The function

    f z = (z 0 && z 2) || (z 0 && z 3) || (z 0 && z 4)
       || (z 1 && z 2) || (z 1 && z 3) || (z 1 && z 4)

which factors as

    f z = (z 0 || z 1) && (z 2 || z 3 || z 4)

`f` depends essentially on each of the five variables: flipping any one of them changes `f`
somewhere. For instance at `z = (1,0,1,0,0)` flipping `z 0` moves `f` from true to false, and at
`z = (1,0,0,0,0)` flipping `z 2` moves it from false to true; the pairs 0/1 and 2/3/4 are
symmetric, so one witness per orbit covers all five.

## Four gates suffice

    a = z 0 ||| z 1
    b = z 2 ||| z 3
    c = b ||| z 4
    d = a &&& c          -- output

Four fan-in-two gates, so the least size is at most 4.

## Three gates cannot

Count input slots. Three gates of fan-in at most two give 6 slots. For the output wire's value to
depend on all five variables, every variable must be read on some slot, and the reading gate must
be connected to the output.

Take the output gate. It reads two wires, each a variable or an earlier gate.
- If it reads two gates, those two gates together hold only 4 slots, which cannot carry 5
  variables.
- If it reads one gate and one variable, that gate must depend on the remaining 4 variables. It
  reads two wires: either two variables, giving 2, or one variable and the last gate, which then
  needs 3 variables in its 2 slots. Neither reaches 4.
- If it reads two variables, the output depends on at most 2.

So at most 4 distinct variables can reach the output through 3 gates, and `f` needs 5. Gates of
fan-in below two, repeated reads and dead gates only make this worse, so the bound is exact: the
least size is 4.

## Why this matters

The positive twin - no monotone fan-in-two AND/OR circuit with at most 3 gates computes this
edge function - is a true step with the proof above. If it is ever drawn from the desk, the work
is the formalisation only: carry `f`'s essential dependence on all five variables, then the slot
count. That is a genuine candidate for a checked proof rather than another honest hand-back, and
it is the first step of this family we have seen with a short argument.
