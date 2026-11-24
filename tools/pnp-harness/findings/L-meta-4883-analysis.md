# L-meta-4883: true, and exactly tight at 14

Released as `missing_lemma`. Recorded because the analysis is reusable, and because the step's
own hypotheses turn out to be the interesting part.

## The step

Fix the 10-element base list of `BitVec 24` values and one more value `x1` drawn from a fixed
24-element list, giving 11 generators. For any list `x3` where every entry is the bitwise AND or
OR of two earlier entries of `base ++ [x1] ++ (the part of x3 before it)`, if the target
`16773120 = 0xFFF000` occurs anywhere in `base ++ [x1] ++ x3`, then `14 <= x3.length`.

## Reformulation

AND and OR act coordinatewise, so every entry of the program is one fixed monotone Boolean
function applied coordinatewise to the 11 generators. Coordinate `c` carries the pattern
`X(c)` = the set of generators whose bit `c` is set. The target asks for a monotone `f` with
`f(X(c)) = 1` on the 12 high coordinates and `0` on the 12 low ones. So the step is a monotone
circuit-size lower bound for that function.

## What was established computationally

- The target is reachable for all 24 choices of `x1`: no high coordinate's pattern is contained
  in a low coordinate's pattern. So the hypotheses are satisfiable and no
  coordinate-implication invariant can prove the bound.
- Every minimal good term is a PAIR of generators, so `f` is an OR of ANDs of pairs, and the
  least number of pairs covering the 12 high rows is 10 or 11 for each of the 24 `x1`.
- The bound is TIGHT. For `x1 = 650134` this 14-gate circuit hits the target exactly, checked
  against the real values, with `g i` the `i`-th generator:

      t1 = g1 &&& (g6 ||| g9)
      t2 = g3 &&& (g8 ||| g10)
      t3 = g0 &&& (g4 ||| g5)
      t4 = g7 &&& (g2 ||| g5)
      t5 = g8 &&& (g5 ||| g6)
      t1 ||| t2 ||| t3 ||| t4 ||| t5 = 16773120

  5 OR gates, 5 AND gates, 4 joining ORs: 14.
- A branch-and-bound over OR-AND-OR circuits with shared OR subcircuits, complete for a 13-gate
  budget (cost = orGates + 2 * terms - 1 <= 13 forces terms <= 7, and 7 pairs cannot cover 12
  rows when the least pair cover is at least 10), found no 13-gate circuit for the `x1` values it
  reached. The search is slow and was not run to completion on all 24.

## Why no short proof exists

Because 14 is the exact optimum there is no slack, so every argument of the shape -- each AND or
OR step improves the quantity by at most one -- caps out below 14. Tried and capped: depth,
counting separated high/low coordinate pairs with `Sep(a op b)` contained in `Sep(a) ∪ Sep(b)`,
and the half-word projections, where each half needs only about 4 gates on its own. Deciding over
13-gate circuits is beyond 10^20 configurations, and `native_decide` is banned.

## Cuts worth posting

1. AND/OR straight-line program over a fixed `BitVec` basis becomes a monotone function applied
   coordinatewise, and then its prime implicants.
2. Every minimal good term here is a pair. This is a cheap `decide` over 55 pairs against 12 low
   rows, per `x1`.
3. A biclique-cover lower bound of 5 blocks, connected to `Defs/BicliqueBlockCost`.
4. The per-`x1` split, so each of the 24 values is a step of its own.

Nothing in `PEqualNP.Defs` mentions `BitVec`, so the existing `BicliqueBlockCost`, `SharedOr`,
`CrossAnd` and `EdgeOwnership` modules do not connect to this concrete form without step 1.
