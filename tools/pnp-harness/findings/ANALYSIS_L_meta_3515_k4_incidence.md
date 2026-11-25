# L-meta-3515 — almost certainly false, and the failure mode is exactly one edge

**Verdict: no 14-gate circuit found, with a quantitative explanation for why.**
Released as `statement_seems_false`. This is strong evidence, not a proof: it rules
out nothing a priori about non-star monotone circuits, but every measurement agrees
and the search is calibrated.

## What was asked

Exhibit a circuit with `IsAO2 10 C`, all gates' `inputs.Nodup`, `C.size ≤ 14`,
computing the incidence function of a bipartite graph on 6 + 4 vertices.

That graph is the **edge-vertex incidence of K4**: 6 left vertices (the edges of
K4), 4 right vertices (its vertices), 12 incidences, every left vertex of degree 2
and every right vertex of degree 3. It is C4-free, since two edges of K4 share at
most one endpoint and two vertices lie on exactly one common edge.

## The arithmetic, exactly

A star partition of `m` edges into `k` stars costs `m + k - 1` gates: `m - k` OR
gates for the leaf-ORs, `k` ANDs, and `k - 1` ORs to combine.

- All 12 incidences: the smallest partition has `k = 4` (centre a star at each of
  the four K4 vertices, which are pairwise non-adjacent in the incidence graph and
  together cover everything), so the cost is `12 + 4 - 1 = **15**`.
- Any 11 of them: `k = 4` still, so `11 + 4 - 1 = **14**`. And this holds for
  *every* choice of dropped edge — all twelve come out at 14.

So the budget of 14 is exactly the price of an 11-edge star circuit, one short of
the function. A 14-gate solution would have to be genuinely non-two-level.

## What the search found, and why it is trustworthy

Rows were reduced by monotonicity: a monotone `g` equals `f` iff `g = 1` on every
minimal true point and `g = 0` on every maximal false point. `IsAO2` circuits are
AND/OR only, hence monotone, so 12 + 12 = **24 rows replace all 1024**. This is what
made the search feasible at all; exact SAT on the full table does not terminate.

**The reduction is verified, not merely argued.** The 15-gate circuit found from
only those 24 rows was then checked against the complete 1024-input table: 0
mismatches. A sufficient-looking argument became a checked fact.

**Calibration.** At 15 gates the annealer reaches 0 wrong rows in ~82 s on
independent seeds, and the result passes the full table and all the structural
conditions (fan-in exactly two, distinct inputs, reads-back). So the method can
solve this problem at the size where a solution is known to exist.

**At 14 gates, twelve seeds, ~10-11 million iterations each: never 0.** Every seed
plateaus at exactly **one** wrong row, and in every single case that row is a
MIN-TRUE point - an uncovered edge - never a maximal-false point:

    seed 11  wrong=1  row 6  (3,6) min-true        seed 1   wrong=2
    seed 12  wrong=1  row 10 (5,7) min-true        seed 4   wrong=2
    seed 13  wrong=1  row 2  (1,6) min-true
    seed 14  wrong=1  row 6  (3,6) min-true
    seed 15  wrong=1  row 2  (1,6) min-true
    seed 16  wrong=1  row 1  (0,7) min-true

The circuits found are therefore always **sound and never over-accepting**; they only
ever **under-cover, by exactly one edge**. That is precisely the signature the
arithmetic predicts: 14 gates buys an 11-edge star circuit, and the twelfth edge has
nowhere to go. The particular edge sacrificed varies with the seed, and every edge
observed is one the arithmetic says is droppable at cost 14 - as, by symmetry, all
twelve are.

Two independent measurements, the star-partition count and the annealing plateau,
agree on the same boundary and on the same failure mode.

## Reusable method

The monotonicity row reduction is the transferable part: for any `IsAO2` or
`Monotone2` synthesis step, replace the full truth table by the minimal-true and
maximal-false points. Here that was a 43x reduction and turned a hopeless instance
into a few seconds of annealing. Tools: `p3515/sa.py <gates> <seconds> <seed>`,
`p3515/emit.py <gates>` (full-table verification plus the Lean circuit literal).
