# L-meta-5150 — Petersen edge function, tight by one gate

**Verdict: not proved, not refutable. Almost certainly true, optimum 16.**
Released to the desk as `missing_lemma`.

## The statement

For every vertex `v`, every `FanInTwo` circuit `C` and every `b : Bool`, if
`C.size + (if b then 1 else 0) ≤ 15` then some input `x` with `x v = false`
makes `(if b then !C.eval x else C.eval x)` disagree with the Petersen edge
function. That is: nothing of size ≤ 15 computes it on the subcube `x v = false`,
and nothing of size ≤ 14 computes its complement there.

## Where it sits

The parent is **already merged**: `lean/PEqualNP/Outside/R_meta_2371_418.lean`
proves "Petersen needs ≥ 18 gates" from three hypotheses, and its `hSmall` is
this step verbatim. So this is a leaf of a merged reduction, and the parent's
header comments are the best available guide to the intended proof.

## Two independent derivations of the floor, agreeing

Fixing `x v = false` reduces the function to the edge function of Petersen minus
a vertex: **9 vertices, 12 edges**, degrees `2,2,2,3,3,3,3,3,3`, independence
number 4, vertex cover number 5, and it stays triangle- and C4-free.

A star partition of `m` edges into `k` stars costs `m + k − 1` gates. Here the
smallest partition has `k = 5`, so the cost is `12 + 5 − 1 = 16`. `k = 4` is
impossible: it would need four pairwise non-adjacent degree-3 vertices, and the
largest independent set among the degree-3 vertices is only 3. In a triangle-free
C4-free graph every biclique is a star, so **every** two-level circuit is a union
of stars whose centres form a vertex cover, and the leaf-OR subexpressions of a
minimum star partition are pairwise disjoint, so nothing can be shared. Hence any
15-gate circuit must be genuinely non-two-level.

Both of these were computed twice, independently (once from the statement's edge
list directly, once by a worker from the reduced graph), with the same answer.

## Why there is no refutation

This mattered because two cuts in this branch were already off by one *in the
false direction* (`L-meta-2571` asked for 45 where 46 is needed, `L-meta-1979`
asked for 63 where 64 is needed), so a 15-gate circuit was a live possibility.

- Simulated annealing over the full `{AND, OR, NOT}` basis at 15 gates, 7 seeds,
  ~2 CPU-hours: never below **3 wrong rows out of 512**.
- **Calibrated against a formally verified optimum.** On Petersen minus two
  adjacent vertices (8 vertices, 10 edges), whose optimum of 13 is already
  verified upstream (`L_meta_1908`, `L_meta_4552`), the same annealer reaches
  cost 0 at 13 gates in 12 s and plateaus at **exactly cost 3** at 12 gates —
  the identical signature to this function at 15. That is what makes the
  negative result credible rather than merely unsuccessful.
- Calibrated for reach too: the same function minus one edge has star cost 15,
  and the annealer found a verified 15-gate circuit for it in 85 s. So failing
  at 12 edges is not a limitation of the search.
- Negation probe: spending a gate on a pre-negated input leaves ≥ 6 wrong rows
  for every vertex tried. Every optimum found was monotone.
- Upper bound confirmed: an explicit 16-gate monotone circuit (star centres
  1,2,4,5,8) matches on all 512 rows.

Exact-synthesis SAT did not terminate at this scale in 20+ minutes, so there is
no machine-checkable UNSAT certificate. The encoder was validated separately: on
C5 it returns UNSAT at 5 and 6 gates and SAT at 7, which is the star bound.

## Why it cannot be closed from here

The step is exactly **one gate** beyond what the repository already has. Upstream
proves `¬ HasCircuitSize 9 target 14`, i.e. ≥ 15 for this very 9-vertex function
(internal theorems in `L_meta_2010.lean`, `L_meta_3841.lean`); this step needs
≥ 16. A submitted file may import only `Mathlib` and `PEqualNP.Defs`, so none of
that can be cited — it would have to be reproved, and the new level is the hard
part.

## Recommended cut, in the shape of the merged parent

1. **Reduction.** A 10-input circuit correct on the subcube `x v = false` yields
   a 9-input circuit of no greater size for the Petersen−v edge function.
   `L_meta_4439.lean` already has reusable `wmap` / `relGate` / `relabel`.
2. **High fan-out.** If some input is read by ≥ 3 gates, the parent's `hElim`
   drops 3 gates, landing at ≤ 12 for Petersen−v−u (8 vertices, 10 edges), which
   contradicts the already-proved `¬ HasCircuitSize 8 … 12`. Note 15 − 2 = 13 is
   *not* a contradiction, so the ≥ 3 case is essential — two gates do not suffice.
3. **Low fan-out.** Every input read by ≤ 2 gates (≤ 3 when read negated) needs
   its own argument, exactly analogous to the parent's `hRest` one level up.
