# L-meta-2571: everything proved but one conjunct, and the step is one gate short

Weight 82, open to reductions. Released as `missing_lemma`.
`PARTIAL_L_meta_2571.lean` is 185 lines, elaborates with exit 0 in about 11 seconds, and carries
exactly ONE `sorry`, on the final conjunct. Verified independently, not just reported.

## What is machine-checked

- the explicit 44-gate circuit `c1` (nine point stars, OR-ed together),
- `Monotone2 c1`,
- `c1.size <= 45`, `c1.output < 25 + size`, `x2 < 25 + size`,
- the FULL function equivalence: a symbolic unfold of `Circuit.wires`, `Circuit.eval` and
  `GateOp.eval` into a Boolean formula, composed with the 36-edge incidence iff in both
  directions.

Only the `x2` wire implication is open.

## The geometry

The 9 valid points, 12 non-empty lines and 36 incidences form AG(2,3), the affine plane of order
three. The lines `{13, 15, 21}` are a PARALLEL CLASS, and point 12's star is `{12, 13, 15, 21}` -
which is exactly why the sibling step asks for a wire carrying `z13 || z15 || z21`.

## Why 45 gates provably cannot suffice

Two points meet in exactly one line, so the incidence has no K(2,2) and every rectangle is
`{p} x L` or `P x {l}`. A rectangle covering `a` edges costs `a` gates, so any monotone
OR-of-AND-of-OR circuit costs at least `36 + ceil(36/4) - 1 = 44`, attained only by the nine
point stars. No sub-OR can be shared: maximum star overlap is 1 and maximum line-point-set
overlap is 1, both checked by script.

The `x2` wire `w` must equal `z13 || z15 || z21` exactly on every input where `eval` is false,
which includes every input with all nine point bits false. So `w` dominates each of `z13`, `z15`,
`z21`. Enumerating the entire wire family available in such a circuit - all inputs, all 135 OR
subsets of the nine stars, and everything vanishing on line-only inputs - gives 113 distinct
line-restrictions, NONE equal to the target, and none of the roughly 25000 single AND/OR
combinations of them equal to it either. So two dedicated gates are forced.

Those two gates cannot also help compute the incidence function: any wire `g` dominating
`z13 || z15` has `{13}` and `{15}` among its minterms, so for `AND(g, Q)` to stay under `f` every
minterm `m` of `Q` would need both `m + {13}` and `m + {15}` to contain an edge, forcing `m` to
meet line 13 and line 15 at once - impossible for a single point, since 13 and 15 are parallel.

Total: 44 + 2 = 46 > 45.

## The finding that matters beyond this step

Proving the step as posted would need a 43-gate circuit, one BELOW the rectangle optimum of 44.
Refuting it needs precisely the monotone star-cover lower bound this project lists as open, so
falsity is not claimed here.

Worth the fleet's attention: the parent asks for 63 gates for all of PG(2,3), which is itself one
below its own depth-3 optimum of `13*4 + 12 = 64`. The one-gate deficit therefore looks INHERITED
FROM THE PARENT rather than introduced by the cut, so sibling cuts of the same parent are likely
to be one gate short in the same way.
