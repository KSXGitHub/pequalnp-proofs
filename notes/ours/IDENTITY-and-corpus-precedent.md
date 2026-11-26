# Two results from the 1498-point row we did not win

L-meta-9747 asked for a 22-gate AND/OR/NOT circuit for an 18-edge bipartite C4-free graph whose
star cover costs exactly 23. We did not find one and we did NOT exhaust the space - no 22-gate UNSAT
was obtained, and the positive control (monotone, 23 gates, known solution, on the 48
minterm-plus-maxterm rows that are exactly equivalent to all 8192 in the monotone model) DID NOT
RETURN in 500 s. So the verdict is `statement_seems_false`: a calibrated negative, not a proof.
What came out of it is worth more than the row.

## 1. An identity that prices a NOT gate, and restates the project's stuck lemma

For any MINIMUM-SIZE `FanInTwo` circuit computing a non-constant function - so every gate is useful
and non-degenerate, fan-in is exactly 2 for AND and OR and 1 for NOT, and no gate reads the output:

    size + 1 = m + s + u

where `m` counts INPUT-WIRE READS, `u` the NOT GATES, and `s` the SHARING, namely the sum of
(outdeg - 1) over non-output gates.

Proof in one line: summing fan-in two ways gives 2b + u = m + sum of outdeg = m + (b + u - 1) + s.
Checked on ten circuits (both covers of four test graphs plus solver-found witnesses); for every
cost-optimal one, m + s + u = |E| + tau exactly.

*** CONSEQUENCE: A NOT GATE COSTS EXACTLY ONE UNIT OF THE SAME BUDGET AS A VARIABLE READ. ***
Negation is a COST in this model, not a discount. And under C4-freeness two stars meet in at most
one point, so a shared wire saves at most one read while the sharing itself costs one unit of `s` -
break-even at best, and a negation inside it adds another unit. Measured independently: NO
minimum-size circuit in this family contains a negation at all (at the exact optimum, hex with one
NOT and with two NOTs are both UNSAT, and twoline with one NOT is UNSAT).

*** AND IT RESTATES `starCoverOfCircuit`, THE LEMMA THAT HAS BLOCKED EVERYTHING, IN A FORM THAT
NEEDS NO GATE-BY-GATE BICLIQUE EXTRACTION AND APPLIES VERBATIM WITH NEGATIONS: *** the whole bound
becomes the single inequality `m_x + m_y >= |E| + tau`. The natural tool is a sensitive-path
argument - for each edge (p, i), flipping x_p at the row e_p + e_i changes the output, so some read
of x_p begins an all-sensitive path - and that argument is valid in the AND/OR/NOT model. The
remaining content is the injectivity/trade-off between the two sides, which cannot hold on both at
once (the line-star cover collapses the y-reads), so it is a genuine LP-style trade-off and not a
one-line argument. That is the sharpest reformulation of the wall we have.

## 2. The corpus has already decided every row of this shape - seven times out of seven

A scan of all 10610 files in `lean/PEqualNP/Outside/` for UNCONDITIONAL top-level `HasCircuitSize`
rows on bipartite edge functions, computing each graph's |E|, tau, C4-freeness and floor:

| file | proves | n | \|E\| | tau | floor | posted | diff | C4-free |
|---|---|---|---|---|---|---|---|---|
| L_meta_9752 | FALSE | 12 | 15 | 5 | 19 | 18 | -1 | yes |
| L_meta_9818 | FALSE | 10 | 13 | 5 | 17 | 16 | -1 | yes |
| L_meta_9825 | FALSE | 10 | 13 | 5 | 17 | 16 | -1 | yes |
| L_meta_670 | FALSE | 9 | 12 | 5 | 16 | 15 | -1 | yes |
| L_meta_1007 | FALSE | 8 | 10 | 4 | 13 | 12 | -1 | yes |
| L_meta_1664 | FALSE | 8 | 9 | 4 | 12 | 11 | -1 | yes |
| L_meta_1004 | FALSE | 6 | 7 | 4 | 10 | 9 | -1 | yes |
| L_meta_1001 | TRUE | 9 | 12 | 5 | 16 | 16 | 0 | yes |
| L_meta_1003 | TRUE | 8 | 10 | 4 | 13 | 13 | 0 | yes |
| L_meta_16082 | TRUE | 7 | 12 | 4 | 15 | 13 | -2 | **NO** |

*** SEVEN OF SEVEN C4-FREE ROWS POSTED AT FLOOR MINUS ONE ARE PROVED FALSE IN THE FULL AND/OR/NOT
MODEL. NOT ONE C4-FREE BELOW-FLOOR ROW IS TRUE. *** The single below-floor TRUE row is NOT C4-free,
so the floor formula does not apply to it - the exception that proves the rule. (One apparent
counterexample, `R_meta_6030_2`, carries the claim as a HYPOTHESIS and not as its conclusion.)
Spot-checked independently: 9752 and 1004 do prove negations, 16082 does prove a positive.
This is now wired into `tools/pnp-harness/floor.py`, which cites the precedent whenever a C4-free row
sits one below its floor and says to release it `statement_seems_false` rather than spend a worker.

## 3. Why this particular row is out of reach of the existing proof technique

The corpus's certificate machinery for these negations - `Live`-set column reachability with free
inversions, split into monotone and signed roots - tops out near n = 11 and 17 gates in
`L_meta_9752`'s core, and its reduction chain peels DEGREE-1 vertices to drop (n, budget) by (1, 1).
Our graph has MINIMUM DEGREE 2, so one pin drops the floor by 2 while the budget drops by 1 and the
slack is lost. That is exactly why this row, and L-meta-9754 (the full Fano at n = 14), are beyond
the technique, and why `statement_seems_false` is the honest release rather than `missing_lemma`.

Incidental structure, verified: the graph is the FANO PLANE INCIDENCE MINUS ONE LINE, the missing
line being {1,2,4} - precisely the three degree-2 points. The minimum vertex cover is UNIQUE (the
six lines), and over all 2^18 ways to assign each edge to an endpoint EXACTLY ONE star partition
costs 23 while the next best costs 24 (38 ways) - so no gate hides in a point-style treatment of the
degree-2 vertices. f is non-degenerate at all 78 variable pairs. The 23-gate cover is exact on all
8192 rows, so if the desk ever posts the FLOOR-level row for this graph it closes in seconds.
