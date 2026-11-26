# The crown needs at most 3n + 2*sqrt(n) + O(n^(1/4)) gates, not 4n - 5

The crown on n a side (u joined to v exactly when u /= v) represented on the one-a-side promise.
Our earlier construction was 4n - 5, verified on every promise row for n = 2..9, and we had been
treating it as the truth. IT IS NOT OPTIMAL FOR ANY n >= 9.

## The reduction that organises everything

With `d_u = x_u or y_u` (n gates), the promise row (u, v) becomes the d-pattern `e_u + e_v`, which
has weight 1 exactly when u = v. So the crown is threshold-2 over the d's, and the weight-1 and
weight-2 patterns are the WHOLE specification, because monotonicity forces the rest. Writing `A(m)`
for the least Monotone2 size of threshold-2 on m variables:

    L(n) <= n + A(n)
    A(m) <= 2m - p - q + A(p) + A(q) + 1     for any p*q >= m
    A(2) = 1

The recurrence is the grid construction: place the m indices in a p x q grid, OR each row and each
column (2m - p - q gates), then `T_2(row ORs) or T_2(column ORs)` - two distinct indices differ in
their row or in their column.

| n | 9 | 11 | 12 | 16 | 20 | 25 | 36 | 64 | 100 |
|---|---|---|---|---|---|---|---|---|---|
| this bound | 30 | 38 | **41** | 55 | 69 | 86 | 123 | 215 | 330 |
| 4n - 5 | 31 | 39 | 43 | 59 | 75 | 95 | 139 | 251 | 395 |

*** ANY POSTED CROWN ROW WITH n >= 9 SHOULD BE RE-COSTED AGAINST THIS TABLE, not against 4n - 5. ***

## The n = 12 witness, Lean-checked

41 gates (5 ANDs, 36 ORs) for the 12 x 12 crown. Wires 0-11 are the left inputs, 12-23 the right,
gate j is wire 24 + j, output 64. Re-simulated independently on all 144 promise rows by two routines
(column algebra, and row-by-row in the Lean wire convention), and the Lean file type-checks:
`L_crown12_41gates.lean` here, CHECK_OK in 49 s.

    g0..g11:  or(u, 12+u) for u = 0..11                    -- the d's
    g12 or(24,25)  g13 or(26,27)  g14 or(36,37)            -- row ORs of a 3x4 grid
    g15 or(28,29)  g16 or(30,31)  g17 or(39,40)
    g18 or(32,33)  g19 or(34,35)  g20 or(42,43)
    g21 or(24,28)  g22 or(45,32)  g23 or(25,29)  g24 or(47,33)   -- column ORs
    g25 or(26,30)  g26 or(49,34)  g27 or(27,31)  g28 or(51,35)
    g29 or(38,41)  g30 and(38,41) g31 and(53,44) g32 or(54,55)   -- Thr2 of the 3 rows
    g33 or(46,48)  g34 and(46,48) g35 and(57,50) g36 or(58,59)
    g37 or(57,50)  g38 and(61,52) g39 or(60,62)                  -- Thr2 of the 4 columns
    g40 or(56,63)

NOTE: that file carries budget 41, so it is a PIPELINE TEST and not a proof of desk row L-meta-18264,
which asks for 40. lint.py refuses it on the statement, correctly.

## Exact values, and what decides the 40 row

L(4) = 11 is SETTLED: exact synthesis over the 16 promise rows, swept UPWARD, UNSAT at 8 three
independent ways (column-order break 12 s, no symmetry break 66 s, automorphism-orbit pin 2.9 s),
UNSAT at 9 twice (108 s, 52.8 s), UNSAT at 10 in 2479.9 s, SAT at 11. The earlier worker's two open
sizes are now genuine UNSATs rather than timeouts. And L(n) = n + A(n) wherever both are known -
n = 2, 3, 4 and 5 - so the reduction looks tight.
A(2) = 1, A(3) = 4, A(4) = 7, A(5) = 10 (UNSAT at 9 twice: 222 s and 34 s). A(6) is 12 or 13,
undecided at a 3000 s timeout.
*** 40 AT n = 12 HOLDS IFF A(12) <= 28. *** Our best is 29, reached by two independent routes (the
3 x 4 grid, and the stars of K6 minus a perfect matching). Closed sub-routes: the 3 x 4 grid's seven
part-ORs cannot be finished in 11 gates by any depth-three circuit, because an AND term `O_X and O_Y`
must vanish at every diagonal pattern, forcing X and Y both among the row values or both among the
column values, which splits into covers of K3 and K4 at psi(3) + psi(4) - 1 = 12; and the 3 x 3 grid
prefix at m = 9 cannot be finished in 8 more gates (UNSAT, 32 s) even letting them read every input
and prefix wire. Stochastic search plateaus at Hamming distance 3 from T_2 on 12 variables at 28
gates. Reading: the row is more likely FALSE than true, but that is judgement, not a result.
SHARD 2 OF THAT ROW CANNOT BE EXHAUSTED: measured UNSAT cost in this family on 8 inputs and 16 rows
is 12 s at 8 gates, 108 s at 9, 2480 s at 10 - about an order of magnitude per gate - and the shard
asks for 40 gates on 24 inputs and 144 rows. There is no structural escape either: the shard pins
the AND count to 7-10 while our best circuits use 5 and the 4n-5 ladder uses 11.

## A calibration warning that generalises to every search we run

*** TIGHT SYMMETRY BREAKING MAKES UNSAT REACHABLE AND MAKES SAT MUCH HARDER TO FIND. *** cadical
could not find the KNOWN 12-gate completion of the m = 12 grid prefix in 330 s with the `distinct`
and `order` options on, and found it in 16 s with `--no-order --no-distinct`. So: HUNT WITNESSES
LOOSE, PROVE UNSAT TIGHT, and never read a tight-option timeout as evidence of anything.
Also new and sound: an automorphism-orbit pin (pin gate 0 to one representative per orbit of input
pairs) is 4x faster than the column-order break on the crown and 6.6x on threshold-2.

Tools and the soundness arguments for each normal form and symmetry break:
$P/p18264/README.md, with mono.py, grid.py, edges.py, ornet.py, anneal.py, mklean.py
($P = /tmp/claude-0/-home-user-pequalnp-proofs/731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/pnp)
