# L-meta-1684 — the promise is looser than the function, which is the whole difficulty

**Released as `missing_lemma`.** Weight 5; the step's own sketch says "no proof is
expected here: propose a cut". What follows is the quantitative part of such a cut.

## The setting, made concrete

The plane is PG(2,3) presented by the perfect difference set `{0,1,3,9}` mod 13:
point `p` lies on line `w` iff `p - w ∈ {0,1,3,9}`. That gives **13 points, 13
lines, lines of size 4, and 52 incidences**, and it is C4-free (two points lie on
exactly one common line).

The step asks: no `Monotone2` circuit of size ≤ 63 can be
- **true** on each of the 52 "incident pair" inputs (exactly one point and one
  incident line set), and
- **false** on the maximal-false inputs induced by *degenerate* point-sets `P`
  (the input being `P` together with every line disjoint from `P`).

## The bound 64 is exactly the two-level floor

A star partition of `m` incidences into `k` stars costs `m + k - 1`. Every vertex
of the incidence structure has degree 4, so `k ≥ 52/4 = 13`, and `k = 13` is
achieved by centring a star at each line. Hence

    52 + 13 - 1 = 64

and because the structure is C4-free every biclique is a star, so **every two-level
monotone circuit costs at least 64**. That is precisely the claimed bound, with
nothing to spare — the same one-gate tightness this branch keeps producing.

## Why that does not settle it, which is the point worth passing on

`Monotone2` is not restricted to two levels, and more importantly **the promise is
strictly weaker than computing the incidence function.** Enumerating the step's own
degeneracy condition over all 8192 point-sets:

    degenerate point-sets P: 236
      by |P|: {0:1, 1:13, 2:78, 3:52, 6:78, 9:13, 13:1}
    distinct negative inputs: 236
    distinct positive inputs:  52
    positives dominated by a negative: 0   (so the promise is consistent)

The `|P| = 2` count is `C(13,2) = 78`, i.e. every pair, since two points are always
collinear; `|P| = 3` is `13 × C(4,3) = 52`, the collinear triples; `|P| = 9` is the
13 line-complements.

The incidence function `g` is the minimal monotone function that is 1 on the 52
positives, and it is 0 on all 236 negatives by construction, so `g` satisfies the
promise at cost 64. But `g`'s maximal-false inputs are indexed by *every* point-set
`P`, and only **236 of 8192** are constrained here. A circuit meeting the promise is
therefore free to output 1 on all the non-degenerate maximal-false inputs — it need
not compute `g` at all. So a sub-64 circuit is not excluded by the star-cover
argument, and any proof of ≥ 64 must exploit the degenerate family specifically.

Conversely, refuting the step means synthesising a ≤ 63-gate monotone circuit on 26
inputs meeting a 52-positive / 236-negative promise. The sketch's own warning
applies: not a session-sized search by plain SAT, with roughly eight times more time
per gate.

## The cut this suggests

1. The two-level case: a C4-free incidence forces every biclique to be a star, so a
   two-level circuit costs `m + k - 1 = 64`. This part is self-contained and does not
   need the promise at all.
2. The promise case: show that satisfying the 236 degenerate negatives already forces
   a circuit to separate all 52 positives from all 8192 maximal-false inputs — i.e.
   that the degenerate family is *saturating*. If true, the promise collapses to
   computing `g` and part 1 finishes the job. This is the lemma I do not have, and it
   is where the step's content actually lives.
