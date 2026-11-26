#!/usr/bin/env python3
"""L-meta-19373: is a 1000-gate circuit reachable as a RECTANGLE COVER?

THE REDUCTION, which turns a blind search into an optimisation. On the one-a-side
promise exactly one x and one y are set, so for any row set S the wire
`OR of x_u for u in S` says whether the live row is in S, and likewise for
columns. Hence for ANY family of all-1 rectangles S_k x T_k covering every
1-entry of A,

    f = OR over k of ( (OR of x_u, u in S_k) AND (OR of y_v, v in T_k) )

is correct on every promise input: the live cell (u,v) is a 1 exactly when some
rectangle contains it, and no rectangle contains a 0 cell. Its size is

    sum over k of ( |S_k| - 1 + |T_k| - 1 + 1 )  +  (K - 1)
      = sum over k of ( |S_k| + |T_k| ) - 1.

So the posted budget of 1000 gates is exactly a cover of total weight 1001, and
the question is combinatorial rather than a circuit search. The desk holds 1001
and asks for one less, which is consistent with its own construction being a
cover of weight 1002.

WHAT THIS SCRIPT ANSWERS. Only whether the neighbourhood is reachable at all. A
greedy cover that lands near 1001 means the row is worth real optimisation
effort; one that lands at three thousand means it is not. The theory says the
minimum weight for a dense random matrix is of order n^2 / log n, about 1170
here, so 1000 sits just below the generic value - which is what makes the row
interesting and also what makes it hard.

The greedy is max-ratio: repeatedly take an all-1 rectangle maximising
(new cells covered) / (|S| + |T|). Finding the best such rectangle is itself
NP-hard, so candidates are generated from row-neighbourhood intersections, which
is the standard cheap source of maximal all-1 rectangles.
"""

from __future__ import annotations

import json
import pathlib
import re
import sys
from typing import Final

STEP: Final = pathlib.Path(
    "/home/user/pequalnp-proofs/tools/pnp-harness/steps/L-meta-19373.json"
)
N: Final = 128


def matrix() -> list[int]:
    """Row u as a 128-bit mask, from the step's own statement."""
    stmt = str(json.load(open(STEP))["gap"]["statement"])
    rows = [int(h, 16) for h in re.findall(r"0x([0-9a-fA-F]+)", stmt)]
    if len(rows) != N:
        sys.stderr.write(f"expected {N} rows, found {len(rows)}\n")
    return rows


def popcount(x: int) -> int:
    return bin(x).count("1")


def best_rectangle(rows: list[int], todo: list[int]) -> tuple[int, int, float]:
    """(rowset-as-mask, colset-as-mask, ratio) maximising new cells per unit weight."""
    best = (0, 0, 0.0)
    for u in range(N):
        if not todo[u]:
            continue
        # Candidate column sets: u's own neighbourhood, and its intersection with
        # each other row's. Those are the cores of the maximal all-1 rectangles
        # that contain u.
        cands = {rows[u]}
        for w in range(N):
            if w != u:
                inter = rows[u] & rows[w]
                if inter:
                    cands.add(inter)
        for t in cands:
            tsize = popcount(t)
            if tsize == 0:
                continue
            # S = every row whose neighbourhood contains T. Then S x T is all-1.
            s = 0
            ssize = 0
            for w in range(N):
                if rows[w] & t == t:
                    s |= 1 << w
                    ssize += 1
            if ssize == 0:
                continue
            new = sum(popcount(todo[w] & t) for w in range(N) if s >> w & 1)
            if new == 0:
                continue
            ratio = new / (ssize + tsize)
            if ratio > best[2]:
                best = (s, t, ratio)
    return best


def main() -> int:
    rows = matrix()
    edges = sum(popcount(r) for r in rows)
    sys.stdout.write(f"128x128, {edges} one-entries, density {edges / (N * N):.3f}\n")
    sys.stdout.write(f"  naive one-rectangle-per-edge weight: {2 * edges} -> {2 * edges - 1} gates\n")
    sys.stdout.write(f"  star cover (one rectangle per row): {edges + N} -> {edges + N - 1} gates\n")
    sys.stdout.write("  POSTED BUDGET 1000 gates = a cover of total weight 1001\n\n")

    todo = list(rows)
    weight = 0
    k = 0
    while any(todo):
        s, t, ratio = best_rectangle(rows, todo)
        if s == 0:
            sys.stdout.write("  greedy stalled with cells uncovered - bug or degenerate input\n")
            return 1
        ssize, tsize = popcount(s), popcount(t)
        weight += ssize + tsize
        k += 1
        for w in range(N):
            if s >> w & 1:
                todo[w] &= ~t
        left = sum(popcount(x) for x in todo)
        if k <= 12 or k % 25 == 0:
            sys.stdout.write(
                f"  rect {k:>4}: {ssize:>3} x {tsize:<3} ratio {ratio:5.2f}"
                f"  weight so far {weight:>5}  cells left {left}\n"
            )
    sys.stdout.write(
        f"\n  GREEDY COVER: {k} rectangles, total weight {weight}"
        f" -> circuit of {weight - 1} gates\n"
        f"  posted budget is 1000 gates (weight 1001), so this is"
        f" {'WITHIN' if weight - 1 <= 1000 else 'OVER by ' + str(weight - 1 - 1000)}\n"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
