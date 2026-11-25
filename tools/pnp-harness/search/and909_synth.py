#!/usr/bin/env python3
"""Find a 6-AND AndCountCircuit for L-meta-909, by exact SAT.

The step: for the Petersen graph, exhibit an AndCountCircuit over 10 vertices
with WellFormed, size <= 6, every vertex bare in at most 2 gates, and for every
MAXIMAL independent set I: eval I = false, while eval (insert w I) = true for
every w outside I. The desk notes a 7-AND circuit is known to work, so this asks
for one gate better, and it hands over the encoding: "per gate, per side,
selector bits for variables and earlier gates; gate values on the 115 defined
points (15 maximal sets, 100 one-points); output selectors over gates (output
variables are useless). Cardinality constraint: for each variable, at most 2
gates have it in either side's bare set."

The model (PEqualNP/Defs/AndCountCircuit.lean): each gate is an AND of two sides;
a side is true when one of its bare vertices lies in u, or one of the earlier
gates it reads is true. The output is an OR of bare vertices and gates. So ORs
are free and only the ANDs are counted - which is why 6 is a real constraint.

Being an exact solve, UNSAT at 6 would be a genuine proof that 6 is impossible,
not a failed search. That is worth more than an annealer here.

usage: synth.py [gates] [timeout-seconds]
"""

from __future__ import annotations

import itertools
import json
import pathlib
import sys
import time
from typing import Final

# pysat ships no type stubs, so mypy cannot see through these three imports.
from pysat.card import CardEnc, EncType  # type: ignore[import-untyped]
from pysat.formula import IDPool  # type: ignore[import-untyped]
from pysat.solvers import Cadical153  # type: ignore[import-untyped]

D: Final = pathlib.Path(__file__).resolve().parent
N: Final = 10
EDGES: Final = [
    (0, 1),
    (1, 2),
    (2, 3),
    (3, 4),
    (4, 0),
    (0, 5),
    (1, 6),
    (2, 7),
    (3, 8),
    (4, 9),
    (5, 7),
    (7, 9),
    (9, 6),
    (6, 8),
    (8, 5),
]
ADJ: Final[dict[int, set[int]]] = {v: set() for v in range(N)}
for _a, _b in EDGES:
    ADJ[_a].add(_b)
    ADJ[_b].add(_a)
BARE_CAP: Final = 2


def maximal_independent_sets() -> list[frozenset[int]]:
    out: list[frozenset[int]] = []
    for r in range(N + 1):
        for combo in itertools.combinations(range(N), r):
            s = set(combo)
            if any(b in ADJ[a] for a, b in itertools.combinations(combo, 2)):
                continue
            if all(ADJ[w] & s for w in range(N) if w not in s):
                out.append(frozenset(s))
    return out


def points() -> list[tuple[frozenset[int], bool]]:
    """The 115 defined points: each maximal set (false) and each +1 (true)."""
    pts: list[tuple[frozenset[int], bool]] = []
    for mis in maximal_independent_sets():
        pts.append((mis, False))
        for w in range(N):
            if w not in mis:
                pts.append((mis | {w}, True))
    return pts


def solve(ng: int, budget: float) -> dict[str, object] | None:
    pts = points()
    pool = IDPool()
    cls: list[list[int]] = []

    lv = {(i, v): int(pool.id(("lv", i, v))) for i in range(ng) for v in range(N)}
    rv = {(i, v): int(pool.id(("rv", i, v))) for i in range(ng) for v in range(N)}
    lg = {(i, j): int(pool.id(("lg", i, j))) for i in range(ng) for j in range(i)}
    rg = {(i, j): int(pool.id(("rg", i, j))) for i in range(ng) for j in range(i)}
    og = {i: int(pool.id(("og", i))) for i in range(ng)}
    ov = {v: int(pool.id(("ov", v))) for v in range(N)}

    # Each variable bare in at most BARE_CAP gates. `in either side's bare set`
    # counts a gate once, so introduce one marker per (gate, variable).
    for v in range(N):
        marks: list[int] = []
        for i in range(ng):
            m = int(pool.id(("mk", i, v)))
            cls += [[-lv[(i, v)], m], [-rv[(i, v)], m], [-m, lv[(i, v)], rv[(i, v)]]]
            marks.append(m)
        cls += CardEnc.atmost(lits=marks, bound=BARE_CAP, vpool=pool, encoding=EncType.seqcounter).clauses

    def side(
        tag: str,
        i: int,
        p: int,
        u: frozenset[int],
        var: dict[tuple[int, int], int],
        gate: dict[tuple[int, int], int],
        gval: dict[tuple[int, int], int],
    ) -> int:
        """One side of gate i at point p: an OR of selected bare vars in U and
        selected earlier gates that are true."""
        s = int(pool.id((tag, i, p)))
        terms: list[int] = [var[(i, v)] for v in sorted(u)]
        aux: list[int] = []
        for j in range(i):
            a = int(pool.id((tag + "a", i, j, p)))
            cls.extend([[-a, gate[(i, j)]], [-a, gval[(j, p)]], [a, -gate[(i, j)], -gval[(j, p)]]])
            aux.append(a)
        lits = terms + aux
        if not lits:
            cls.append([-s])
            return s
        cls.append([-s, *lits])
        cls.extend([[s, -x] for x in lits])
        return s

    gval = {(i, p): int(pool.id(("g", i, p))) for i in range(ng) for p in range(len(pts))}
    for p, (u, want) in enumerate(pts):
        for i in range(ng):
            a = side("l", i, p, u, lv, lg, gval)
            b = side("r", i, p, u, rv, rg, gval)
            g = gval[(i, p)]
            cls += [[-g, a], [-g, b], [g, -a, -b]]
        # eval = OR of selected bare output vars in u, and selected true gates
        lits: list[int] = [ov[v] for v in sorted(u)]
        for i in range(ng):
            a = int(pool.id(("oa", i, p)))
            cls += [[-a, og[i]], [-a, gval[(i, p)]], [a, -og[i], -gval[(i, p)]]]
            lits.append(a)
        if want:
            cls.append(lits)
        else:
            for x in lits:
                cls.append([-x])

    sys.stdout.write(f"{ng} AND gates, {len(pts)} points -> {pool.top} vars, {len(cls)} clauses\n")
    t0 = time.time()
    with Cadical153(bootstrap_with=cls) as solver:
        ok = solver.solve()
        el = time.time() - t0
        sys.stdout.write(f"{'SAT' if ok else 'UNSAT'} in {el:.1f}s\n")
        if not ok:
            return None
        model = {x for x in solver.get_model() if x > 0}
        return {
            "size": ng,
            "leftVars": [[v for v in range(N) if lv[(i, v)] in model] for i in range(ng)],
            "rightVars": [[v for v in range(N) if rv[(i, v)] in model] for i in range(ng)],
            "leftGates": [[j for j in range(i) if lg[(i, j)] in model] for i in range(ng)],
            "rightGates": [[j for j in range(i) if rg[(i, j)] in model] for i in range(ng)],
            "outVars": [v for v in range(N) if ov[v] in model],
            "outGates": [i for i in range(ng) if og[i] in model],
        }


def main() -> int:
    ng = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    budget = float(sys.argv[2]) if len(sys.argv) > 2 else 0.0
    mis = maximal_independent_sets()
    pts = points()
    sys.stdout.write(f"maximal independent sets: {len(mis)}  sizes {sorted({len(m) for m in mis})}\n")
    sys.stdout.write(f"defined points: {len(pts)} ({len(mis)} false, {len(pts) - len(mis)} true)\n")
    got = solve(ng, budget)
    if got is None:
        sys.stdout.write(f"no {ng}-AND circuit exists (exact, so this is a proof for {ng})\n")
        return 1
    json.dump(got, open(D / f"circuit_{ng}.json", "w"), indent=1)
    sys.stdout.write(json.dumps(got, indent=1) + "\n")
    sys.stdout.write(f"wrote {D / f'circuit_{ng}.json'}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
