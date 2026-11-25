#!/usr/bin/env python3
"""gennot.py with the function given as a truth-table number instead of a graph's edges.

`notes/data/lrat-link/gennot.py` only ever uses the function through `g(r)`, so this is that file
with `g` replaced by `T.testBit(r)` and the clause order kept exactly.  `--selfcheck EDGES`
regenerates the edge function's table and asserts the CNF is byte-identical to gennot.py's.

Usage: gentab.py n s TABLE out.cnf
"""

from __future__ import annotations

import sys
from collections.abc import Callable

Clause = list[int]


def build(n: int, s: int, g: Callable[[int], bool]) -> tuple[int, list[Clause]]:
    """The clauses of `LinkN.enc2 n s g (List.range (2^n))`, in gennot.py's order."""
    R = 1 << n
    A = R + n + s + 2
    rows = list(range(R))

    def ix(kd: int, j: int, a: int) -> int:
        return (kd * (s + 1) + j) * A + a

    def P(v: int) -> int:
        return v + 1

    def Q(v: int) -> int:
        return -(v + 1)

    def L(v: int, b: bool) -> int:
        return P(v) if b else Q(v)

    def bit(r: int, k: int) -> bool:
        return (r >> k) & 1 == 1

    F: list[Clause] = []
    # fOp
    for j in range(s):
        F.append([P(ix(0, j, 0)), P(ix(0, j, 1)), P(ix(0, j, 2)), P(ix(0, j, 3))])
    # fSrcAlo
    for sd in (1, 2):
        for j in range(s):
            F.append([P(ix(sd, j, k)) for k in range(n + j + 1)])
    # fSrcEq
    for sd in (1, 2):
        for j in range(s):
            for r in rows:
                for k in range(n + j + 1):
                    if k < n:
                        F.append([Q(ix(sd, j, k)), L(ix(sd + 3, j, r), bit(r, k))])
                    elif k < n + j:
                        F.append([Q(ix(sd, j, k)), Q(ix(sd + 3, j, r)), P(ix(3, k - n, r))])
                        F.append([Q(ix(sd, j, k)), P(ix(sd + 3, j, r)), Q(ix(3, k - n, r))])
                    else:
                        F.append([Q(ix(sd, j, k)), Q(ix(sd + 3, j, r))])
    # fGate
    for j in range(s):
        for r in rows:
            o0, o1, o2 = ix(0, j, 0), ix(0, j, 1), ix(0, j, 2)
            w, u1, u2 = ix(3, j, r), ix(4, j, r), ix(5, j, r)
            F += [
                [Q(o0), Q(w), P(u1)],
                [Q(o0), Q(w), P(u2)],
                [Q(o0), P(w), Q(u1), Q(u2)],
                [Q(o1), P(w), Q(u1)],
                [Q(o1), P(w), Q(u2)],
                [Q(o1), Q(w), P(u1), P(u2)],
                [Q(o2), P(w)],
                [Q(ix(0, j, 3)), P(w), P(u1)],
                [Q(ix(0, j, 3)), Q(w), Q(u1)],
            ]
    # fOutAlo
    F.append([P(ix(6, 0, k)) for k in range(n + s + 1)])
    # fOutEq
    for r in rows:
        for k in range(n + s + 1):
            if k < n:
                if bit(r, k) != g(r):
                    F.append([Q(ix(6, 0, k))])
            elif k < n + s:
                F.append([Q(ix(6, 0, k)), L(ix(3, k - n, r), g(r))])
            elif g(r):
                F.append([Q(ix(6, 0, k))])

    # symmetry / normal form
    def pad(j: int) -> int:
        return ix(7, j, 0)

    F.append([P(ix(6, 0, n + s - 1)), P(pad(s - 1))])
    for j in range(s):
        F += [
            [Q(pad(j)), P(ix(0, j, 2))],
            [Q(pad(j)), P(ix(1, j, n + j))],
            [Q(pad(j)), P(ix(2, j, n + j))],
            [P(pad(j)), Q(ix(0, j, 2))],
            [P(pad(j)), Q(ix(1, j, n + j))],
            [P(pad(j)), Q(ix(2, j, n + j))],
        ]
    for j in range(s - 1):
        F.append([Q(pad(j + 1)), P(pad(j))])
    for j in range(s):
        for i in range(j):
            F += [[Q(pad(i)), Q(ix(1, j, n + i))], [Q(pad(i)), Q(ix(2, j, n + i))]]
    for j in range(s):
        for k in range(n + j + 1):
            for l in range(k + 1):
                F.append([Q(ix(1, j, k)), Q(ix(2, j, l)), P(pad(j))] + ([P(ix(0, j, 3))] if l == k else []))
    for j in range(s - 1):
        F.append(
            [P(ix(1, i, n + j)) for i in range(j + 1, s)] + [P(ix(2, i, n + j)) for i in range(j + 1, s)] + [P(pad(j))]
        )
    for j in range(s):
        for k in range(n + j + 1):
            F.append([Q(ix(0, j, 3)), Q(ix(1, j, k)), P(ix(2, j, k))])
    for j in range(s):
        for i in range(j):
            F.append([Q(ix(0, j, 3)), Q(ix(0, i, 3)), Q(ix(1, j, n + i))])
    # lex (gennot.py always emits this part: 'lex' is unconditionally in its `drop` set)
    for j in range(s - 1):
        base = [P(pad(j)), P(ix(1, j + 1, n + j)), P(ix(2, j + 1, n + j))]
        for a in range(n + j + 1):
            for b in range(a):
                F.append([Q(ix(1, j, a)), Q(ix(1, j + 1, b)), *base])
            for c in range(n + j + 1):
                for d in range(c):
                    F.append([Q(ix(1, j, a)), Q(ix(1, j + 1, a)), Q(ix(2, j, c)), Q(ix(2, j + 1, d)), *base])
                F.append(
                    [Q(ix(1, j, a)), Q(ix(1, j + 1, a)), Q(ix(2, j, c)), Q(ix(2, j + 1, c)), Q(ix(0, j, 1)), *base]
                )
                F.append(
                    [Q(ix(1, j, a)), Q(ix(1, j + 1, a)), Q(ix(2, j, c)), Q(ix(2, j + 1, c)), Q(ix(0, j + 1, 0)), *base]
                )
    return 10 * (s + 1) * A, F


def render(nv: int, F: list[Clause]) -> str:
    return f"p cnf {nv} {len(F)}\n" + "".join(" ".join(map(str, c)) + " 0\n" for c in F)


def main() -> int:
    n, s, table, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    nv, F = build(n, s, lambda r: (table >> r) & 1 == 1)
    with open(out, "w") as o:
        o.write(render(nv, F))
    print(f"vars={nv} clauses={len(F)}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
