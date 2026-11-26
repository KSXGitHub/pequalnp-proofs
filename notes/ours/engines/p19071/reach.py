#!/usr/bin/env python3
"""Solver-free, encoding-free restatement of the question, to cross-check rep44.py.

On the 16 promise rows (u, v) in Fin 4 x Fin 4, index the rows r = 4u + v.  Each WIRE of a
circuit then has a 16-bit COLUMN: bit r is its value on row r.

  input wire u  (u < 4) : true exactly on rows 4u .. 4u+3   ->  0xF << (4*u)
  input wire 4+v        : true exactly on rows v, 4+v, 8+v, 12+v -> 0x1111 << v
  gate (and a b)        : column_a & column_b
  gate (or a b)         : column_a | column_b
  gate (not a)          : ~column_a  (16 bits)
  an out-of-range index : 0

`Represents A C` with A u v = mask.testBit (4u+v) and the output the last gate says exactly:
the last gate's column is `mask`.  So the least size of a normal-form circuit is the least
number of AND/OR/NOT steps that reach `mask` from the eight input columns, reusing any
earlier column freely.  This file counts levels of that reachability relation, with the two
leastness prunings (a new column is never 0 and never equal to a column already present),
and so depends on no CNF and no SAT solver.
"""

from __future__ import annotations

import sys
from typing import FrozenSet, List, Set, Tuple

M = 0xFFFF
INPUTS: Tuple[int, ...] = tuple([0xF << (4 * u) for u in range(4)]
                               + [0x1111 << v for v in range(4)])


def step_candidates(avail: Tuple[int, ...]) -> Set[int]:
    out: Set[int] = set()
    k = len(avail)
    for i in range(k):
        a = avail[i]
        out.add(~a & M)
        for j in range(i + 1, k):
            b = avail[j]
            out.add(a & b)
            out.add(a | b)
    out.discard(0)
    return out - set(avail)


def reach_in_one(avail: Tuple[int, ...], target: int) -> bool:
    k = len(avail)
    for i in range(k):
        a = avail[i]
        if (~a & M) == target:
            return True
        for j in range(i + 1, k):
            b = avail[j]
            if (a & b) == target or (a | b) == target:
                return True
    return False


def main() -> int:
    target = int(sys.argv[1])
    depth = int(sys.argv[2])
    print(f"target=0x{target:04x}={target} inputs={[hex(x) for x in INPUTS]}")
    # level 0
    level: Set[FrozenSet[int]] = {frozenset()}
    for d in range(1, depth + 1):
        nxt: Set[FrozenSet[int]] = set()
        hit = False
        for st in level:
            avail = INPUTS + tuple(sorted(st))
            if reach_in_one(avail, target):
                hit = True
                break
            for c in step_candidates(avail):
                nxt.add(st | {c})
        if hit:
            print(f"REACHABLE at depth {d}")
            return 0
        print(f"depth {d}: no hit; distinct states after {d} gates = {len(nxt)}", flush=True)
        level = nxt
    print(f"NOT REACHABLE within depth {depth}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
