#!/usr/bin/env python3
"""Check a found AndCountCircuit against the Lean semantics, independently.

The SAT encoder can be satisfiable and still wrong: a model satisfies MY clauses,
which is only as good as my transcription of PEqualNP/Defs/AndCountCircuit.lean.
So this re-implements the definitions straight from that file and re-checks every
one of the 115 required points, plus WellFormed and the bare-count bound.

From the Lean source:
  sideTrue U B F i val = (exists v in B, v in U) or (exists j in F, j < i and val j)
  gateVal U i          = sideTrue (leftVars i) (leftGates i) and sideTrue (rightVars i) ...
  eval U               = (exists v in outVars, v in U) or (exists j in outGates, gateVal U j)
  WellFormed           = every gate read by a side of gate i has index < i

usage: verify.py <gates>
"""

from __future__ import annotations

import itertools
import json
import pathlib
import sys
from typing import Any, Final

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


def _rows(raw: dict[str, Any], key: str) -> list[set[int]]:
    return [{int(v) for v in row} for row in raw[key]]


def _flat(raw: dict[str, Any], key: str) -> set[int]:
    return {int(v) for v in raw[key]}


class Circuit:
    """The circuit as the Lean structure defines it, read from the solver's JSON."""

    def __init__(self, raw: dict[str, Any]) -> None:
        self.size: int = int(raw["size"])
        self.lv: list[set[int]] = _rows(raw, "leftVars")
        self.rv: list[set[int]] = _rows(raw, "rightVars")
        self.lgs: list[set[int]] = _rows(raw, "leftGates")
        self.rgs: list[set[int]] = _rows(raw, "rightGates")
        self.ov: set[int] = _flat(raw, "outVars")
        self.og: set[int] = _flat(raw, "outGates")

    def well_formed(self) -> bool:
        return all(all(j < i for j in self.lgs[i]) and all(j < i for j in self.rgs[i]) for i in range(self.size))

    def bare_counts(self) -> list[int]:
        return [sum(1 for i in range(self.size) if v in self.lv[i] or v in self.rv[i]) for v in range(N)]

    def gate_vals(self, u: frozenset[int]) -> list[bool]:
        val: list[bool] = [False] * self.size
        for i in range(self.size):
            left = bool(self.lv[i] & u) or any(j < i and val[j] for j in self.lgs[i])
            right = bool(self.rv[i] & u) or any(j < i and val[j] for j in self.rgs[i])
            val[i] = left and right
        return val

    def eval(self, u: frozenset[int]) -> bool:
        val = self.gate_vals(u)
        return bool(self.ov & u) or any(val[j] for j in self.og)


def main() -> int:
    ng = int(sys.argv[1])
    path = D / f"circuit_{ng}.json"
    if not path.exists():
        sys.stdout.write(f"{path} does not exist\n")
        return 1
    raw: dict[str, Any] = json.load(open(path))
    c = Circuit(raw)
    sys.stdout.write(f"size={c.size}  WellFormed={c.well_formed()}\n")
    counts = c.bare_counts()
    sys.stdout.write(f"bare counts per vertex: {counts}  max={max(counts)} (cap 2)\n")

    bad: list[str] = []
    checked = 0
    for mis in maximal_independent_sets():
        checked += 1
        if c.eval(mis):
            bad.append(f"eval is TRUE on the maximal set {sorted(mis)}, must be false")
        for w in range(N):
            if w in mis:
                continue
            checked += 1
            if not c.eval(mis | {w}):
                bad.append(f"eval is FALSE on {sorted(mis)} + {w}, must be true")
    sys.stdout.write(f"points checked: {checked}\n")
    for b in bad[:6]:
        sys.stdout.write(f"  WRONG: {b}\n")
    ok = not bad and c.well_formed() and max(counts) <= 2 and c.size <= ng
    if ok:
        sys.stdout.write(f"\nVERIFIED: the {ng}-AND circuit meets every condition of the step\n")
    else:
        sys.stdout.write(f"\nFAILED: {len(bad)} wrong points, WellFormed={c.well_formed()}\n")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
