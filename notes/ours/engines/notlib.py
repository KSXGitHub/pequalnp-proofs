#!/usr/bin/env python3
"""Graphs, the target function, an INDEPENDENT Lean-faithful simulator, and the
hand-built star-cover upper bound.

Nothing in this file knows anything about SAT or about the encoder in rep44.py.
It is the control: every circuit that comes out of the solver is decoded to a
plain gate list and then checked here, against f recomputed from the edge list,
on all 2^n inputs.

Lean semantics reproduced (PEqualNP/Defs/CircuitLowerBounds.lean):

    Circuit.wires C x = C.gates.foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
    Circuit.eval  C x = (C.wires x).getD C.output false
    GateOp.eval and l = l.all id      -- true on []
    GateOp.eval or  l = l.any id      -- false on []
    GateOp.eval not l = !(l.headD false)   -- true on []

so wires 0..n-1 are the inputs, gate j produces wire n+j, a wire index that does
not exist reads false, and an out-of-range output wire makes eval false.
`inputs.length <= 2` permits fan-in 1 and 0.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass
from typing import Dict, List, Sequence, Tuple

Edge = Tuple[int, int]

GRAPHS: Dict[str, Tuple[int, List[Edge]]] = {
    "G1": (8, [(0, 3), (1, 4), (0, 5), (1, 5), (2, 5), (2, 6),
               (3, 6), (4, 6), (0, 7), (1, 7), (2, 7), (3, 7)]),
    "G2": (7, [(0, 3), (1, 4), (0, 5), (1, 5), (3, 5), (0, 6),
               (1, 6), (2, 6), (4, 6), (5, 6)]),
    "G3": (7, [(0, 2), (1, 3), (0, 4), (1, 4), (2, 4), (0, 5), (1, 5),
               (3, 5), (0, 6), (1, 6), (2, 6), (3, 6), (4, 6), (5, 6)]),
}


@dataclass
class Gate:
    op: str               # "and" | "or" | "not"
    inputs: List[int]


# ---------------------------------------------------------------- the function


def f_of(n: int, edges: Sequence[Edge], bits: Sequence[bool]) -> bool:
    """f(x) = OR over edges (a,b) of (x_a AND x_b).  Recomputed from the edge
    list every time, never cached from the encoder."""
    for a, b in edges:
        if bits[a] and bits[b]:
            return True
    return False


def all_rows(n: int, edges: Sequence[Edge]) -> List[Tuple[Tuple[bool, ...], bool]]:
    """All 2^n rows, input i = bit i of the row index (any fixed order will do;
    the encoder is handed exactly this list)."""
    rows: List[Tuple[Tuple[bool, ...], bool]] = []
    for r in range(1 << n):
        bits = tuple(bool((r >> i) & 1) for i in range(n))
        rows.append((bits, f_of(n, edges, bits)))
    return rows


# ------------------------------------------------------- independent simulator


def simulate(gates: Sequence[Gate], bits: Sequence[bool], output: int) -> bool:
    w: List[bool] = list(bits)
    for g in gates:
        vals = [w[i] if 0 <= i < len(w) else False for i in g.inputs]
        if g.op == "and":
            w.append(all(vals))
        elif g.op == "or":
            w.append(any(vals))
        elif g.op == "not":
            w.append(not (vals[0] if vals else False))
        else:
            raise ValueError(f"unknown op {g.op!r}")
    return w[output] if 0 <= output < len(w) else False


def check_circuit(n: int, edges: Sequence[Edge], gates: Sequence[Gate],
                  output: int) -> Tuple[bool, List[Tuple[int, bool, bool]]]:
    """Check a gate list against f on ALL 2^n inputs.  Also checks the basis:
    every gate is and/or/not with at most two inputs, and reads only wires that
    already exist (so the circuit is acyclic in the Lean sense)."""
    bad: List[Tuple[int, bool, bool]] = []
    for j, g in enumerate(gates):
        if g.op not in ("and", "or", "not"):
            raise ValueError(f"gate {j}: op {g.op!r} outside the basis")
        if len(g.inputs) > 2:
            raise ValueError(f"gate {j}: fan-in {len(g.inputs)} > 2")
        for i in g.inputs:
            if i < 0:
                raise ValueError(f"gate {j}: negative wire {i}")
    for r in range(1 << n):
        bits = tuple(bool((r >> i) & 1) for i in range(n))
        got = simulate(gates, bits, output)
        want = f_of(n, edges, bits)
        if got != want:
            bad.append((r, want, got))
    return (not bad, bad)


def not_count(gates: Sequence[Gate]) -> int:
    return sum(1 for g in gates if g.op == "not")


# ----------------------------------------------------------- the star cover


def neighbours(n: int, edges: Sequence[Edge]) -> List[List[int]]:
    nb: List[List[int]] = [[] for _ in range(n)]
    for a, b in edges:
        nb[a].append(b)
        nb[b].append(a)
    return [sorted(set(x)) for x in nb]


def is_cover(edges: Sequence[Edge], c: Sequence[int]) -> bool:
    s = set(c)
    return all((a in s) or (b in s) for a, b in edges)


def star_cover_circuit(n: int, edges: Sequence[Edge],
                       cover: Sequence[int]) -> Tuple[List[Gate], int]:
    """f = OR over u in cover of (x_u AND (OR over v in N(u) of x_v)).

    Correct exactly when `cover` is a vertex cover: each term is the OR of the
    edges at u, and every edge has an endpoint in the cover.  Gate count is
    sum of deg(u) over the cover, plus |cover| - 1."""
    assert is_cover(edges, cover), "not a vertex cover"
    nb = neighbours(n, edges)
    gates: List[Gate] = []

    def emit(op: str, ins: List[int]) -> int:
        gates.append(Gate(op, ins))
        return n + len(gates) - 1

    terms: List[int] = []
    for u in cover:
        ns = nb[u]
        assert ns, "isolated vertex in the cover"
        w = ns[0]
        for v in ns[1:]:
            w = emit("or", [w, v])
        terms.append(emit("and", [u, w]))
    out = terms[0]
    for t in terms[1:]:
        out = emit("or", [out, t])
    return gates, out


def best_star_cover(n: int, edges: Sequence[Edge]
                    ) -> Tuple[List[int], List[Gate], int, List[int]]:
    """The cheapest star cover over all vertex covers, and the cheapest over the
    MINIMUM-cardinality vertex covers (the brief's literal recipe)."""
    nb = neighbours(n, edges)
    best: Tuple[int, Tuple[int, ...]] = (10 ** 9, ())
    best_min: Tuple[int, int, Tuple[int, ...]] = (10 ** 9, 10 ** 9, ())
    for k in range(1, n + 1):
        for c in itertools.combinations(range(n), k):
            if not is_cover(edges, c):
                continue
            cost = sum(len(nb[u]) for u in c) + len(c) - 1
            if cost < best[0]:
                best = (cost, c)
            if (len(c), cost) < (best_min[0], best_min[1]):
                best_min = (len(c), cost, c)
    gates, out = star_cover_circuit(n, edges, list(best[1]))
    return list(best[1]), gates, out, list(best_min[2])


def gate_list_str(gates: Sequence[Gate], n: int) -> str:
    return "\n".join(f"  wire {n + j}: {g.op} {g.inputs}" for j, g in enumerate(gates))


def lean_gate_list(gates: Sequence[Gate]) -> str:
    parts = ["⟨GateOp." + g.op + ", [" + ", ".join(str(i) for i in g.inputs) + "]⟩"
             for g in gates]
    return "[" + ", ".join(parts) + "]"
