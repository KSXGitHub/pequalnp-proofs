#!/usr/bin/env python3
"""Better hand-built monotone upper bounds than the plain star cover, all checked
by the independent simulator on all 2^n inputs.

Construction (a strict generalisation of the star cover).  Pick a vertex cover C
and assign every edge to ONE covering endpoint.  Then

    f = OR over u in C of ( x_u AND OR_{v assigned to u} x_v )

which is still exactly "contains an edge": each term is an OR of genuine edges at
u, and every edge is assigned once.  The OR-of-neighbours subexpressions are then
built with SHARING: when a needed set T already has an available subset A, only
|T| - |A| further OR gates are spent, and every intermediate becomes available.
The star cover is the special case C = cover, every edge assigned to every
covering endpoint, no sharing.

All vertex covers are enumerated, with four edge-assignment rules, and the
cheapest result is reported.
"""

from __future__ import annotations

import argparse
import importlib.util
import itertools
import sys
from pathlib import Path
from typing import Any, Dict, FrozenSet, List, Optional, Sequence, Tuple

PNOT = Path("/tmp/claude-0/-home-user-pequalnp-proofs/"
            "731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/pnot")


def load(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, str(path))
    assert spec and spec.loader
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


nl = load("notlib", PNOT / "notlib.py")

Edge = Tuple[int, int]


def build_circuit(n: int, heads: Sequence[int],
                  assigned: Dict[int, List[int]]) -> Tuple[List[Any], int]:
    """Emit the gate list for the term family, sharing OR subexpressions."""
    gates: List[Any] = []

    def emit(op: str, ins: List[int]) -> int:
        gates.append(nl.Gate(op, ins))
        return n + len(gates) - 1

    # available OR-subexpressions: frozenset of vertices -> wire index
    avail: Dict[FrozenSet[int], int] = {frozenset([i]): i for i in range(n)}

    def or_wire(want: FrozenSet[int]) -> int:
        if want in avail:
            return avail[want]
        # the largest available subset of `want`
        best: Optional[FrozenSet[int]] = None
        for a in avail:
            if a <= want and (best is None or len(a) > len(best)):
                best = a
        assert best is not None
        cur, curset = avail[best], best
        for v in sorted(want - best):
            cur = emit("or", [cur, v])
            curset = curset | {v}
            avail[curset] = cur
        return cur

    terms: List[int] = []
    # build the bigger OR sets first so the smaller ones can reuse prefixes
    order = sorted(heads, key=lambda u: -len(assigned[u]))
    wires: Dict[int, int] = {}
    for u in order:
        wires[u] = or_wire(frozenset(assigned[u]))
    for u in heads:
        terms.append(emit("and", [u, wires[u]]))
    out = terms[0]
    for t in terms[1:]:
        out = emit("or", [out, t])
    return gates, out


def try_cover(n: int, edges: Sequence[Edge], cover: Sequence[int], rule: str
              ) -> Optional[Tuple[List[Any], int]]:
    s = set(cover)
    deg_in = {u: sum(1 for a, b in edges if u in (a, b)) for u in s}
    assigned: Dict[int, List[int]] = {u: [] for u in s}
    for a, b in edges:
        ends = [x for x in (a, b) if x in s]
        if not ends:
            return None
        if len(ends) == 1:
            u = ends[0]
        elif rule == "lo":
            u = min(ends)
        elif rule == "hi":
            u = max(ends)
        elif rule == "deghi":
            u = max(ends, key=lambda x: (deg_in[x], x))
        else:
            u = min(ends, key=lambda x: (deg_in[x], x))
        other = b if u == a else a
        assigned[u].append(other)
    heads = [u for u in sorted(s) if assigned[u]]
    if not heads:
        return None
    return build_circuit(n, heads, {u: sorted(set(assigned[u])) for u in heads})


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--graphs", type=str, default="G1,G2,G3")
    args = ap.parse_args(argv)
    rc = 0
    for name in args.graphs.replace(",", " ").split():
        n, edges = nl.GRAPHS[name]
        best: Optional[Tuple[int, str, Tuple[int, ...], List[Any], int]] = None
        for k in range(1, n + 1):
            for cover in itertools.combinations(range(n), k):
                if not nl.is_cover(edges, cover):
                    continue
                for rule in ("lo", "hi", "deghi", "deglo"):
                    got = try_cover(n, edges, cover, rule)
                    if got is None:
                        continue
                    gates, out = got
                    if best is None or len(gates) < best[0]:
                        best = (len(gates), rule, cover, gates, out)
        assert best is not None
        cnt, rule, cover, gates, out = best
        ok, bad = nl.check_circuit(n, edges, gates, out)
        print(f"=== {name}: best shared-OR cover circuit = {cnt} gates "
              f"(cover={list(cover)}, rule={rule})")
        print(nl.gate_list_str(gates, n))
        print(f"  output wire: {out}  NOTs={nl.not_count(gates)}")
        print(f"  simulator on all {1 << n} inputs: "
              f"{'ACCEPTED' if ok else f'REJECTED {bad[:3]}'}")
        print(f"  => M({name}) <= {cnt}, N({name}) <= {cnt}")
        if not ok:
            rc = 3
        print()
    return rc


if __name__ == "__main__":
    sys.exit(main())
