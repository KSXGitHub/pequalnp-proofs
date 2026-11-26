#!/usr/bin/env python3
"""CONTROL 2: the hand-built star cover for each graph, checked by the
independent simulator on all 2^n inputs.  Also prints the data the normal form
in rep44.py needs to be legitimate (f not constant, not a projection)."""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path
from typing import Any

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


def main() -> int:
    rc = 0
    for name in ("G1", "G2", "G3"):
        n, edges = nl.GRAPHS[name]
        nb = nl.neighbours(n, edges)
        rows = nl.all_rows(n, edges)
        ones = sum(1 for _, w in rows if w)
        print(f"=== {name}: n={n} edges={len(edges)} rows={len(rows)} "
              f"ones={ones} zeros={len(rows) - ones}")
        print(f"  degrees: {[len(nb[u]) for u in range(n)]}")

        # normal-form sanity: f is not constant and not a single input wire
        if ones == 0 or ones == len(rows):
            print("  !! f is constant: normal form not justified")
            rc = 3
        proj = [i for i in range(n)
                if all(w == bits[i] for bits, w in rows)]
        if proj:
            print(f"  !! f equals input wire(s) {proj}: output need not be a gate")
            rc = 3
        else:
            print("  f is not constant and equals no input wire "
                  "-> the output of a least circuit is a gate wire")

        cover, gates, out, mincard = nl.best_star_cover(n, edges)
        ok, bad = nl.check_circuit(n, edges, gates, out)
        cost = sum(len(nb[u]) for u in cover) + len(cover) - 1
        print(f"  cheapest star cover: C={cover} "
              f"(degrees {[len(nb[u]) for u in cover]}) gates={len(gates)} "
              f"= sum(deg)+|C|-1 = {cost}")
        print(nl.gate_list_str(gates, n))
        print(f"  output wire: {out}")
        print(f"  simulator on all {1 << n} inputs: "
              f"{'ACCEPTED' if ok else f'REJECTED ({len(bad)} bad rows {bad[:3]})'}")
        if not ok:
            rc = 3
        g2, o2 = nl.star_cover_circuit(n, edges, mincard)
        ok2, bad2 = nl.check_circuit(n, edges, g2, o2)
        print(f"  minimum-CARDINALITY cover C={mincard} -> gates={len(g2)}, "
              f"simulator {'ACCEPTED' if ok2 else 'REJECTED'}")
        if not ok2:
            rc = 3
        print(f"  => M <= {min(len(gates), len(g2))} and N <= {min(len(gates), len(g2))}")
        print()
    return rc


if __name__ == "__main__":
    sys.exit(main())
