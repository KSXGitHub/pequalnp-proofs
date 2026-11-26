#!/usr/bin/env python3
"""CONTROL: a brute-force minimum-circuit search, written with no SAT at all, as
an independent oracle for tiny graphs.  Used to calibrate the SAT code path:
the SAT sweep must agree with this on every graph small enough for both.

Search space = rep44's normal form, expressed directly: gates in order, each
`and`/`or` on two distinct earlier wires or `not` on one earlier wire, output the
last gate, no gate equal to a constant or to an earlier wire (all of which hold
of a LEAST circuit).  Sizes are swept upward, so the first size at which a
circuit is found is the minimum -- no reachability condition needed, because a
circuit with an unread gate yields a strictly smaller one, which an earlier
(already failed) size would have had.

Columns are bitmasks over all 2^n inputs, so correctness is on every input.
Every circuit found is re-checked by notlib's simulator before it is reported.

usage: pnotbrute [--graph G1|G2|G3] [--n N --edges a-b,c-d] [--max-gates k]
                 [--nots 0|1]
"""

from __future__ import annotations

import argparse
import importlib.util
import sys
import time
from pathlib import Path
from typing import Any, List, Optional, Sequence, Tuple

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

Form = Tuple[str, int, int]


def columns(n: int, edges: Sequence[Tuple[int, int]]) -> Tuple[List[int], int, int]:
    """Input columns as bitmasks over row index r (input i = bit i of r), the
    target column, and the all-ones mask."""
    nrow = 1 << n
    full = (1 << nrow) - 1
    cols = [0] * n
    target = 0
    for r in range(nrow):
        bits = tuple(bool((r >> i) & 1) for i in range(n))
        for i in range(n):
            if bits[i]:
                cols[i] |= 1 << r
        if nl.f_of(n, edges, bits):
            target |= 1 << r
    return cols, target, full


def search(n: int, edges: Sequence[Tuple[int, int]], s: int, nots: int
           ) -> Optional[List[Any]]:
    cols0, target, full = columns(n, edges)
    gates: List[Any] = []

    def rec(cols: List[int], left: int, nleft: int) -> bool:
        top = len(cols)
        last = left == 1
        for b in range(top):
            cb = cols[b]
            for a in range(b):
                ca = cols[a]
                for op, c in (("and", ca & cb), ("or", ca | cb)):
                    if c == 0 or c == full or c in cols:
                        continue
                    if last:
                        if c != target:
                            continue
                        gates.append(nl.Gate(op, [a, b]))
                        return True
                    cols.append(c)
                    gates.append(nl.Gate(op, [a, b]))
                    if rec(cols, left - 1, nleft):
                        return True
                    gates.pop()
                    cols.pop()
        if nleft > 0:
            for a in range(top):
                c = (~cols[a]) & full
                if c == 0 or c == full or c in cols:
                    continue
                if last:
                    if c != target:
                        continue
                    gates.append(nl.Gate("not", [a]))
                    return True
                cols.append(c)
                gates.append(nl.Gate("not", [a]))
                if rec(cols, left - 1, nleft - 1):
                    return True
                gates.pop()
                cols.pop()
        return False

    if rec(list(cols0), s, nots):
        return list(gates)
    return None


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--graph", type=str, default="")
    ap.add_argument("--n", type=int, default=0)
    ap.add_argument("--edges", type=str, default="")
    ap.add_argument("--max-gates", type=int, default=5)
    ap.add_argument("--nots", type=int, default=0)
    args = ap.parse_args(argv)

    if args.graph:
        n, edges = nl.GRAPHS[args.graph]
    else:
        n = args.n
        edges = []
        for tok in args.edges.replace(",", " ").split():
            x, y = tok.split("-")
            edges.append((int(x), int(y)))

    label = args.graph or f"n={n} edges={edges}"
    print(f"brute force: {label}  nots<={args.nots}  up to {args.max_gates} gates")
    for s in range(1, args.max_gates + 1):
        t0 = time.time()
        got = search(n, edges, s, args.nots)
        dt = time.time() - t0
        if got is None:
            print(f"  s={s}: NONE ({dt:.1f}s)")
            continue
        out = n + s - 1
        ok, bad = nl.check_circuit(n, edges, got, out)
        nc = nl.not_count(got)
        print(f"  s={s}: FOUND ({dt:.1f}s) NOTs={nc} simulator="
              f"{'ACCEPTED' if ok else f'REJECTED {bad[:3]}'}")
        print(nl.gate_list_str(got, n))
        print(f"  output wire: {out}")
        if not ok:
            return 3
        print(f"BRUTE RESULT: minimum with nots<={args.nots} is {s}")
        return 0
    print(f"BRUTE RESULT: no circuit with <= {args.max_gates} gates, "
          f"nots<={args.nots}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
