#!/usr/bin/env python3
"""Sweep exact gate counts UPWARD (or a given list) for one graph and one NOT
budget, printing one table line per size: SAT / UNSAT / DID-NOT-RETURN, with the
wall time of each solver call.  Stops at the first SAT (that size is then the
minimum, because every smaller size is a recorded UNSAT), at the first
DID-NOT-RETURN, or when the total budget runs out.

usage: pnotsweep --graph G1 --nots 0 --from 1 --to 12 --mode tight
                 --per 300 --budget 900
"""

from __future__ import annotations

import argparse
import importlib.util
import itertools
import sys
import time
from pathlib import Path
from typing import Any, List, Optional, Sequence

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
ns = load("notsat", PNOT / "notsat.py")
rep = ns.rep


def one(n: int, edges: Sequence[Any], s: int, nots: int, tight: bool,
        per: int, work: Path, tag: str) -> tuple:
    rows = nl.all_rows(n, edges)
    t0 = time.time()
    enc = rep.build(n, s, rows, tight, tight)
    cnf = enc.cnf
    notvars: List[int] = []
    for j in range(s):
        nf = [enc.sel[j][f] for f in enc.forms[j] if f.op == "not"]
        if nots <= 0:
            for v in nf:
                cnf.clauses.append([-v])
        else:
            u = cnf.new_var()
            for v in nf:
                cnf.clauses.append([-v, u])
            notvars.append(u)
    if nots >= 1:
        for a, b in itertools.combinations(notvars, 2):
            cnf.clauses.append([-a, -b])
    build_t = time.time() - t0
    work.mkdir(parents=True, exist_ok=True)
    path = work / (f"sw_n{n}e{len(edges)}_s{s}_nots{nots}"
                   f"{'_tight' if tight else '_loose'}{tag}.cnf")
    cnf.write(path)
    solver = rep.find_solver()
    status, assign, dt = rep.run_solver(solver, path, per)
    gates = None
    if status == "SAT":
        specs = rep.decode(enc, assign)
        gates = [nl.Gate(g.op, list(g.inputs)) for g in specs]
    try:
        path.unlink()
    except OSError:
        pass
    return status, dt, build_t, cnf.nvars, len(cnf.clauses), gates


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--graph", type=str, default="")
    ap.add_argument("--n", type=int, default=0)
    ap.add_argument("--edges", type=str, default="")
    ap.add_argument("--sizes", type=str, default="",
                    help="explicit comma list, overrides --from/--to")
    ap.add_argument("--from", dest="lo", type=int, default=1)
    ap.add_argument("--to", dest="hi", type=int, default=12)
    ap.add_argument("--nots", type=int, default=0)
    ap.add_argument("--mode", choices=("tight", "loose"), default="tight")
    ap.add_argument("--per", type=int, default=300)
    ap.add_argument("--budget", type=int, default=840)
    ap.add_argument("--tag", type=str, default="")
    ap.add_argument("--keep-going", action="store_true",
                    help="do not stop at the first SAT or DID-NOT-RETURN")
    args = ap.parse_args(argv)

    if args.graph:
        n, edges = nl.GRAPHS[args.graph]
    else:
        n, edges = args.n, ns.parse_edges(args.edges)
    sizes = ([int(x) for x in args.sizes.replace(",", " ").split()]
             if args.sizes else list(range(args.lo, args.hi + 1)))
    tight = args.mode == "tight"
    label = args.graph or f"n={n}/{len(edges)}e"
    print(f"SWEEP {label} nots<={args.nots} mode={args.mode} sizes={sizes} "
          f"per={args.per}s budget={args.budget}s")
    t_start = time.time()
    rc = 0
    for s in sizes:
        spent = time.time() - t_start
        if spent > args.budget:
            print(f"  s={s}: SKIPPED (budget spent)")
            break
        per = min(args.per, int(args.budget - spent))
        status, dt, bt, nv, nc, gates = one(
            n, edges, s, args.nots, tight, per, PNOT / "cnf", args.tag)
        word = {"SAT": "SAT", "UNSAT": "UNSAT",
                "TIMEOUT": "DID-NOT-RETURN"}.get(status, f"NO-VERDICT({status})")
        print(f"  s={s:>3} nots<={args.nots} {args.mode:>5}: {word:>14} "
              f"solver={dt:8.1f}s build={bt:5.1f}s vars={nv} clauses={nc}",
              flush=True)
        if gates is not None:
            out = n + s - 1
            ok, bad = nl.check_circuit(n, edges, gates, out)
            print(nl.gate_list_str(gates, n))
            print(f"    output wire: {out}  NOTs={nl.not_count(gates)}  "
                  f"simulator={'ACCEPTED' if ok else f'REJECTED {bad[:3]}'}")
            print("    lean gates: " + nl.lean_gate_list(gates))
            if not ok:
                print("    !! DECODING BUG")
                return 3
            if not args.keep_going:
                print(f"SWEEP RESULT: minimum (nots<={args.nots}) = {s}")
                return 0
        elif status == "TIMEOUT" and not args.keep_going:
            print(f"SWEEP RESULT: stalled at s={s} -- NOT an UNSAT")
            return 2
    print("SWEEP RESULT: finished list without a SAT")
    return rc


if __name__ == "__main__":
    sys.exit(main())
