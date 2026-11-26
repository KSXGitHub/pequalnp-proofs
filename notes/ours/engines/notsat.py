#!/usr/bin/env python3
"""One exact-synthesis query: is there a fan-in-two circuit of EXACTLY s gates,
with at most `nots` NOT gates, computing f_G on ALL 2^n inputs?

rep44.py is used UNCHANGED, through its `build(N, s, rows, symmetry,
distinct_cols)`: the row set is already a parameter, so feeding it all 2^n rows
of f is the whole adaptation.  The NOT budget is added on top of the returned
Encoding, by reading enc.forms / enc.sel and appending clauses to enc.cnf --
rep44.py itself is not touched.

Normal form.  rep44's docstring justifies "s gates, each and/or on two distinct
in-range wires or not on one in-range wire, output = last gate, every gate but
the last read by a later gate" for a LEAST circuit.  Every step of that argument
(fold out constants, delete copies, delete unread gates, output is a gate wire)
is about single gates and holds verbatim when the constrained row set is all
2^n inputs, provided f is neither constant nor equal to an input wire -- which
jobs/pnotstar.py checks and prints for each graph.  None of the folds ever adds
a NOT gate, so they also preserve a NOT budget.  Hence the sweep is exact.
"""

from __future__ import annotations

import argparse
import importlib.util
import itertools
import sys
import time
from pathlib import Path
from typing import Any, List, Optional, Sequence, Tuple

PNOT = Path("/tmp/claude-0/-home-user-pequalnp-proofs/"
            "731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/pnot")
REP44 = Path("/tmp/claude-0/-home-user-pequalnp-proofs/"
             "731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/pnp/p19071/rep44.py")


def load(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, str(path))
    assert spec and spec.loader
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


nl = load("notlib", PNOT / "notlib.py")
rep = load("rep44", REP44)


def parse_edges(spec: str) -> List[Tuple[int, int]]:
    out: List[Tuple[int, int]] = []
    for tok in spec.replace(",", " ").split():
        a, b = tok.split("-")
        out.append((int(a), int(b)))
    return out


def run(n: int, edges: Sequence[Tuple[int, int]], s: int, nots: int,
        symmetry: bool, distinct_cols: bool, timeout: Optional[int],
        work: Path, tag: str, solver_args: Sequence[str]) -> int:
    rows = nl.all_rows(n, edges)
    ones = sum(1 for _, w in rows if w)
    if ones == 0 or ones == len(rows):
        raise SystemExit("f is constant: normal form not justified")
    if any(all(w == bits[i] for bits, w in rows) for i in range(n)):
        raise SystemExit("f is an input wire: normal form not justified")

    t0 = time.time()
    enc = rep.build(n, s, rows, symmetry, distinct_cols)
    cnf = enc.cnf

    # ---- the NOT budget, added on top of rep44's encoding ----
    notvars: List[int] = []
    pinned = 0
    for j in range(s):
        nf = [enc.sel[j][f] for f in enc.forms[j] if f.op == "not"]
        if nots <= 0:
            for v in nf:
                cnf.clauses.append([-v])
                pinned += 1
        else:
            u = cnf.new_var()
            for v in nf:
                cnf.clauses.append([-v, u])
            notvars.append(u)
    if nots >= 1 and notvars:
        for a, b in itertools.combinations(notvars, 2):
            cnf.clauses.append([-a, -b])
    build_t = time.time() - t0

    work.mkdir(parents=True, exist_ok=True)
    name = (f"n{n}_e{len(edges)}_s{s}_nots{nots}"
            f"{'_sym' if symmetry else '_nosym'}{'_dc' if distinct_cols else ''}"
            f"{tag}.cnf")
    path = work / name
    enc.cnf.write(path)
    print(f"n={n} edges={len(edges)} rows={len(rows)} gates={s} nots<={nots} "
          f"symmetry={symmetry} distinct_cols={distinct_cols} "
          f"vars={cnf.nvars} clauses={len(cnf.clauses)} "
          f"(not-units={pinned}) build={build_t:.1f}s", flush=True)

    solver = rep.find_solver()
    status, assign, dt = rep.run_solver(solver, path, timeout, solver_args)
    print(f"solver={Path(solver).name} {' '.join(solver_args)} status={status} "
          f"seconds={dt:.1f}", flush=True)

    if status == "TIMEOUT":
        print(f"RESULT: DID-NOT-RETURN s={s} nots<={nots} -- NOT a negative result")
        return 2
    if status == "UNSAT":
        print(f"RESULT: UNSAT s={s} nots<={nots} "
              f"symmetry={symmetry} distinct_cols={distinct_cols}")
        return 0
    if status != "SAT":
        print("RESULT: solver gave no verdict")
        return 2

    specs = rep.decode(enc, assign)
    gates = [nl.Gate(g.op, list(g.inputs)) for g in specs]
    output = n + s - 1
    nc = nl.not_count(gates)
    print("gates:")
    print(nl.gate_list_str(gates, n))
    print(f"output wire: {output}")
    print(f"NOT gates: {nc}")
    print("lean gates: " + nl.lean_gate_list(gates))
    ok, bad = nl.check_circuit(n, edges, gates, output)
    if nc > nots:
        print(f"RESULT: ENCODING BUG -- {nc} NOT gates, budget {nots}")
        return 3
    if not ok:
        print(f"RESULT: DECODING BUG -- {len(bad)} mismatched rows: {bad[:4]}")
        return 3
    print(f"RESULT: SAT s={s} nots<={nots} (actual NOTs {nc}) -- "
          f"independent simulator ACCEPTED on all {1 << n} inputs")
    return 0


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--graph", type=str, default="")
    ap.add_argument("--n", type=int, default=0)
    ap.add_argument("--edges", type=str, default="")
    ap.add_argument("--gates", type=int, required=True)
    ap.add_argument("--nots", type=int, default=0)
    ap.add_argument("--loose", action="store_true",
                    help="symmetry off, distinct-cols off: for HUNTING witnesses")
    ap.add_argument("--tight", action="store_true",
                    help="symmetry on, distinct-cols on: for PROVING unsat")
    ap.add_argument("--timeout", type=int, default=0)
    ap.add_argument("--tag", type=str, default="")
    ap.add_argument("--solver-arg", action="append", default=[])
    args = ap.parse_args(argv)

    if args.graph:
        n, edges = nl.GRAPHS[args.graph]
    else:
        n, edges = args.n, parse_edges(args.edges)
    if args.loose and args.tight:
        raise SystemExit("pick one of --loose / --tight")
    symmetry = bool(args.tight)
    distinct_cols = bool(args.tight)
    return run(n, edges, args.gates, args.nots, symmetry, distinct_cols,
               args.timeout or None, PNOT / "cnf", args.tag, args.solver_arg)


if __name__ == "__main__":
    sys.exit(main())
