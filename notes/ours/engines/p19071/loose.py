#!/usr/bin/env python3
"""A SECOND, independent CNF for the same question, over the FULL loose FanInTwo model.

Written from the Lean definitions again rather than from rep44.py, and deliberately NOT in
the normal form: no leastness argument is used anywhere here.

PEqualNP.MetaComplexity.FanInTwo C says every gate has op in {and, or, not} and
inputs.length <= 2.  PEqualNP.CircuitLowerBounds:
  GateOp.eval and l = l.all id        (true on [])
  GateOp.eval or  l = l.any id        (false on [])
  GateOp.eval not l = !(l.headD false) (true on [])
  Circuit.wires C x = C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (w.getD . false))]) x
  Circuit.eval  C x = (C.wires x).getD C.output false
  Circuit.size  C   = C.gates.length
So a gate of gate index j sees wires 0 .. N+j-1; every other index reads false.  Writing
`top = N + j` and letting `a`, `b` range over 0 .. top-1, the COMPLETE list of value
functions a loose gate can have is

  TRUE        (and [], not [], not [k] for k out of range)
  FALSE       (or [], or [k] / and [a,k] / ... collapsing to false)
  COPY a      (and [a], or [a], or [a,k] with k out of range, and [a,a], or [a,a])
  NOT a       (not [a], not [a,b])
  AND a b     (and [a,b], a /= b)
  OR  a b     (or  [a,b], a /= b)

and every one of those is realised by an actual FanInTwo gate, so this behaviour set is
exactly the loose model.  The output wire ranges over 0 .. N+s-1 AND over "out of range"
(value false), again exactly as Circuit.eval allows.

Monotone in the size, with no normal form needed: a circuit of k < s gates becomes one of
exactly s gates by appending s-k gates `or []` at the end, which changes no earlier wire and
leaves the output index valid.  So UNSAT at exactly s gates here means: no FanInTwo circuit
with AT MOST s gates represents the graph.
"""

from __future__ import annotations

import argparse
import itertools
import shutil
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

Behav = Tuple  # ("T",) | ("F",) | ("C", a) | ("N", a) | ("A", a, b) | ("O", a, b)


def rows_of(mask: int) -> Tuple[int, List[Tuple[List[bool], bool]]]:
    """oneEach u v = List.ofFn (fun i : Fin 4 => decide (i = u))
                     ++ List.ofFn (fun j : Fin 4 => decide (j = v))
       A u v = (mask : Nat).testBit (4 * u + v)"""
    out = []
    for u in range(4):
        for v in range(4):
            x = [i == u for i in range(4)] + [j == v for j in range(4)]
            out.append((x, ((mask >> (4 * u + v)) & 1) == 1))
    return 8, out


def behaviours(top: int) -> List[Behav]:
    bs: List[Behav] = [("T",), ("F",)]
    bs += [("C", a) for a in range(top)]
    bs += [("N", a) for a in range(top)]
    bs += [("A", a, b) for a, b in itertools.combinations(range(top), 2)]
    bs += [("O", a, b) for a, b in itertools.combinations(range(top), 2)]
    return bs


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--mask", type=int, required=True)
    ap.add_argument("--gates", type=int, required=True)
    ap.add_argument("--timeout", type=int, default=0)
    ap.add_argument("--work", type=str, default="cnf2")
    args = ap.parse_args(argv)

    s = args.gates
    N, rows = rows_of(args.mask)
    nr = len(rows)

    nv = 0
    clauses: List[List[int]] = []

    def nxt() -> int:
        nonlocal nv
        nv += 1
        return nv

    beh = [behaviours(N + j) for j in range(s)]
    sel = [{b: nxt() for b in beh[j]} for j in range(s)]
    for j in range(s):
        lits = list(sel[j].values())
        clauses.append(lits)
        for p, q in itertools.combinations(lits, 2):
            clauses.append([-p, -q])

    val = [[nxt() for _ in range(nr)] for _ in range(s)]

    TRUE, FALSE = "T", "F"

    def wire(w: int, r: int):
        if w < N:
            return TRUE if rows[r][0][w] else FALSE
        if w < N + s:
            return val[w - N][r]
        return FALSE

    def add(ls: Sequence) -> None:
        o: List[int] = []
        for t in ls:
            if t == TRUE:
                return
            if t == FALSE:
                continue
            o.append(t)
        clauses.append(o)

    def nt(t):
        if t == TRUE:
            return FALSE
        if t == FALSE:
            return TRUE
        return -t

    for j in range(s):
        for b, sv in sel[j].items():
            for r in range(nr):
                v = val[j][r]
                if b[0] == "T":
                    clauses.append([-sv, v])
                elif b[0] == "F":
                    clauses.append([-sv, -v])
                elif b[0] == "C":
                    ta = wire(b[1], r)
                    add([-sv, -v, ta])
                    add([-sv, v, nt(ta)])
                elif b[0] == "N":
                    ta = wire(b[1], r)
                    add([-sv, -v, nt(ta)])
                    add([-sv, v, ta])
                elif b[0] == "A":
                    ta, tb = wire(b[1], r), wire(b[2], r)
                    add([-sv, -v, ta])
                    add([-sv, -v, tb])
                    add([-sv, v, nt(ta), nt(tb)])
                else:
                    ta, tb = wire(b[1], r), wire(b[2], r)
                    add([-sv, v, nt(ta)])
                    add([-sv, v, nt(tb)])
                    add([-sv, -v, ta, tb])

    # the output: any wire, or out of range (which reads false)
    outs = {w: nxt() for w in list(range(N + s)) + [-1]}
    lits = list(outs.values())
    clauses.append(lits)
    for p, q in itertools.combinations(lits, 2):
        clauses.append([-p, -q])
    for w, ov in outs.items():
        for r in range(nr):
            t = FALSE if w < 0 else wire(w, r)
            add([-ov, t] if rows[r][1] else [-ov, nt(t)])

    work = Path(args.work)
    work.mkdir(parents=True, exist_ok=True)
    cnf = work / f"loose_m{args.mask}_s{s}.cnf"
    with cnf.open("w", encoding="ascii") as fh:
        fh.write(f"p cnf {nv} {len(clauses)}\n")
        fh.writelines(" ".join(str(x) for x in c) + " 0\n" for c in clauses)
    print(f"LOOSE model: mask={args.mask} gates(exactly)={s} rows={nr} "
          f"vars={nv} clauses={len(clauses)}", flush=True)

    solver = shutil.which("cadical") or next(
        (str(p) for p in Path("/root/.elan/toolchains").glob("*/bin/cadical")), "")
    if not solver:
        raise SystemExit("no solver")
    t0 = time.time()
    try:
        proc = subprocess.run([solver, str(cnf)], capture_output=True, text=True,
                              timeout=args.timeout or None, check=False)
    except subprocess.TimeoutExpired:
        print(f"RESULT: DID NOT RETURN (timeout after {time.time()-t0:.0f}s) -- NOT UNSAT")
        return 2
    dt = time.time() - t0
    assign: Dict[int, bool] = {}
    status = "UNKNOWN"
    for line in proc.stdout.splitlines():
        if line.startswith("s "):
            status = "UNSAT" if "UNSATISFIABLE" in line else (
                "SAT" if "SATISFIABLE" in line else status)
        elif line.startswith("v "):
            for tok in line[2:].split():
                k = int(tok)
                if k:
                    assign[abs(k)] = k > 0
    print(f"solver={solver} status={status} seconds={dt:.1f}")
    if status == "UNSAT":
        print(f"RESULT: UNSAT  mask={args.mask} at most {s} gates (loose model, padding)")
        return 0
    if status != "SAT":
        print("RESULT: no verdict")
        return 2
    gates = []
    for j in range(s):
        got = [b for b, v in sel[j].items() if assign.get(v, False)]
        assert len(got) == 1, (j, got)
        gates.append(got[0])
    ow = [w for w, v in outs.items() if assign.get(v, False)]
    print(f"behaviours: {gates}\noutput wire: {ow}")
    print(f"RESULT: SAT  mask={args.mask} gates={s}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
