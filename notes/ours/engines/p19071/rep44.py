#!/usr/bin/env python3
"""Exact synthesis of least AND/OR/NOT fan-in-two circuits REPRESENTING an n x m bipartite
graph on the one-a-side promise (PEqualNP.Represents.Represents).

n and m come from --n / --m and default to 4 and 4, which is the shape this file was
validated on (masks 854, 3824, 9999); nothing in the encoding below is shape-specific.

Adapted from $P/p18664/crown.py.  Two changes from that file:

  * the graph is an arbitrary mask: A u v = (mask >>> (m*u + v)) &&& 1, matching
    `fun u v : Fin n => (mask : Nat).testBit (m * u.val + v.val)`;
  * the gate basis is PEqualNP.MetaComplexity.FanInTwo, i.e. op in {and, or, not} with
    inputs.length <= 2, so NOT gates are allowed and counted.

Wire convention (read from PEqualNP/Defs/CircuitLowerBounds.lean):
    Circuit.wires C x = C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (w.getD . false))]) x
  wire i < N is input i, wire N + j is gate j, gate j sees wires 0 .. N+j-1 only, any other
  index reads false, Circuit.eval = (C.wires x).getD C.output false, C.size = gates.length.
  GateOp.eval: and l = l.all id (true on []), or l = l.any id (false on []),
  not l = !(l.headD false) (true on []).

NORMAL FORM, and why it contains every LEAST circuit (so an exact-size UNSAT sweep upward
from 1 is a real lower bound):

  Let C be a circuit of fewest gates with FanInTwo C and Represents A C.
  * A fan-in 0 gate is a constant (and -> true, or -> false, not -> true).  A constant can be
    folded out of every gate that reads it (an operand that reads false can be dropped from an
    OR and makes an AND constant false; an operand that reads true can be dropped from an AND
    and makes an OR constant true; NOT of a constant is a constant) and a constant false wire
    can be replaced everywhere by an out-of-range index, which reads false for free.  Every
    fold emits at most the same number of gates while deleting the constant gate, so the
    result is strictly smaller: impossible.
  * A fan-in 1 AND or OR gate is a copy of its operand; delete it and rewire its readers (and
    the output if needed) to the operand: strictly smaller.  Likewise a fan-in 2 AND or OR with
    two equal operands.
  * An AND or OR gate with an out-of-range operand (one that reads false) is a constant false
    or a copy: strictly smaller, as above.  A NOT gate with an out-of-range operand is the
    constant true: strictly smaller.
  * A NOT gate with two operands ignores the second, so it may be listed with one operand; this
    changes no value and no count.
  * A gate the output does not depend on can be deleted: strictly smaller.
  * The output wire is a gate wire.  An out-of-range output makes eval constantly false, and A
    is not constantly false; output = wire u < n makes eval (oneEach u' v) = decide (u' = u),
    independent of v, and output = wire n + v makes it independent of u.  (The caller checks
    that the given mask has a row that is not constant in v and a column that is not constant
    in u, and refuses otherwise.)
  * Every gate is then reachable from the output, so the last gate in the list IS the output
    gate: any other last gate is read by nobody and is not the output.

  Hence a least circuit has, after listing each NOT with one operand, exactly: s gates, each
  either `and`/`or` on two distinct in-range wires or `not` on one in-range wire, output the
  last gate, and every gate but the last read by a later gate.  That is the search space here.

OPTIONAL STRENGTHENINGS, all also consequences of leastness (so they keep the sweep valid):
  --distinct-cols : no two gates agree on all the constrained rows, and no gate agrees there
      with an input wire or with the constant false.  (Agreement lets a reader be rewired to
      the earlier wire -- or, for the constant false, to an out-of-range index -- after which
      the gate is unread and drops.)
  --symmetry (default on) : adjacent independent gates are sorted.  Swapping gate j and gate
      j+1 when gate j+1 does not read gate j is a valid relabelling, and each such swap
      strictly lowers the sequence of gate keys lexicographically, so some least circuit is a
      fixed point of the sorting.  Only j <= s-3 is swapped, so the output gate never moves.
"""

from __future__ import annotations

import argparse
import itertools
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

CONST_TRUE = "T"
CONST_FALSE = "F"
Term = object


@dataclass(frozen=True)
class Form:
    op: str              # "and" | "or" | "not"
    ins: Tuple[int, ...]  # (a, b) with a < b for and/or; (a,) for not

    def key(self) -> Tuple[int, int, int]:
        oprank = {"and": 0, "or": 1, "not": 2}[self.op]
        if len(self.ins) == 1:
            return (self.ins[0], -1, oprank)
        return (self.ins[1], self.ins[0], oprank)


@dataclass
class GateSpec:
    op: str
    inputs: List[int]


class CnfBuilder:
    def __init__(self) -> None:
        self.nvars = 0
        self.clauses: List[List[int]] = []

    def new_var(self) -> int:
        self.nvars += 1
        return self.nvars

    def add(self, terms: Sequence[Term]) -> None:
        lits: List[int] = []
        for t in terms:
            if isinstance(t, str):
                if t == CONST_TRUE:
                    return
                continue
            assert isinstance(t, int)
            lits.append(t)
        self.clauses.append(lits)

    def exactly_one(self, lits: Sequence[int]) -> None:
        self.clauses.append(list(lits))
        for x, y in itertools.combinations(lits, 2):
            self.clauses.append([-x, -y])

    def write(self, path: Path) -> None:
        with path.open("w", encoding="ascii") as fh:
            fh.write(f"p cnf {self.nvars} {len(self.clauses)}\n")
            fh.writelines(" ".join(str(x) for x in c) + " 0\n" for c in self.clauses)


def neg(t: Term) -> Term:
    if isinstance(t, str):
        return CONST_FALSE if t == CONST_TRUE else CONST_TRUE
    assert isinstance(t, int)
    return -t


def mask_rows(mask: int, n: int = 4, m: int = 4
              ) -> Tuple[int, List[Tuple[Tuple[bool, ...], bool]]]:
    """The rows of `Represents A C` for A u v = (mask).testBit (m*u + v).

    oneEach u v = List.ofFn (fun i : Fin n => decide (i = u))
                  ++ List.ofFn (fun j : Fin m => decide (j = v)),
    so wire u is left vertex u and wire n + v is right vertex v; N = n + m wires."""
    N = n + m
    rows: List[Tuple[Tuple[bool, ...], bool]] = []
    for u in range(n):
        for v in range(m):
            bits = tuple([i == u for i in range(n)] + [j == v for j in range(m)])
            rows.append((bits, bool((mask >> (m * u + v)) & 1)))
    return N, rows


def forms_for(top: int) -> List[Form]:
    fs = [Form("and", (a, b)) for b in range(top) for a in range(b)]
    fs += [Form("or", (a, b)) for b in range(top) for a in range(b)]
    fs += [Form("not", (a,)) for a in range(top)]
    fs.sort(key=lambda f: f.key())
    return fs


@dataclass
class Encoding:
    cnf: CnfBuilder
    N: int
    s: int
    forms: List[List[Form]]
    sel: List[Dict[Form, int]]
    val: List[List[int]]


def build(N: int, s: int, rows: List[Tuple[Tuple[bool, ...], bool]],
          symmetry: bool, distinct_cols: bool) -> Encoding:
    nrows = len(rows)
    cnf = CnfBuilder()

    forms = [forms_for(N + j) for j in range(s)]
    sel: List[Dict[Form, int]] = []
    for j in range(s):
        d = {f: cnf.new_var() for f in forms[j]}
        sel.append(d)
        cnf.exactly_one(list(d.values()))

    val = [[cnf.new_var() for _ in range(nrows)] for _ in range(s)]

    def wire_term(w: int, r: int) -> Term:
        if w < N:
            return CONST_TRUE if rows[r][0][w] else CONST_FALSE
        return val[w - N][r]

    for j in range(s):
        for f, sv in sel[j].items():
            for r in range(nrows):
                v = val[j][r]
                if f.op == "not":
                    ta = wire_term(f.ins[0], r)
                    cnf.add([-sv, -v, neg(ta)])
                    cnf.add([-sv, v, ta])
                else:
                    ta = wire_term(f.ins[0], r)
                    tb = wire_term(f.ins[1], r)
                    if f.op == "and":
                        cnf.add([-sv, -v, ta])
                        cnf.add([-sv, -v, tb])
                        cnf.add([-sv, v, neg(ta), neg(tb)])
                    else:
                        cnf.add([-sv, v, neg(ta)])
                        cnf.add([-sv, v, neg(tb)])
                        cnf.add([-sv, -v, ta, tb])

    # the output is the last gate; pin its column to the target
    for r in range(nrows):
        v = val[s - 1][r]
        cnf.clauses.append([v] if rows[r][1] else [-v])

    def reads(j: int, w: int) -> List[int]:
        return [sel[j][f] for f in forms[j] if w in f.ins]

    # every gate but the last is read by a later gate
    for j in range(s - 1):
        w = N + j
        lits = [x for k in range(j + 1, s) for x in reads(k, w)]
        cnf.clauses.append(lits)

    if symmetry:
        for j in range(s - 2):
            w = N + j
            readers = set(reads(j + 1, w))
            for f in forms[j]:
                kf = f.key()
                for g in forms[j + 1]:
                    if g.key() < kf and sel[j + 1][g] not in readers:
                        cnf.clauses.append([-sel[j][f], -sel[j + 1][g]])

    if distinct_cols:
        for j in range(s):
            for k in range(j):
                lits = []
                for r in range(nrows):
                    d = cnf.new_var()
                    cnf.clauses.append([-d, val[j][r], val[k][r]])
                    cnf.clauses.append([-d, -val[j][r], -val[k][r]])
                    lits.append(d)
                cnf.clauses.append(lits)
        for j in range(s):
            for w in range(N):
                cnf.clauses.append(
                    [(-val[j][r] if rows[r][0][w] else val[j][r]) for r in range(nrows)]
                )
            cnf.clauses.append([val[j][r] for r in range(nrows)])

    return Encoding(cnf, N, s, forms, sel, val)


def decode(enc: Encoding, assign: Dict[int, bool]) -> List[GateSpec]:
    gates: List[GateSpec] = []
    for j in range(enc.s):
        chosen: Optional[Form] = None
        for f, v in enc.sel[j].items():
            if assign.get(v, False):
                if chosen is not None:
                    raise ValueError(f"gate {j}: two selectors true")
                chosen = f
        if chosen is None:
            raise ValueError(f"gate {j}: no selector true")
        gates.append(GateSpec(chosen.op, list(chosen.ins)))
    return gates


def simulate(gates: Sequence[GateSpec], bits: Sequence[bool], output: int) -> bool:
    """Lean-faithful: Circuit.wires then getD output false."""
    w = list(bits)
    for g in gates:
        vals = [w[i] if 0 <= i < len(w) else False for i in g.inputs]
        if g.op == "and":
            w.append(all(vals))
        elif g.op == "or":
            w.append(any(vals))
        else:
            w.append(not (vals[0] if vals else False))
    return w[output] if 0 <= output < len(w) else False


def lean_gate_list(gates: Sequence[GateSpec]) -> str:
    parts = ["⟨GateOp." + g.op + ", [" + ", ".join(str(i) for i in g.inputs) + "]⟩"
             for g in gates]
    return "[" + ", ".join(parts) + "]"


def find_solver() -> str:
    for cand in ("cadical", "kissat", "cryptominisat5", "minisat"):
        p = shutil.which(cand)
        if p:
            return p
    for p2 in Path("/root/.elan/toolchains").glob("*/bin/cadical"):
        return str(p2)
    raise SystemExit("no SAT solver found")


def run_solver(solver: str, cnf_path: Path, timeout: Optional[int],
               extra: Sequence[str] = ()) -> Tuple[str, Dict[int, bool], float]:
    t0 = time.time()
    try:
        proc = subprocess.run([solver, *extra, str(cnf_path)], capture_output=True,
                              text=True, timeout=timeout, check=False)
    except subprocess.TimeoutExpired:
        return ("TIMEOUT", {}, time.time() - t0)
    dt = time.time() - t0
    status = "UNKNOWN"
    assign: Dict[int, bool] = {}
    for line in proc.stdout.splitlines():
        if line.startswith("s "):
            if "UNSATISFIABLE" in line:
                status = "UNSAT"
            elif "SATISFIABLE" in line:
                status = "SAT"
        elif line.startswith("v "):
            for tok in line[2:].split():
                k = int(tok)
                if k:
                    assign[abs(k)] = k > 0
    return (status, assign, dt)


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--mask", type=int, required=True)
    ap.add_argument("--n", type=int, default=4, help="left vertices (rows of the mask)")
    ap.add_argument("--m", type=int, default=4, help="right vertices (columns of the mask)")
    ap.add_argument("--gates", type=int, required=True, help="EXACT gate count")
    ap.add_argument("--no-symmetry", action="store_true")
    ap.add_argument("--distinct-cols", action="store_true")
    ap.add_argument("--timeout", type=int, default=0)
    ap.add_argument("--work", type=str, default="cnf")
    ap.add_argument("--solver", type=str, default="")
    ap.add_argument("--solver-arg", action="append", default=[],
                    help="extra flag passed to the solver, repeatable "
                         "(e.g. --solver-arg --sat).  Default: none, i.e. the "
                         "solver's own defaults, which is what was validated.")
    ap.add_argument("--tag", type=str, default="")
    args = ap.parse_args(argv)

    s = args.gates
    n, m = args.n, args.m
    if n < 1 or m < 1:
        raise SystemExit("--n and --m must be positive")
    if args.mask >> (n * m):
        raise SystemExit(f"mask has bits above {n * m}: wrong --n/--m for this mask")
    N, rows = mask_rows(args.mask, n, m)
    # the normal form needs the output to be a gate: check the mask allows no projection
    cols_ok = any(len({rows[m * u + v][1] for u in range(n)}) > 1 for v in range(m))
    rows_ok = any(len({rows[m * u + v][1] for v in range(m)}) > 1 for u in range(n))
    if not (cols_ok and rows_ok and any(w for _, w in rows)):
        raise SystemExit("mask is a projection or constant false: normal form not justified")

    enc = build(N, s, rows, not args.no_symmetry, args.distinct_cols)
    work = Path(args.work)
    work.mkdir(parents=True, exist_ok=True)
    name = (f"m{args.mask}_{n}x{m}_s{s}{'_nosym' if args.no_symmetry else ''}"
            f"{'_dc' if args.distinct_cols else ''}{args.tag}.cnf")
    cnf_path = work / name
    enc.cnf.write(cnf_path)
    print(f"mask={args.mask} shape={n}x{m} N={N} rows={len(rows)} gates={s} "
          f"symmetry={not args.no_symmetry} distinct_cols={args.distinct_cols} "
          f"vars={enc.cnf.nvars} clauses={len(enc.cnf.clauses)}", flush=True)

    solver = args.solver or find_solver()
    status, assign, dt = run_solver(solver, cnf_path, args.timeout or None,
                                    args.solver_arg)
    print(f"solver={solver} {' '.join(args.solver_arg)} status={status} "
          f"seconds={dt:.1f}", flush=True)

    if status != "SAT":
        if status == "TIMEOUT":
            print("RESULT: DID NOT RETURN (timeout) -- NOT a negative result")
            return 2
        if status == "UNSAT":
            print(f"RESULT: UNSAT  mask={args.mask} shape={n}x{m} gates={s}")
            return 0
        print("RESULT: solver gave no verdict")
        return 2

    gates = decode(enc, assign)
    output = N + s - 1
    bad = [(bits, want, simulate(gates, bits, output))
           for bits, want in rows if simulate(gates, bits, output) != want]
    print("gates:")
    for j, gg in enumerate(gates):
        print(f"  wire {N+j}: {gg.op} {gg.inputs}")
    print(f"output wire: {output}")
    print("lean gates: " + lean_gate_list(gates))
    if bad:
        print(f"RESULT: DECODING BUG -- {len(bad)} mismatched rows: {bad[:4]}")
        return 3
    print(f"RESULT: SAT  mask={args.mask} shape={n}x{m} gates={s} -- re-simulated on all "
          f"{len(rows)} oneEach rows")
    return 0


if __name__ == "__main__":
    sys.exit(main())
