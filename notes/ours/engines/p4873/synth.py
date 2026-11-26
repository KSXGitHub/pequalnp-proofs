#!/usr/bin/env python3
"""Exact circuit synthesis as SAT.

Given a Boolean function on `n` inputs (as a truth-table integer, bit `k` = value on the
input whose i-th bit is `(k >> i) & 1`, matching the PEqualNP convention
`sum i, if x i then 2^i else 0`), decide whether a straight-line circuit of exactly `s`
gates computes it, and if so print the gate list in the PEqualNP `Circuit` convention:

  wire i < n            -- input i
  wire n + j            -- gate j
  gate j may read wires 0 .. n+j-1 only
  output wire           -- n + s - 1 (the last gate)

Models
------
mono : AND / OR, fan-in exactly two, distinct operands.  Target predicate
       `PEqualNP.MetaComplexity.Monotone2` (op in {and,or}, inputs.length <= 2).
ao2  : AND / OR / NOT.  AND/OR have fan-in exactly two with distinct operands;
       NOT is written as `not [a, a]` so that `inputs.length = 2` holds, which keeps the
       gate list legal for `PEqualNP.TopForm.IsAO2` as well as for the looser
       `FanInTwo`-style predicates.

Why this normal form is complete (no solutions are lost)
-------------------------------------------------------
Let f be non-constant and computable by a circuit of the loose model (fan-in <= 2,
repeated operands allowed, reads of nonexistent wires returning false).  Walk the gates in
order keeping a map phi from each old wire to either a constant or a new wire:

  fan-in 0            -> and = true, or = false              (constant, emit nothing)
  fan-in 1            -> phi(gate) = phi(operand)            (copy,     emit nothing)
  an operand constant -> fold (x and true = x, x and false = false, ...)
  both operands equal -> copy
  otherwise           -> emit one gate with two distinct operands

The result computes the same function with at most as many gates and every gate has fan-in
exactly two with distinct operands (for `ao2`, additionally, a NOT gate reads one wire,
duplicated).  Dropping gates the output does not depend on and re-sorting topologically
puts the output last.  Hence the minimum size is found by sweeping `s` upwards, and an
UNSAT at `s` means no circuit of this normal form with exactly `s` gates exists.

Symmetry breaking (on by default, switch off with --no-symmetry)
----------------------------------------------------------------
* colex : consecutive gates j, j+1 (j <= s-3, i.e. excluding the output gate) have
  non-decreasing operand pairs in colex order.  Valid because a gate whose pair is colex
  smaller than its predecessor's cannot read its predecessor (that wire is the largest
  index available, so a pair containing it is colex maximal), so the two can be swapped.
* used  : every gate other than the output gate is read by some later gate.  Valid for a
  minimum-size circuit.
* nodup : no two gates have the same operand pair AND the same op (implied by colex
  being strict where independent); encoded as part of colex.
* nonot2: in `ao2`, no NOT gate reads a NOT gate (double negation is a copy).

Only the operand-ordering part of the normal form is unconditional; --no-symmetry keeps
that and drops the rest, which is the configuration to use for an UNSAT one wants to trust
without reading the argument above.
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

# A term in a clause: either a DIMACS literal, or a fixed constant.
CONST_TRUE = "T"
CONST_FALSE = "F"
Term = object  # int | str, kept loose for the helper below


@dataclass(frozen=True)
class Pair:
    """An operand pair of a gate: wire indices a <= b."""

    a: int
    b: int

    def colex_key(self) -> Tuple[int, int]:
        return (self.b, self.a)


@dataclass
class GateSpec:
    """A decoded gate."""

    op: str  # 'and' | 'or' | 'not'
    inputs: List[int]


class CnfBuilder:
    def __init__(self) -> None:
        self.nvars: int = 0
        self.clauses: List[List[int]] = []

    def new_var(self) -> int:
        self.nvars += 1
        return self.nvars

    def add(self, terms: Sequence[Term]) -> None:
        """Add a clause.  Terms may be ints (literals) or CONST_TRUE/CONST_FALSE."""
        lits: List[int] = []
        for t in terms:
            if isinstance(t, str):
                if t == CONST_TRUE:
                    return  # clause already satisfied
                continue  # CONST_FALSE contributes nothing
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
            out: List[str] = []
            for c in self.clauses:
                out.append(" ".join(str(x) for x in c) + " 0\n")
            fh.writelines(out)


def neg(t: Term) -> Term:
    if isinstance(t, str):
        return CONST_FALSE if t == CONST_TRUE else CONST_TRUE
    assert isinstance(t, int)
    return -t


@dataclass
class Encoding:
    cnf: CnfBuilder
    n: int
    s: int
    model: str
    pairs: List[List[Pair]]
    sel: List[Dict[Pair, int]]
    val: List[List[int]]  # val[j][row]
    is_and: List[int]
    is_not: List[int]
    encoding: str = "pair"
    sa: Optional[List[List[int]]] = None
    sb: Optional[List[List[int]]] = None


def build(
    n: int,
    s: int,
    rows: List[bool],
    model: str,
    symmetry: bool,
    encoding: str = "pair",
) -> Encoding:
    """Build the CNF.

    encoding='pair': one one-hot selector per ORDERED OPERAND PAIR.  Compact in variables
    and strong propagation, but the clause count grows like sum_j C(n+j,2) * 2^n, so it is
    the right choice for small n (say n <= 6).

    encoding='wire': two one-hot selectors per gate over single wires, plus an auxiliary
    value variable per (gate, operand, row).  The clause count grows like
    sum_j (n+j) * 2^n, which is smaller by a factor of about (n+s)/2 -- use this for large
    n (for n=10, s=17 it is ~1.4M clauses instead of ~17M).
    """
    if encoding == "wire":
        return build_wire(n, s, rows, model, symmetry)
    nrows = 1 << n
    assert len(rows) == nrows
    cnf = CnfBuilder()

    # operand pairs available to each gate
    pairs: List[List[Pair]] = []
    for j in range(s):
        top = n + j  # wires 0 .. n+j-1 are readable
        ps: List[Pair] = []
        for b in range(top):
            for a in range(b):
                ps.append(Pair(a, b))
            if model == "ao2":
                ps.append(Pair(b, b))  # NOT reads one wire, duplicated
        ps.sort(key=lambda p: p.colex_key())
        pairs.append(ps)

    sel: List[Dict[Pair, int]] = []
    for j in range(s):
        d: Dict[Pair, int] = {}
        for p in pairs[j]:
            d[p] = cnf.new_var()
        sel.append(d)
        cnf.exactly_one(list(d.values()))

    is_and: List[int] = [cnf.new_var() for _ in range(s)]
    is_not: List[int] = (
        [cnf.new_var() for _ in range(s)] if model == "ao2" else [0] * s
    )

    val: List[List[int]] = [[cnf.new_var() for _ in range(nrows)] for _ in range(s)]

    if model == "ao2":
        # a NOT gate reads a duplicated wire; an AND/OR gate reads two distinct wires
        for j in range(s):
            for p, v in sel[j].items():
                if p.a == p.b:
                    cnf.add([-v, is_not[j]])
                else:
                    cnf.add([-v, -is_not[j]])

    def wire_term(w: int, row: int) -> Term:
        """The value of wire w on the given row, as a clause term."""
        if w < n:
            return CONST_TRUE if ((row >> w) & 1) else CONST_FALSE
        g = w - n
        return val[g][row]

    for j in range(s):
        for p, selv in sel[j].items():
            for row in range(nrows):
                ta = wire_term(p.a, row)
                tb = wire_term(p.b, row)
                v = val[j][row]
                if model == "mono":
                    # is_and[j] -> v <-> a and b
                    cnf.add([-selv, -is_and[j], -v, ta])
                    cnf.add([-selv, -is_and[j], -v, tb])
                    cnf.add([-selv, -is_and[j], v, neg(ta), neg(tb)])
                    # not is_and[j] -> v <-> a or b
                    cnf.add([-selv, is_and[j], -v, ta, tb])
                    cnf.add([-selv, is_and[j], v, neg(ta)])
                    cnf.add([-selv, is_and[j], v, neg(tb)])
                else:
                    if p.a == p.b:
                        # NOT gate: v <-> not a
                        cnf.add([-selv, -v, neg(ta)])
                        cnf.add([-selv, v, ta])
                    else:
                        cnf.add([-selv, -is_and[j], -v, ta])
                        cnf.add([-selv, -is_and[j], -v, tb])
                        cnf.add([-selv, -is_and[j], v, neg(ta), neg(tb)])
                        cnf.add([-selv, is_and[j], -v, ta, tb])
                        cnf.add([-selv, is_and[j], v, neg(ta)])
                        cnf.add([-selv, is_and[j], v, neg(tb)])

    # the output wire is the last gate; pin its column to the target
    for row in range(nrows):
        v = val[s - 1][row]
        cnf.clauses.append([v] if rows[row] else [-v])

    if symmetry:
        # colex non-decreasing operand pairs among gates 0 .. s-2
        for j in range(s - 2):
            for p in pairs[j]:
                kp = p.colex_key()
                for q in pairs[j + 1]:
                    if q.colex_key() < kp:
                        cnf.clauses.append([-sel[j][p], -sel[j + 1][q]])
        # every gate but the output gate is read later
        for j in range(s - 1):
            w = n + j
            lits: List[int] = []
            for k in range(j + 1, s):
                for p in pairs[k]:
                    if p.a == w or p.b == w:
                        lits.append(sel[k][p])
            cnf.clauses.append(lits)
        if model == "ao2":
            # no NOT directly above a NOT
            for j in range(s):
                for p in sel[j]:
                    if p.a == p.b and p.a >= n:
                        k = p.a - n
                        cnf.clauses.append([-sel[j][p], -is_not[j], -is_not[k]])

    return Encoding(cnf, n, s, model, pairs, sel, val, is_and, is_not)


def build_wire(
    n: int,
    s: int,
    rows: List[bool],
    model: str,
    symmetry: bool,
) -> Encoding:
    """The scalable encoding: per-wire operand selectors and auxiliary operand values."""
    nrows = 1 << n
    assert len(rows) == nrows
    cnf = CnfBuilder()

    sa: List[List[int]] = []
    sb: List[List[int]] = []
    for j in range(s):
        top = n + j
        sa.append([cnf.new_var() for _ in range(top)])
        sb.append([cnf.new_var() for _ in range(top)])
        cnf.exactly_one(sa[j])
        cnf.exactly_one(sb[j])

    is_and: List[int] = [cnf.new_var() for _ in range(s)]
    is_not: List[int] = [cnf.new_var() for _ in range(s)] if model == "ao2" else [0] * s

    for j in range(s):
        top = n + j
        if model == "mono":
            # first operand strictly below the second
            for w in range(top):
                for w2 in range(w + 1):
                    cnf.clauses.append([-sa[j][w], -sb[j][w2]])
        else:
            # a NOT gate reads one wire twice; an AND/OR gate reads two distinct wires
            for w in range(top):
                cnf.clauses.append([-is_not[j], -sa[j][w], sb[j][w]])
                cnf.clauses.append([-is_not[j], sa[j][w], -sb[j][w]])
                for w2 in range(w + 1):
                    cnf.clauses.append([is_not[j], -sa[j][w], -sb[j][w2]])

    val: List[List[int]] = [[cnf.new_var() for _ in range(nrows)] for _ in range(s)]
    aval: List[List[int]] = [[cnf.new_var() for _ in range(nrows)] for _ in range(s)]
    bval: List[List[int]] = [[cnf.new_var() for _ in range(nrows)] for _ in range(s)]

    # tie the auxiliary operand values to the selected wires
    for j in range(s):
        for w in range(n + j):
            for row in range(nrows):
                if w < n:
                    bit = bool((row >> w) & 1)
                    cnf.clauses.append(
                        [-sa[j][w], aval[j][row] if bit else -aval[j][row]]
                    )
                    cnf.clauses.append(
                        [-sb[j][w], bval[j][row] if bit else -bval[j][row]]
                    )
                else:
                    src = val[w - n][row]
                    cnf.clauses.append([-sa[j][w], -aval[j][row], src])
                    cnf.clauses.append([-sa[j][w], aval[j][row], -src])
                    cnf.clauses.append([-sb[j][w], -bval[j][row], src])
                    cnf.clauses.append([-sb[j][w], bval[j][row], -src])

    # gate semantics, once per (gate, row)
    for j in range(s):
        for row in range(nrows):
            a, b, v = aval[j][row], bval[j][row], val[j][row]
            if model == "mono":
                cnf.clauses.append([-is_and[j], -v, a])
                cnf.clauses.append([-is_and[j], -v, b])
                cnf.clauses.append([-is_and[j], v, -a, -b])
                cnf.clauses.append([is_and[j], -v, a, b])
                cnf.clauses.append([is_and[j], v, -a])
                cnf.clauses.append([is_and[j], v, -b])
            else:
                nn = is_not[j]
                cnf.clauses.append([-nn, -v, -a])
                cnf.clauses.append([-nn, v, a])
                cnf.clauses.append([nn, -is_and[j], -v, a])
                cnf.clauses.append([nn, -is_and[j], -v, b])
                cnf.clauses.append([nn, -is_and[j], v, -a, -b])
                cnf.clauses.append([nn, is_and[j], -v, a, b])
                cnf.clauses.append([nn, is_and[j], v, -a])
                cnf.clauses.append([nn, is_and[j], v, -b])

    for row in range(nrows):
        v = val[s - 1][row]
        cnf.clauses.append([v] if rows[row] else [-v])

    if symmetry:
        # colex non-decreasing operand pairs among gates 0 .. s-2:
        # forbid b(j+1) < b(j), and, for equal b, a(j+1) < a(j)
        for j in range(s - 2):
            topj = n + j
            for w in range(topj):
                for w2 in range(w):
                    cnf.clauses.append([-sb[j][w], -sb[j + 1][w2]])
                for wa in range(topj):
                    for wa2 in range(wa):
                        cnf.clauses.append(
                            [-sb[j][w], -sb[j + 1][w], -sa[j][wa], -sa[j + 1][wa2]]
                        )
        # every gate but the output gate is read later
        for j in range(s - 1):
            w = n + j
            lits: List[int] = []
            for k in range(j + 1, s):
                lits.append(sa[k][w])
                lits.append(sb[k][w])
            cnf.clauses.append(lits)
        if model == "ao2":
            # no NOT directly above a NOT
            for j in range(s):
                for k in range(j):
                    cnf.clauses.append([-sa[j][n + k], -is_not[j], -is_not[k]])

    return Encoding(
        cnf, n, s, model, [], [], val, is_and, is_not, "wire", sa, sb
    )


def decode(enc: Encoding, assign: Dict[int, bool]) -> List[GateSpec]:
    if enc.encoding == "wire":
        assert enc.sa is not None and enc.sb is not None
        out: List[GateSpec] = []
        for j in range(enc.s):
            wa = [w for w in range(enc.n + j) if assign.get(enc.sa[j][w], False)]
            wb = [w for w in range(enc.n + j) if assign.get(enc.sb[j][w], False)]
            if len(wa) != 1 or len(wb) != 1:
                raise ValueError(f"gate {j}: selectors {wa} {wb}")
            if enc.model == "ao2" and assign.get(enc.is_not[j], False):
                out.append(GateSpec("not", [wa[0], wb[0]]))
            else:
                op = "and" if assign.get(enc.is_and[j], False) else "or"
                out.append(GateSpec(op, [wa[0], wb[0]]))
        return out
    gates: List[GateSpec] = []
    for j in range(enc.s):
        chosen: Optional[Pair] = None
        for p, v in enc.sel[j].items():
            if assign.get(v, False):
                if chosen is not None:
                    raise ValueError(f"gate {j}: two selectors true")
                chosen = p
        if chosen is None:
            raise ValueError(f"gate {j}: no selector true")
        if enc.model == "ao2" and assign.get(enc.is_not[j], False):
            gates.append(GateSpec("not", [chosen.a, chosen.b]))
        else:
            op = "and" if assign.get(enc.is_and[j], False) else "or"
            gates.append(GateSpec(op, [chosen.a, chosen.b]))
    return gates


def simulate(gates: Sequence[GateSpec], n: int, output: int, row: int) -> bool:
    """Independent simulator, following PEqualNP.CircuitLowerBounds.Circuit.wires:
    fold over the gates, each appending one wire; a read of a wire that does not exist
    yet returns false; the value is the output wire, false if it does not exist."""
    w: List[bool] = [bool((row >> i) & 1) for i in range(n)]
    for g in gates:
        vals = [w[i] if 0 <= i < len(w) else False for i in g.inputs]
        if g.op == "and":
            r = all(vals)
        elif g.op == "or":
            r = any(vals)
        elif g.op == "not":
            r = not (vals[0] if vals else False)
        else:
            raise ValueError(f"bad op {g.op}")
        w.append(r)
    return w[output] if 0 <= output < len(w) else False


def lean_gate_list(gates: Sequence[GateSpec]) -> str:
    parts = [
        "⟨GateOp." + g.op + ", [" + ", ".join(str(i) for i in g.inputs) + "]⟩"
        for g in gates
    ]
    return "[" + ", ".join(parts) + "]"


def target_rows(n: int, table: int) -> List[bool]:
    return [bool((table >> k) & 1) for k in range(1 << n)]


def find_solver() -> str:
    for cand in ("cadical", "kissat", "cryptominisat5", "minisat"):
        p = shutil.which(cand)
        if p:
            return p
    # the Lean toolchain ships one
    for p2 in Path("/root/.elan/toolchains").glob("*/bin/cadical"):
        return str(p2)
    raise SystemExit("no SAT solver found")


def run_solver(solver: str, cnf_path: Path, timeout: Optional[int]) -> Tuple[str, Dict[int, bool], float]:
    cmd = [solver, str(cnf_path)]
    t0 = time.time()
    try:
        proc = subprocess.run(
            cmd, capture_output=True, text=True, timeout=timeout, check=False
        )
    except subprocess.TimeoutExpired:
        return ("TIMEOUT", {}, time.time() - t0)
    dt = time.time() - t0
    status = "UNKNOWN"
    assign: Dict[int, bool] = {}
    for line in proc.stdout.splitlines():
        if line.startswith("s "):
            if "SATISFIABLE" in line and "UNSAT" not in line:
                status = "SAT"
            elif "UNSATISFIABLE" in line:
                status = "UNSAT"
        elif line.startswith("v "):
            for tok in line[2:].split():
                k = int(tok)
                if k == 0:
                    continue
                assign[abs(k)] = k > 0
    return (status, assign, dt)


def parse_int(text: str) -> int:
    return int(text, 0)


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(description="exact circuit synthesis as SAT")
    ap.add_argument("--n", type=int, required=True, help="number of inputs")
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--target", type=str, help="truth table as an integer (0x.. allowed)")
    g.add_argument(
        "--target-expr",
        type=str,
        help="python expression over x (a list of 0/1) giving the value of each row",
    )
    ap.add_argument("--gates", type=int, required=True, help="exact number of gates")
    ap.add_argument("--model", choices=("mono", "ao2"), default="mono")
    ap.add_argument(
        "--encoding",
        choices=("pair", "wire"),
        default="pair",
        help="pair: one selector per operand pair (small n); wire: per-wire selectors (large n)",
    )
    ap.add_argument("--no-symmetry", action="store_true")
    ap.add_argument("--timeout", type=int, default=0, help="solver timeout in seconds, 0 = none")
    ap.add_argument("--work", type=str, default=".", help="directory for the cnf file")
    ap.add_argument("--solver", type=str, default="", help="path to the SAT solver")
    args = ap.parse_args(argv)

    n: int = args.n
    s: int = args.gates
    nrows = 1 << n

    if args.target is not None:
        table = parse_int(args.target)
        rows = target_rows(n, table)
    else:
        rows = []
        for k in range(nrows):
            x = [(k >> i) & 1 for i in range(n)]
            rows.append(bool(eval(args.target_expr, {"__builtins__": {}}, {"x": x})))
        table = sum((1 << k) for k in range(nrows) if rows[k])

    enc = build(n, s, rows, args.model, not args.no_symmetry, args.encoding)
    work = Path(args.work)
    work.mkdir(parents=True, exist_ok=True)
    cnf_path = (
        work
        / f"synth_n{n}_s{s}_{args.model}_{args.encoding}"
        f"{'_nosym' if args.no_symmetry else ''}.cnf"
    )
    enc.cnf.write(cnf_path)
    print(
        f"n={n} gates={s} model={args.model} encoding={args.encoding} "
        f"symmetry={not args.no_symmetry} "
        f"table=0x{table:x} vars={enc.cnf.nvars} clauses={len(enc.cnf.clauses)}",
        flush=True,
    )

    solver = args.solver or find_solver()
    status, assign, dt = run_solver(solver, cnf_path, args.timeout or None)
    print(f"solver={solver} status={status} seconds={dt:.1f}", flush=True)

    if status != "SAT":
        if status == "TIMEOUT":
            print("RESULT: DID NOT RETURN (timeout) -- this is NOT a negative result")
        elif status == "UNSAT":
            print(f"RESULT: UNSAT at {s} gates")
        else:
            print("RESULT: solver gave no verdict")
        return 0 if status == "UNSAT" else 2

    gates = decode(enc, assign)
    output = n + s - 1
    bad = [k for k in range(nrows) if simulate(gates, n, output, k) != rows[k]]
    print("gates:")
    for j, gg in enumerate(gates):
        print(f"  wire {n+j}: {gg.op} {gg.inputs}")
    print(f"output wire: {output}")
    print("lean: " + lean_gate_list(gates))
    if bad:
        print(f"RESULT: DECODING BUG -- mismatch on rows {bad}")
        return 3
    print(f"RESULT: SAT at {s} gates, independently verified on all {nrows} rows")
    return 0


if __name__ == "__main__":
    sys.exit(main())
