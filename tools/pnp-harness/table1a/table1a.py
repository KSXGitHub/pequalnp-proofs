#!/usr/bin/env python3
"""Exact decision tool for the "Table 1a, 5 by 5, mask <N>" family of steps.

WHAT IT DECIDES
---------------
    PEqualNP.Represents.RepSizeAtMost
        (fun u v : Fin 5 => (<mask> : Nat).testBit (5 * u.val + v.val)) <budget>

i.e. "some circuit of AND and OR gates of fan-in at most two, with at most
<budget> gates, outputs A u v at every input `oneEach u v`".  The answer is
exact: SAT comes with a circuit (checked again by verify.py), UNSAT is a
complete exclusion of every circuit of that size.

INVOCATION (one solver process; run in the foreground)
-----------------------------------------------------
    python3 table1a.py --mask 7874358 --budget 10 --out /path/prefix

      --mask N      the Table 1a mask (bit 5*u+v is A u v, u = row = left vertex)
      --budget S    decide RepSizeAtMost A S.  Sizes 0,1,...,S are tried in turn;
                    the first that is SAT is the EXACT least size and its circuit
                    is written to <prefix>_<size>.json.  If every size up to S is
                    UNSAT the step "takes at least S+1 gates" is TRUE.
      --out PREFIX  where to write the witness (optional)
      --from N      skip sizes below N (only to resume a scan; a full scan from 0
                    is what proves a lower bound)
      --no-sym      drop the lexicographic symmetry break (slower, same answers;
                    use it to cross-check a surprising UNSAT)
      --no-count    drop the read-budget constraints (N5) (much slower, same answers)
      --solver NAME any python-sat solver, e.g. cadical195, glucose4, minisat22;
                    default cadical153.  Re-run a decisive UNSAT on a second one.

Then check the witness independently:

    python3 verify.py --mask 7874358 --circuit /path/prefix_10.json --budget 10

THE SEMANTICS, TRANSCRIBED FROM SOURCE
--------------------------------------
lean/PEqualNP/Defs/CircuitLowerBounds.lean
    Circuit = { gates : List Gate, output : Nat };  Gate = { op, inputs : List Nat }
    wires C x = C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (w.getD . false))]) x
      -> input bits are wires 0 .. 9; gate j is wire 10 + j; it may only read
         wires that already exist (a later/absent index reads `false`).
    eval C x = (wires C x).getD C.output false
    size C   = C.gates.length                 (inputs are free, every gate counts)
    GateOp.eval and l = l.all id   (true on the empty list)
    GateOp.eval or  l = l.any id   (false on the empty list)
lean/PEqualNP/Defs/MetaComplexityLgpMono.lean
    Monotone2 C = forall g in C.gates, g.op in {and, or} and g.inputs.length <= 2
lean/PEqualNP/Defs/Represents.lean
    oneEach u v  = ofFn (fun i : Fin 5 => decide (i = u)) ++ ofFn (fun j : Fin 5 => decide (j = v))
    Represents A C = forall u v, C.eval (oneEach u v) = A u v   (nothing asked elsewhere)
    RepSizeAtMost A s = exists C, Monotone2 C and C.size <= s and Represents A C

So: 10 input wires, 25 constrained inputs oneEach u v (u,v in Fin 5), wire u is
the left-vertex indicator and wire 5+v the right-vertex indicator.  Over those
25 points a wire is a SUBSET of the 5x5 grid; the 10 input wires are the 5 full
rows and the 5 full columns, an AND gate is intersection, an OR gate is union,
and the question is the least number of union/intersection steps that build the
set A out of the rows and columns.

WHY THE SEARCH SPACE IS COMPLETE
--------------------------------
Sizes are tried in increasing order, and at size `ng` only circuits in this
normal form are searched:

  (N0) ng = 0 is handled separately and exactly: a gateless circuit outputs
       wire `output`, so it represents A iff A is all false (output absent) or
       A u v = decide(u = w) or A u v = decide(v = w) for some w.
  (N1) every gate reads exactly two distinct already-existing wires, the smaller
       index first;
  (N2) the last gate is the output wire, and every other gate is read by a later
       gate;
  (N3) no gate is constant over the 25 points, and no two wires (input wires
       included) have the same value vector over the 25 points;
  (N4) [--sym, default] for i <= ng-3, if gate i+1 does not read gate i then
       (input pair, op) of gate i is lexicographically <= that of gate i+1.
  (N5) [--count, default] the read budget.  A circuit of ng gates has 2*ng read
       slots.  Each of the ng-1 non-output gates needs one (N2), and so does each
       input wire that `must_read_inputs` marks, say m of them.  So 2*ng >= ng-1+m,
       i.e. ng >= m-1: for a mask needing all ten wires this alone gives ng >= 9,
       with no search at all.  Beyond that the slack ng-(m-1) bounds how many reads
       may go anywhere else, which at ng = 9 forces a READ-ONCE FORMULA (every wire
       read exactly once) and at ng = 10 a formula with exactly one wire read twice.
       This is what makes sizes 9 and 10 decidable in seconds instead of hours.

Each of these holds for at least one SIZE-MINIMAL circuit, so UNSAT at every
size 0..S really does refute RepSizeAtMost A S:

  (N2) a gate that no later gate reads and that is not the output can be deleted,
       so in a minimal circuit of size >= 1 the last gate is read by nobody and
       must therefore be the output, and then every earlier gate is read later.
       (If the output were an input wire or absent, all gates would be unused and
       the least size would be 0, which (N0) tests.)
  (N3) `Represents` only looks at the 25 points, so if gate i has the same
       25-point vector as an earlier wire a, redirecting every read of gate i
       (and the output) to a leaves all 25 values unchanged and frees gate i:
       one gate fewer.  A gate constant `false` over the 25 points can likewise
       be replaced by an absent wire index (free), and a gate constant `true`
       can be dropped from the AND gates that read it and makes the OR gates
       that read it constant `true` in turn; iterating removes a gate.  Either
       way a minimal circuit has none, unless A itself is constant over the 25
       points -- and then (N0) already answers, so the tool refuses to use the
       normal form for a constant A.
  (N1) follows from (N3): fan-in 0 is a constant gate, and fan-in 1, a repeated
       wire, or a read of an absent wire makes the gate a copy of another wire
       or a constant.
  (N5) is the counting above; `must_read_inputs` carries its own proof.
  (N4) is a pure symmetry break.  Swapping two adjacent gates when the later one
       does not read the earlier one gives another circuit of the same size in
       the same normal form (the last gate, hence the output, is untouched
       because the break stops at i+1 = ng-2), and it exchanges the two keys at
       positions i and i+1 while leaving positions < i alone.  Hence the circuit
       whose key sequence is lexicographically least in the (finite) set of all
       normal-form circuits of size ng for A has no out-of-order adjacent
       independent pair, and it survives the break.

The encoding itself is the house selector encoding: one-hot selectors for the
two wires each gate reads, one op bit per gate, one value variable per wire per
constrained point, and the 25 output values pinned to A.
"""

from __future__ import annotations

import argparse
import itertools
import json
import pathlib
import sys
import time
from typing import Final

# python-sat ships no type stubs.
from pysat.card import CardEnc, EncType  # type: ignore[import-untyped]
from pysat.formula import IDPool  # type: ignore[import-untyped]
from pysat.solvers import Solver  # type: ignore[import-untyped]

NL: Final = 5
NR: Final = 5
NIN: Final = NL + NR
PTS: Final[list[tuple[int, int]]] = [(u, v) for u in range(NL) for v in range(NR)]
NPTS: Final = len(PTS)


def table(mask: int) -> list[list[bool]]:
    """A u v = mask.testBit (5 * u + v); rows are left vertices."""
    return [[bool((mask >> (NL * u + v)) & 1) for v in range(NR)] for u in range(NL)]


def input_wire_value(w: int, u: int, v: int) -> bool:
    """Bit w of `oneEach u v`: wires 0..4 are the left vertices, 5..9 the right."""
    return (w == u) if w < NL else ((w - NL) == v)


def zero_gate_witness(mask: int) -> dict[str, object] | None:
    """A gateless circuit representing A, if one exists (case (N0))."""
    a = table(mask)
    for out in [NIN, *list(range(NIN))]:  # NIN is an absent wire: constant false
        ok = all((input_wire_value(out, u, v) if out < NIN else False) == a[u][v] for u, v in PTS)
        if ok:
            return {"mask": mask, "size": 0, "gates": [], "output": out}
    return None


def must_read_inputs(mask: int) -> list[bool]:
    """Which of the 10 input wires every minimal circuit of size >= 1 has to read.

    The circuit is monotone, so x <= y implies eval x <= eval y.  Suppose no gate
    reads the left wire u.  `oneEach u v` and the input with only right wire v on
    differ in bit u alone, so every gate, and hence the output (which in a minimal
    circuit of size >= 1 is the last gate, never an input wire), takes the same
    value on both; and the second input is below `oneEach u' v` for every u'.
    Therefore A u v <= A u' v for all u', i.e. the left wire u can be unread only
    if every v with A u v also has a column of A that is all ones.  Dually for a
    right wire v and the all-ones rows of A.
    """
    a = table(mask)
    full_col = [all(a[u][v] for u in range(NL)) for v in range(NR)]
    full_row = [all(a[u][v] for v in range(NR)) for u in range(NL)]
    out: list[bool] = []
    for u in range(NL):  # left wire u
        out.append(not all(full_col[v] for v in range(NR) if a[u][v]))
    for v in range(NR):  # right wire 5 + v
        out.append(not all(full_row[u] for u in range(NL) if a[u][v]))
    return out


def at_least_c(nv: object, cls: list[list[int]], lits: list[int], cap: int, tag: object) -> list[int]:
    """Sequential-counter indicators `at least c of lits` for c = 1..cap.

    Only the direction `enough true lits -> indicator` is asserted, which is all an
    upper bound on the number of true indicators needs.
    """
    assert callable(nv)
    prev: list[int] = []  # prev[c-1] = at least c of the lits seen so far
    for k, lit in enumerate(lits):
        cur = [nv((tag, k, c)) for c in range(1, cap + 1)]
        for c in range(1, cap + 1):
            if prev:
                cls.append([-prev[c - 1], cur[c - 1]])
            if c == 1:
                cls.append([-lit, cur[0]])
            elif prev:
                cls.append([-lit, -prev[c - 2], cur[c - 1]])
        prev = cur
    return prev


def solve_size(
    mask: int, ng: int, sym: bool, count: bool, solver_name: str, desc: bool = False
) -> tuple[dict[str, object] | None, str]:
    """Search the normal form for a circuit of exactly `ng` gates representing A."""
    a = table(mask)
    pool = IDPool()
    cls: list[list[int]] = []

    def nv(key: object) -> int:
        return int(pool.id(key))

    nw = {i: NIN + i for i in range(ng)}  # wires visible to gate i
    op = {i: nv(("op", i)) for i in range(ng)}  # true = OR, false = AND
    sel = {(s, i, w): nv(("sel", s, i, w)) for i in range(ng) for s in (0, 1) for w in range(nw[i])}
    gval = {(i, p): nv(("g", i, p)) for i in range(ng) for p in range(NPTS)}
    sval = {(s, i, p): nv(("s", s, i, p)) for s in (0, 1) for i in range(ng) for p in range(NPTS)}

    def wire_val_lit(w: int, p: int) -> int | bool:
        """The value of wire w at point p: a literal for a gate, a constant for an input."""
        if w < NIN:
            return input_wire_value(w, PTS[p][0], PTS[p][1])
        return gval[(w - NIN, p)]

    # (N1) exactly one wire per side, and left index strictly below right index.
    for i in range(ng):
        for s in (0, 1):
            lits = [sel[(s, i, w)] for w in range(nw[i])]
            cls.append(lits)
            for x, y in itertools.combinations(lits, 2):
                cls.append([-x, -y])
        for wl in range(nw[i]):
            for wr in range(wl + 1):
                cls.append([-sel[(0, i, wl)], -sel[(1, i, wr)]])

    # (N2) every gate but the last is read by a later gate; the last is the output.
    for i in range(ng - 1):
        cls.append([sel[(s, j, NIN + i)] for j in range(i + 1, ng) for s in (0, 1)])

    # Gate semantics at every constrained point, and the 25 pinned outputs.
    for p in range(NPTS):
        for i in range(ng):
            for s in (0, 1):
                sv = sval[(s, i, p)]
                for w in range(nw[i]):
                    k = sel[(s, i, w)]
                    val = wire_val_lit(w, p)
                    if isinstance(val, bool):
                        cls.append([-k, sv] if val else [-k, -sv])
                    else:
                        cls.append([-k, -sv, val])
                        cls.append([-k, sv, -val])
            x, y, g, o = sval[(0, i, p)], sval[(1, i, p)], gval[(i, p)], op[i]
            # o -> g = x or y
            cls += [[-o, -g, x, y], [-o, g, -x], [-o, g, -y]]
            # not o -> g = x and y
            cls += [[o, -g, x], [o, -g, y], [o, g, -x, -y]]
        out = gval[(ng - 1, p)]
        cls.append([out] if a[PTS[p][0]][PTS[p][1]] else [-out])

    # (N3) no gate is constant over the 25 points ...
    for i in range(ng):
        cls.append([gval[(i, p)] for p in range(NPTS)])
        cls.append([-gval[(i, p)] for p in range(NPTS)])
    # ... and every pair of wires differs somewhere on the 25 points.
    for i in range(ng):
        for w in range(nw[i]):
            diffs: list[int] = []
            for p in range(NPTS):
                d = nv(("d", w, i, p))
                gb = gval[(i, p)]
                val = wire_val_lit(w, p)
                if isinstance(val, bool):
                    cls.append([-d, -gb] if val else [-d, gb])
                else:
                    cls.append([-d, val, gb])
                    cls.append([-d, -val, -gb])
                diffs.append(d)
            cls.append(diffs)

    # (N4) lexicographic break on adjacent independent gates, keys (right, left, op).
    if sym:
        # `desc` asks for the lexicographically GREATEST key sequence instead of the
        # least.  That is an equally valid break by the same argument, and running a
        # decisive UNSAT under both is a check on this constraint.
        for i in range(ng - 2):
            j = i + 1
            dep = [sel[(0, j, NIN + i)], sel[(1, j, NIN + i)]]  # gate j reads gate i
            hi, lo = (i, j) if not desc else (j, i)  # key(hi) may not exceed key(lo)
            for wh in range(nw[i]):  # right(hi) = wh
                for wl in range(wh):  # right(lo) = wl < wh is forbidden
                    cls.append([*dep, -sel[1, hi, wh], -sel[1, lo, wl]])
                tie = [*dep, -sel[(1, hi, wh)], -sel[(1, lo, wh)]]  # equal right inputs
                for lh in range(wh):  # left(hi) = lh < right(hi)
                    for ll in range(lh):  # left(lo) = ll < lh is forbidden
                        cls.append([*tie, -sel[0, hi, lh], -sel[0, lo, ll]])
                    # equal input pairs: and (false) must come before or (true)
                    cls.append([*tie, -sel[0, hi, lh], -sel[0, lo, lh], -op[hi], op[lo]])

    # (N5) the read budget.  There are 2*ng read slots.  Every non-output gate must
    # be read at least once (N2) and so must every input wire in `must_read_inputs`,
    # which is ng - 1 + m wires needing a read, so the slack is 2*ng - (ng - 1 + m).
    # Negative slack is an outright refutation; otherwise at most `slack` reads may
    # go anywhere beyond the one each of those wires needs.
    must = must_read_inputs(mask)
    m = sum(1 for b in must if b)
    slack = 2 * ng - (ng - 1 + m)
    if count:
        if slack < 0:
            line = (
                f"size {ng}: UNSAT by the read budget ({2 * ng} read slots, "
                f"{ng - 1} gates and {m} input wires must each be read)"
            )
            sys.stdout.write(line + "\n")
            sys.stdout.flush()
            return None, line
        surplus: list[int] = []
        for w in range(NIN + ng - 1):  # the last gate is read by nobody
            slots = [sel[(s, i, w)] for i in range(ng) for s in (0, 1) if w < nw[i]]
            req = 1 if (w >= NIN or must[w]) else 0
            if req == 1:
                cls.append(list(slots))  # at least one read
            cap = min(len(slots), req + slack + 1)
            if cap > req:
                ge = at_least_c(nv, cls, slots, cap, ("rc", w))
                surplus += ge[req:]
        if surplus:
            if slack == 0:
                for lit in surplus:
                    cls.append([-lit])
            else:
                enc = CardEnc.atmost(lits=surplus, bound=slack, vpool=pool, encoding=EncType.seqcounter)
                cls += [list(c) for c in enc.clauses]

    head = f"size {ng}: {pool.top} vars, {len(cls)} clauses, read slack {slack}"
    sys.stdout.write(head + "\n")
    sys.stdout.flush()
    t0 = time.time()
    with Solver(name=solver_name, bootstrap_with=cls) as solver:
        ok = bool(solver.solve())
        el = time.time() - t0
        line = f"size {ng}: {'SAT' if ok else 'UNSAT'} in {el:.2f}s ({solver_name})"
        sys.stdout.write(line + "\n")
        sys.stdout.flush()
        if not ok:
            return None, line
        model = {x for x in solver.get_model() if x > 0}

    gates: list[dict[str, object]] = []
    for i in range(ng):
        left = [w for w in range(nw[i]) if sel[(0, i, w)] in model]
        right = [w for w in range(nw[i]) if sel[(1, i, w)] in model]
        assert len(left) == 1 and len(right) == 1, (i, left, right)
        gates.append({"op": "or" if op[i] in model else "and", "inputs": [left[0], right[0]]})
    return {"mask": mask, "size": ng, "gates": gates, "output": NIN + ng - 1}, line


def main() -> int:
    ap = argparse.ArgumentParser(description="decide RepSizeAtMost for a Table 1a mask")
    ap.add_argument("--mask", type=int, required=True)
    ap.add_argument("--budget", type=int, required=True)
    ap.add_argument("--out", type=str, default="")
    ap.add_argument("--from", dest="start", type=int, default=0)
    ap.add_argument("--no-sym", dest="sym", action="store_false", default=True)
    ap.add_argument("--no-count", dest="count", action="store_false", default=True)
    ap.add_argument("--solver", type=str, default="cadical153")
    ap.add_argument("--sym-desc", dest="desc", action="store_true", default=False)
    args = ap.parse_args()

    mask: int = args.mask
    budget: int = args.budget
    a = table(mask)
    sys.stdout.write(f"mask {mask}: A u v = mask.testBit (5*u + v), rows = left vertices\n")
    for u in range(NL):
        sys.stdout.write("  " + " ".join(str(int(a[u][v])) for v in range(NR)) + "\n")
    ones = sum(1 for u, v in PTS if a[u][v])
    sys.stdout.write(f"  {ones} of the 25 constrained points are true\n")
    must = must_read_inputs(mask)
    names = [f"left {w}" if w < NL else f"right {w - NL}" for w in range(NIN)]
    need = [names[w] for w in range(NIN) if must[w]]
    sys.stdout.write(
        f"  input wires every minimal circuit must read: {len(need)} of {NIN}"
        + ("" if len(need) == NIN else f" ({', '.join(need)})")
        + f" -> read budget gives least size >= {max(0, len(need) - 1)}\n"
    )
    if ones in (0, NPTS):
        sys.stdout.write("A is constant on the 25 points; the normal form does not apply\n")
        return 2

    if args.start <= 0:
        got0 = zero_gate_witness(mask)
        sys.stdout.write(f"size 0: {'SAT' if got0 else 'UNSAT'}\n")
        if got0 is not None:
            sys.stdout.write(json.dumps(got0) + "\n")
            sys.stdout.write(f"\nRepSizeAtMost(mask={mask}, {budget}) = TRUE, least size 0\n")
            return 0

    for ng in range(max(1, args.start), budget + 1):
        got, _line = solve_size(mask, ng, args.sym, args.count, args.solver, args.desc)
        if got is not None:
            if args.out:
                p = pathlib.Path(args.out)
                dest = p.with_name(p.name + f"_{ng}.json")
                dest.write_text(json.dumps(got, indent=1) + "\n")
                sys.stdout.write(f"wrote {dest}\n")
            sys.stdout.write(json.dumps(got) + "\n")
            if args.start <= 0:
                sys.stdout.write(f"\nRepSizeAtMost(mask={mask}, {budget}) = TRUE; the EXACT least size is {ng}\n")
            else:
                sys.stdout.write(
                    f"\nRepSizeAtMost(mask={mask}, {budget}) = TRUE, witness of size {ng}; "
                    f"sizes below {args.start} were SKIPPED, so {ng} is an upper bound only\n"
                )
            return 0

    if args.start <= 0:
        sys.stdout.write(
            f"\nRepSizeAtMost(mask={mask}, {budget}) = FALSE; every size 0..{budget} is "
            f"excluded, so the least size is at least {budget + 1}\n"
        )
        return 1
    sys.stdout.write(
        f"\nno circuit of size {args.start}..{budget}; sizes below {args.start} were SKIPPED, "
        f"so this is NOT a decision of RepSizeAtMost(mask={mask}, {budget})\n"
    )
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
