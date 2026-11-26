#!/usr/bin/env python3
"""Settle any TWO-LIT row of the desk, with the controls that make the answer trustworthy.

THE FAMILY. The desk posts rows of the form

  exists C, FanInTwo C and C.size <= B and
    forall i j : Fin n, C.eval (List.ofFn fun k : Fin n => decide (k = i or k = j))
      = (M : Nat).testBit (n * min i.val j.val + max i.val j.val)

so only the indicator vectors of the unordered pairs are constrained - n*(n+1)/2
of them, i = j included, which is the weight-one vector e_i. Off that set the
circuit is free, as on a promise row. Three have been handed to us so far
(L-meta-23192, L-meta-24013, L-meta-24274) and each was a copy-and-edit of the
last, which is how a wrong constant slips in. Hence one tool.

WHAT MAKES IT TRUSTWORTHY. Every one of these sketches hands over a circuit the
desk already holds, one or two gates above what it asks for. That circuit is an
EXTERNAL check on the row construction, available before any search: if the rows
do not accept it, the reading of the function is wrong and an UNSAT would mean
nothing. It doubles as the positive control at a size known satisfiable, which is
what makes a smaller UNSAT believable.

PADDING DOES NOT APPLY HERE. On a monotone row, one loose UNSAT at the budget
rules out every smaller size, because a circuit of size k extends to k+1 by
appending `c op a` after its last gate `c = a op b`. These rows are FanInTwo and
their known circuits often END in a NOT - 24013's does - and `NOT a` cannot be
padded that way. So every size below the budget is swept explicitly.

USAGE
  twolit.py --mask M --n N --budget B --desk "or:3,4;or:5,6;not:7;and:2,8;..."

The --desk string is the sketch's gate list in order, each gate `op:operands`,
with wires numbered as the sketch does: inputs 0..n-1, gate k on wire n+k, the
output the last gate.
"""

from __future__ import annotations

import argparse
import pathlib
import sys
from typing import Final

ENGINE: Final = pathlib.Path(
    "/tmp/claude-0/-home-user-pequalnp-proofs/731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/pnp/p20508"
)
sys.path.insert(0, str(ENGINE))

import rep44m as E  # noqa: E402

WORK: Final = pathlib.Path(
    "/tmp/claude-0/-home-user-pequalnp-proofs/731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/twolit"
)


def rows(mask: int, n: int) -> list[tuple[tuple[bool, ...], bool]]:
    out: list[tuple[tuple[bool, ...], bool]] = []
    for a in range(n):
        for b in range(a, n):
            bits = tuple(k in (a, b) for k in range(n))
            out.append((bits, bool((mask >> (n * a + b)) & 1)))
    return out


def parse_desk(spec: str) -> list[E.GateSpec]:
    gates: list[E.GateSpec] = []
    for part in spec.split(";"):
        part = part.strip()
        if not part:
            continue
        op, _, ins = part.partition(":")
        gates.append(E.GateSpec(op.strip(), [int(t) for t in ins.split(",") if t.strip()]))
    return gates


#: The sketch writes its circuit as `OR(3,4), AND(0,5), NOT(7), ...` in order.
GATE_RE: Final = __import__("re").compile(r"\b(OR|AND|NOT)\(\s*(\d+)\s*(?:,\s*(\d+)\s*)?\)")


def from_step(step_id: str) -> tuple[int, int, int, str]:
    """(mask, n, budget, desk-spec) read from the step's own record.

    Reading these off a sketch BY HAND is how a wrong constant gets into a run,
    and it has already happened once in this project with a budget taken from a
    row title instead of its statement. So the mask, the number of points and the
    budget come from the posted STATEMENT, and the control circuit from the
    sketch, parsed rather than retyped.
    """
    import json
    import re

    rec = pathlib.Path(f"/home/user/pequalnp-proofs/tools/pnp-harness/steps/{step_id}.json")
    d = json.load(open(rec))
    gap = d["gap"]
    stmt = str(gap.get("statement", ""))
    n = int(re.search(r"Fin (\d+)", stmt).group(1))  # type: ignore[union-attr]
    budget = int(re.search(r"C\.size ≤ (\d+)", stmt).group(1))  # type: ignore[union-attr]
    mask = int(re.search(r"\((\d+) : ℕ\)\.testBit", stmt).group(1))  # type: ignore[union-attr]
    spec = ";".join(
        f"{op.lower()}:{b}" + (f",{c}" if c else "")
        for op, b, c in GATE_RE.findall(str(gap.get("sketch", "")))
    )
    return mask, n, budget, spec


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--step", type=str, default="", help="read mask, n, budget and the control circuit from this step id")
    ap.add_argument("--mask", type=int)
    ap.add_argument("--n", type=int)
    ap.add_argument("--budget", type=int)
    ap.add_argument("--desk", type=str, default="", help="the sketch's gate list, op:a,b;...")
    ap.add_argument("--seconds", type=int, default=600)
    a = ap.parse_args(argv)
    if a.step:
        a.mask, a.n, a.budget, spec = from_step(a.step)
        a.desk = a.desk or spec
        sys.stdout.write(f"{a.step}: mask {a.mask}, {a.n} points, budget {a.budget}\n")
        sys.stdout.write(f"  control circuit from the sketch: {a.desk or '(none found)'}\n")
    if a.mask is None or a.n is None or a.budget is None:
        sys.stderr.write("need --step, or all of --mask --n --budget\n")
        return 2

    rs = rows(a.mask, a.n)
    sys.stdout.write(f"mask {a.mask} on {a.n} points, {len(rs)} constrained rows, budget {a.budget}\n")
    for u in range(a.n):
        sys.stdout.write(
            "    "
            + "".join(
                "1" if (a.mask >> (a.n * min(u, v) + max(u, v))) & 1 else "." for v in range(a.n)
            )
            + "\n"
        )

    control_size = 0
    if a.desk:
        desk = parse_desk(a.desk)
        ow = a.n + len(desk) - 1
        miss = [1 for bits, want in rs if E.simulate(desk, bits, ow) != want]
        if miss:
            sys.stdout.write(
                f"  CONTROL FAILED: the desk's own {len(desk)}-gate circuit misses {len(miss)}"
                f" of {len(rs)} rows. The row construction is wrong; stopping.\n"
            )
            return 2
        control_size = len(desk)
        sys.stdout.write(
            f"  CONTROL PASSED: the desk's {control_size}-gate circuit satisfies all {len(rs)} rows\n"
        )

    wants = [w for _, w in rs]
    if all(wants) or not any(wants):
        sys.stdout.write("  target is CONSTANT here; the engine's normal form is not justified\n")
        return 2
    for w in range(a.n):
        if all(bits[w] == want for bits, want in rs):
            sys.stdout.write(f"  target equals input {w} on every row; normal form not justified\n")
            return 2
    sys.stdout.write("  target is neither constant nor a projection\n\n")

    WORK.mkdir(parents=True, exist_ok=True)
    order = ([control_size] if control_size else []) + list(range(a.budget, 0, -1))
    saw_control = not control_size
    win: int | None = None
    for g in order:
        enc = E.build(a.n, g, rs, False, False, False)  # loose: hunting
        path = WORK / f"m{a.mask}_n{a.n}_s{g}.cnf"
        enc.cnf.write(path)
        status, assign, dt = E.run_solver(E.find_solver(), path, a.seconds)
        tag = "  (control)" if g == control_size and not saw_control else ""
        sys.stdout.write(f"  exactly {g} gates: {status} in {dt:.1f}s{tag}\n")
        if status == "SAT":
            got = E.decode(enc, assign)
            ow = a.n + len(got) - 1
            if [1 for bits, want in rs if E.simulate(got, bits, ow) != want]:
                sys.stdout.write("    DECODE MISMATCH - not reporting this\n")
                continue
            if g == control_size and not saw_control:
                saw_control = True
                continue
            # A SAT at or below the budget is the WIN; above it is only a control.
            if g <= a.budget:
                win = g
                sys.stdout.write(
                    f"\n  *** WIN: {g} GATES, re-simulated on all {len(rs)} rows ***\n"
                    f"  lean gates: {E.lean_gate_list(got)}\n  output wire: {ow}\n"
                )
                (WORK / f"witness_m{a.mask}_s{g}.txt").write_text(
                    f"{E.lean_gate_list(got)}\noutput wire {ow}\n"
                )
                break
        elif status != "UNSAT":
            sys.stdout.write(
                f"    {status} is NOT an UNSAT and must not be reported as one; stopping the sweep\n"
            )
            return 1
    if not saw_control:
        sys.stdout.write(
            "\n  the control did NOT return SAT at a size known to be satisfiable, so this\n"
            "  encoding is unvalidated and no UNSAT above means anything.\n"
        )
        return 1
    if win is not None:
        sys.stdout.write(
            "\n  The witness IS the proof: gate list, FanInTwo by `intro g hg; fin_cases hg`,\n"
            "  the size by simp, the rows by decide. Build it, check.sh, lint.py, submit.\n"
        )
        return 0
    sys.stdout.write(
        f"\n  every size from 1 to {a.budget} is UNSAT and the control passed, so the row is\n"
        "  FALSE by exhaustion. Release statement_seems_false (NOT exhausted - that reason is\n"
        "  only for a range of a sharded search and the desk refuses it otherwise).\n"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
