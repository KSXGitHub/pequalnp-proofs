#!/usr/bin/env python3
"""L-meta-16088: a 9-gate circuit for a six-input function that USES A NOT GATE.

THE ROW, 39 points:

  exists C, FanInTwo C and (exists g in C.gates, g.op = not and g.inputs.length = 1)
    and C.size <= 9
    and forall x : Fin 6 -> Bool, C.eval (List.ofFn x)
          = Nat.testBit (3901270152 * 2^32 + 2827526144)
              (sum over i : Fin 6 of if x i then 2^i else 0)

Three differences from every row settled so far, and all three make it EASIER:

  * the function is FULLY SPECIFIED - all 64 inputs are constrained, not a
    promise subset - so there is no freedom to reason about;
  * six inputs and nine gates is a small instance;
  * the index is exactly the integer whose bits are x, so row k of the table is
    simply testBit(TABLE, k).

The one new ingredient is the NOT REQUIREMENT. The desk's sketch explains why it
is there: "The AND/OR size of f is 9 (computed, not checked), so a find is a tie:
a least circuit using NOT." So a monotone 9-gate circuit exists and is not an
answer; the row wants a 9-gate circuit containing at least one NOT gate, which
ties the monotone optimum while using negation.

That is one clause: the disjunction of every NOT selector over every gate. The
engine already creates one selector per (operation, operand-pair) per gate and
constrains each gate to exactly one, so requiring at least one NOT is a single
OR over the NOT selectors and nothing else about the encoding changes.

A SAT here IS the proof, and the sketch says so: the gate kinds, the gate count,
and `decide` over all 64 inputs.
"""

from __future__ import annotations

import pathlib
import sys
from typing import Final

ENGINE: Final = pathlib.Path(
    "/tmp/claude-0/-home-user-pequalnp-proofs/731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/pnp/p20508"
)
sys.path.insert(0, str(ENGINE))

import rep44m as E  # noqa: E402

TABLE: Final = 3901270152 * 2**32 + 2827526144
N: Final = 6
BUDGET: Final = 9
WORK: Final = pathlib.Path(
    "/tmp/claude-0/-home-user-pequalnp-proofs/731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/p16088"
)


def rows() -> list[tuple[tuple[bool, ...], bool]]:
    """All 64 inputs. Row k is the assignment whose bits are k, output testBit(TABLE, k)."""
    out: list[tuple[tuple[bool, ...], bool]] = []
    for k in range(1 << N):
        bits = tuple(bool((k >> i) & 1) for i in range(N))
        out.append((bits, bool((TABLE >> k) & 1)))
    return out


def monotone_check(rs: list[tuple[tuple[bool, ...], bool]]) -> bool:
    """The desk calls f monotone; verify rather than take its word.

    If f were not monotone the sketch's claim that its AND/OR size is 9 could not
    hold, and the whole framing of the row - a tie using NOT - would be wrong.
    """
    val = {bits: want for bits, want in rs}
    for bits, want in rs:
        if not want:
            continue
        for i in range(N):
            if not bits[i]:
                up = tuple(True if j == i else b for j, b in enumerate(bits))
                if not val[up]:
                    return False
    return True


def solve(gates: int, require_not: bool, seconds: int, tight: bool, tag: str) -> tuple[str, str]:
    rs = rows()
    enc = E.build(N, gates, rs, tight, tight, False)
    if require_not:
        # AT LEAST ONE NOT GATE: one clause, the disjunction of every NOT
        # selector across every gate. `sel[j]` maps each candidate form at gate j
        # to its selector variable and the engine already forces exactly one per
        # gate, so this adds a requirement without disturbing that.
        lits = [v for j in range(gates) for f, v in enc.sel[j].items() if f.op == "not"]
        if not lits:
            return "NO-NOT-FORMS", ""
        enc.cnf.add(lits)
    WORK.mkdir(parents=True, exist_ok=True)
    path = WORK / f"t_s{gates}_{tag}.cnf"
    enc.cnf.write(path)
    status, assign, dt = E.run_solver(E.find_solver(), path, seconds)
    if status != "SAT":
        return status, f"{dt:.1f}s"
    got = E.decode(enc, assign)
    ow = N + len(got) - 1
    wrong = [1 for bits, want in rs if E.simulate(got, bits, ow) != want]
    if wrong:
        return "DECODE-MISMATCH", f"{len(wrong)} rows"
    nots = sum(1 for g in got if g.op == "not")
    if require_not and nots == 0:
        return "NO-NOT-IN-MODEL", "the clause did not bind - investigate"
    (WORK / f"witness_s{gates}_{tag}.txt").write_text(
        f"{E.lean_gate_list(got)}\noutput wire {ow}\nNOT gates: {nots}\n"
    )
    return "SAT", f"{dt:.1f}s | {nots} NOT | {E.lean_gate_list(got)} | output {ow}"


def solve_pinned(gates: int, pos: int, seconds: int, tight: bool) -> tuple[str, str]:
    """Require gate `pos` itself to be the NOT, instead of one existing somewhere.

    WHY SPLIT. "Some gate is a NOT" is a single wide disjunction over every NOT
    selector of every gate, and the solver has to search the whole space at once:
    both loose and tight timed out at about 500 seconds, while the SAME instance
    without the NOT requirement solved in ten. Pinning the position turns one
    hard question into `gates` much tighter ones. If every one is UNSAT the row
    is false, because any circuit with a NOT has it at some position; if one is
    SAT it is a witness and the row is won. This is cube-and-conquer on the only
    free choice the requirement leaves.
    """
    rs = rows()
    enc = E.build(N, gates, rs, tight, tight, False)
    lits = [v for f, v in enc.sel[pos].items() if f.op == "not"]
    if not lits:
        return "NO-NOT-FORMS", f"gate {pos} has no NOT form"
    enc.cnf.add(lits)
    WORK.mkdir(parents=True, exist_ok=True)
    path = WORK / f"pin_s{gates}_g{pos}{chr(95)}{int(tight)}.cnf"
    enc.cnf.write(path)
    status, assign, dt = E.run_solver(E.find_solver(), path, seconds)
    if status != "SAT":
        return status, f"{dt:.1f}s"
    got = E.decode(enc, assign)
    ow = N + len(got) - 1
    if [1 for bits, want in rs if E.simulate(got, bits, ow) != want]:
        return "DECODE-MISMATCH", ""
    nots = sum(1 for g in got if g.op == "not")
    (WORK / f"witness_pin_g{pos}.txt").write_text(
        f"{E.lean_gate_list(got)}\noutput wire {ow}\nNOT gates: {nots}\n"
    )
    return "SAT", f"{dt:.1f}s | {nots} NOT | {E.lean_gate_list(got)} | output {ow}"


def main() -> int:
    rs = rows()
    ones = sum(1 for _b, w in rs if w)
    sys.stdout.write(f"table {TABLE}, {N} inputs, {len(rs)} rows, {ones} of them true\n")
    sys.stdout.write(f"  monotone: {monotone_check(rs)} (the desk says it is)\n")
    wants = [w for _b, w in rs]
    if all(wants) or not any(wants):
        sys.stdout.write("  CONSTANT - normal form not justified\n")
        return 2
    for i in range(N):
        if all(b[i] == w for b, w in rs):
            sys.stdout.write(f"  equals input {i} - normal form not justified\n")
            return 2
    sys.stdout.write("  neither constant nor a projection\n\n")

    # Control first: a MONOTONE 9-gate circuit is claimed to exist, so the
    # encoding must find one. Without that, nothing below is believable.
    st, info = solve(BUDGET, False, 400, False, "ctl")
    sys.stdout.write(f"  control, {BUDGET} gates, NOT not required: {st}  {info[:80]}\n")
    if st != "SAT":
        sys.stdout.write(
            "  the control did not return SAT, so the encoding is unvalidated on this"
            " instance and no result below means anything\n"
        )
        return 1

    # The row itself.
    st, info = solve(BUDGET, True, 500, False, "req")
    sys.stdout.write(f"  THE ROW, {BUDGET} gates WITH a NOT: {st}\n")
    if st == "SAT":
        sys.stdout.write(f"  *** WIN ***\n  {info}\n")
        return 0
    sys.stdout.write(f"  {info}\n")
    if st == "TIMEOUT":
        # THE CALIBRATION LAW. The unconstrained instance solved in ten seconds
        # while the NOT-constrained one did not return at all, which is the
        # signature of an UNSAT rather than a hard-to-find witness. Tight
        # symmetry breaking makes UNSAT reachable at the cost of making a
        # witness harder to find, so it is exactly the right second attempt.
        st, info = solve(BUDGET, True, 520, True, "tight")
        sys.stdout.write(f"  THE ROW again, tight: {st}  {info[:90]}\n")
        if st == "SAT":
            sys.stdout.write(f"  *** WIN ***\n  {info}\n")
            return 0
    if st == "UNSAT":
        sys.stdout.write(
            "  no 9-gate circuit with a NOT exists. That refutes the row - but note the\n"
            "  control shows a monotone 9-gate circuit DOES exist, so the row is a tie\n"
            "  question and the answer is that negation does not achieve the tie.\n"
        )
    else:
        sys.stdout.write("  not an UNSAT; the row is unsettled\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
