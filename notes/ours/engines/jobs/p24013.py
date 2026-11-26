#!/usr/bin/env python3
"""L-meta-24013: an 8-gate FanInTwo circuit for the two-lit function of mask 275161.

THE ROW, 60 points:

  exists C, FanInTwo C and C.size <= 8 and
    forall i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i or k = j))
      = (275161 : Nat).testBit (5 * min i.val j.val + max i.val j.val)

Fifteen constrained inputs - the indicator vectors of the unordered pairs over
five points, i = j included, which is the weight-one vector e_i. Off that set the
circuit is free. The desk's sketch says its own complete search found nothing at
five gates or fewer, and that it holds one of nine:

  OR(1,2), AND(0,5), AND(1,3), OR(0,1), NOT(8), AND(4,9), OR(6,7), OR(10,11), NOT(12)

with inputs 0-4 the five points, gate k on wire 5+k, the output the last gate. So
the question is 6, 7 or 8, and the row asks for 8.

A SAT here IS the proof - gate list, FanInTwo by `intro g hg; fin_cases hg`, the
size by simp, the fifteen rows by decide - and it would be the first posted row
we have closed.

THE CONTROL COMES FIRST. That nine-gate circuit lets the row construction be
checked against something external BEFORE any search: if these fifteen rows do
not accept it, my reading of the function is wrong and an UNSAT would be
meaningless. Note its output gate is a NOT, which also means the padding argument
does NOT apply here, so every size below the budget is swept rather than inferred.
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

MASK: Final = 275161
N: Final = 5
BUDGET: Final = 8
WORK: Final = pathlib.Path(
    "/tmp/claude-0/-home-user-pequalnp-proofs/731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/p24013"
)

#: The desk's own nine-gate circuit, verbatim from its sketch. Wire 5+k is gate k.
DESK9: Final = [
    E.GateSpec("or", [1, 2]),    # wire 5
    E.GateSpec("and", [0, 5]),   # wire 6
    E.GateSpec("and", [1, 3]),   # wire 7
    E.GateSpec("or", [0, 1]),    # wire 8
    E.GateSpec("not", [8]),      # wire 9
    E.GateSpec("and", [4, 9]),   # wire 10
    E.GateSpec("or", [6, 7]),    # wire 11
    E.GateSpec("or", [10, 11]),  # wire 12
    E.GateSpec("not", [12]),     # wire 13 = output
]


def rows() -> list[tuple[tuple[bool, ...], bool]]:
    out: list[tuple[tuple[bool, ...], bool]] = []
    for a in range(N):
        for b in range(a, N):
            bits = tuple(k in (a, b) for k in range(N))
            out.append((bits, bool((MASK >> (N * a + b)) & 1)))
    return out


def main() -> int:
    rs = rows()
    sys.stdout.write(f"mask {MASK}, {len(rs)} constrained rows\n")
    for a in range(N):
        sys.stdout.write(
            "    "
            + "".join(
                "1" if (MASK >> (N * min(a, b) + max(a, b))) & 1 else "." for b in range(N)
            )
            + "\n"
        )

    out_wire = N + len(DESK9) - 1
    bad = [1 for bits, want in rs if E.simulate(DESK9, bits, out_wire) != want]
    if bad:
        sys.stdout.write(
            f"  CONTROL FAILED: the desk's own 9-gate circuit misses {len(bad)} of {len(rs)}"
            " rows, so my reading of the function is wrong. Nothing below would mean anything.\n"
        )
        return 1
    sys.stdout.write(
        f"  CONTROL PASSED: the desk's 9-gate circuit satisfies all {len(rs)} rows.\n"
    )

    wants = [w for _, w in rs]
    if all(wants) or not any(wants):
        sys.stdout.write("  target is CONSTANT on the rows; normal form not justified\n")
        return 1
    for w in range(N):
        if all(bits[w] == want for bits, want in rs):
            sys.stdout.write(f"  target equals input {w}; normal form not justified\n")
            return 1
    sys.stdout.write("  target is neither constant nor a projection\n\n")

    WORK.mkdir(parents=True, exist_ok=True)
    best: int | None = None
    # Ask the budget first - that is the row - then walk down for a smaller
    # witness, then confirm a control SAT above if the budget is UNSAT.
    # 9 first as the POSITIVE CONTROL: a circuit of that size is known to exist,
    # so if this code path cannot find one, no UNSAT it reports means anything.
    # Then the budget and every size below it, because the known circuit's output
    # gate is a NOT and padding therefore does not transfer.
    for gates in (9, BUDGET, 7, 6, 5, 4, 3, 2, 1):
        enc = E.build(N, gates, rs, False, False, False)  # loose: hunting
        path = WORK / f"m{MASK}_s{gates}.cnf"
        enc.cnf.write(path)
        status, assign, dt = E.run_solver(E.find_solver(), path, 600)
        sys.stdout.write(f"  exactly {gates} gates: {status} in {dt:.1f}s\n")
        if status != "SAT":
            continue
        got = E.decode(enc, assign)
        ow = N + len(got) - 1
        wrong = [1 for bits, want in rs if E.simulate(got, bits, ow) != want]
        if wrong:
            sys.stdout.write(f"    DECODE MISMATCH on {len(wrong)} rows - not a win\n")
            continue
        # ONLY a SAT at or below the posted budget satisfies the row. The run at 9
        # is a positive CONTROL, not a win: an earlier version of this line set
        # `best` for any SAT and then announced "ROW IS TRUE at 9 gates (posted
        # budget 8)", which is false and is exactly how a tool talks its operator
        # into submitting something that cannot be accepted.
        if gates <= BUDGET:
            best = gates
        sys.stdout.write(
            f"\n  *** {gates}-GATE CIRCUIT, RE-SIMULATED ON ALL {len(rs)} ROWS ***\n"
            f"  lean gates: {E.lean_gate_list(got)}\n"
            f"  output wire: {ow}\n"
        )
        (WORK / f"witness_s{gates}.txt").write_text(
            f"{E.lean_gate_list(got)}\noutput wire {ow}\n"
        )
    if best is not None:
        sys.stdout.write(
            f"\n  ROW IS TRUE at {best} gates (posted budget {BUDGET}). The witness is the proof:\n"
            "    build the Lean file, check.sh it, lint.py L-meta-24013, then submit.\n"
        )
        return 0
    sys.stdout.write(
        "\n  nothing found at 8, 7 or 6. Each of those is an EXACT-size result; the output gate\n"
        "  of the known 9-gate circuit is a NOT, so padding does not apply and an UNSAT at 8\n"
        "  does not rule out smaller sizes. Sweep 1..5 before calling the row false.\n"
    )
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
