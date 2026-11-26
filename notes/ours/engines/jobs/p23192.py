#!/usr/bin/env python3
"""L-meta-23192: a 6-gate FanInTwo circuit for the two-lit function of mask 20287.

THE ROW, verbatim:

  exists C, FanInTwo C and C.size <= 6 and
    forall i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i or k = j))
      = (20287 : Nat).testBit (6 * min i.val j.val + max i.val j.val)

So only 21 inputs are constrained - the indicator vectors of the unordered pairs
{i,j} over six points, i = j included, which is the weight-1 vector e_i. Off that
set the circuit is free, exactly as on a promise row. The desk holds a 7-gate
circuit and asks for 6, and its sketch says: "A met unit may be a better order of
the points and not a saving from a NOT gate."

WHY THIS ONE IS WORTH THE TRY. Six inputs, six gates, 21 rows: the smallest
winnable-looking object the desk has handed us. And a SAT here IS the proof - the
gate list, FanInTwo by `intro g hg; fin_cases hg`, the size by simp, and the 21
rows by decide - so it would be the first posted row we have ever closed.

THE CONTROL THAT COMES FIRST. The sketch gives its own 7-gate circuit, so my row
construction can be checked against something external BEFORE any search:

  OR(3,4), OR(5,6), NOT(7), AND(2,8), AND(1,7), OR(0,9), OR(10,11)

with inputs 0-5 the six points, gate k on wire 6+k, output the last gate. If my
21 rows do not accept that circuit, my reading of the function is wrong and any
UNSAT from the search would be meaningless. That check runs first and the job
stops if it fails.
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

MASK: Final = 20287
N: Final = 6
WORK: Final = pathlib.Path(
    "/tmp/claude-0/-home-user-pequalnp-proofs/731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/p23192"
)

#: The desk's own 7-gate circuit, as its sketch lists it. Wire 6+k is gate k, so
#: operand 6 is gate 0, operand 7 is gate 1, and so on; the output is the last.
DESK7: Final = [
    E.GateSpec("or", [3, 4]),
    E.GateSpec("or", [5, 6]),
    E.GateSpec("not", [7]),
    E.GateSpec("and", [2, 8]),
    E.GateSpec("and", [1, 7]),
    E.GateSpec("or", [0, 9]),
    E.GateSpec("or", [10, 11]),
]


def rows() -> list[tuple[tuple[bool, ...], bool]]:
    """One row per unordered pair, i = j included: 21 of them."""
    out: list[tuple[tuple[bool, ...], bool]] = []
    for a in range(N):
        for b in range(a, N):
            bits = tuple(k in (a, b) for k in range(N))
            out.append((bits, bool((MASK >> (N * a + b)) & 1)))
    return out


def show(rs: list[tuple[tuple[bool, ...], bool]]) -> None:
    sys.stdout.write(f"mask {MASK}, {len(rs)} constrained rows\n")
    for a in range(N):
        line = "    "
        for b in range(N):
            lo, hi = min(a, b), max(a, b)
            line += "1" if (MASK >> (N * lo + hi)) & 1 else "."
        sys.stdout.write(line + "\n")


def control(rs: list[tuple[tuple[bool, ...], bool]]) -> bool:
    bad = [
        (bits, want)
        for bits, want in rs
        if E.simulate(DESK7, bits, N + len(DESK7) - 1) != want
    ]
    if bad:
        sys.stdout.write(
            f"  CONTROL FAILED: the desk's own 7-gate circuit misses {len(bad)} of"
            f" {len(rs)} rows. My reading of the function is wrong; no search result"
            " from here would mean anything.\n"
        )
        for bits, want in bad[:4]:
            sys.stdout.write(f"    bits {''.join('1' if x else '0' for x in bits)} want {want}\n")
        return False
    sys.stdout.write(
        f"  CONTROL PASSED: the desk's 7-gate circuit satisfies all {len(rs)} rows,"
        " so the row construction is right.\n"
    )
    return True


def degenerate(rs: list[tuple[tuple[bool, ...], bool]]) -> str | None:
    """The engine's normal form is not justified for a constant or a projection."""
    wants = [w for _, w in rs]
    if all(wants) or not any(wants):
        return "the target is CONSTANT on the constrained rows"
    for w in range(N):
        if all(bits[w] == want for bits, want in rs):
            return f"the target equals input wire {w} on every constrained row (a projection)"
        if all(bits[w] != want for bits, want in rs):
            return f"the target equals NOT input wire {w} on every constrained row"
    return None


def hunt(rs: list[tuple[tuple[bool, ...], bool]], gates: int, seconds: int) -> str:
    enc = E.build(N, gates, rs, False, False, False)  # loose: hunting, not proving
    WORK.mkdir(parents=True, exist_ok=True)
    path = WORK / f"m{MASK}_s{gates}.cnf"
    enc.cnf.write(path)
    status, assign, dt = E.run_solver(E.find_solver(), path, seconds)
    sys.stdout.write(f"  exactly {gates} gates: {status} in {dt:.1f}s\n")
    if status != "SAT":
        return status
    got = E.decode(enc, assign)
    out = N + len(got) - 1
    wrong = [1 for bits, want in rs if E.simulate(got, bits, out) != want]
    if wrong:
        sys.stdout.write(f"  DECODE MISMATCH on {len(wrong)} rows - not reporting this as a win\n")
        return "BAD"
    sys.stdout.write(
        f"\n  *** {gates}-GATE CIRCUIT FOUND AND RE-SIMULATED ON ALL {len(rs)} ROWS ***\n"
        f"  lean gates: {E.lean_gate_list(got)}\n"
        f"  output wire: {out}\n"
    )
    (WORK / f"witness_s{gates}.txt").write_text(
        f"{E.lean_gate_list(got)}\noutput wire {out}\n"
    )
    return "SAT"


def main() -> int:
    rs = rows()
    show(rs)
    if not control(rs):
        return 1
    why = degenerate(rs)
    if why:
        sys.stdout.write(f"  NOTE: {why}; the engine's normal form is not justified here\n")
        return 1
    sys.stdout.write("  target is neither constant nor a projection, so the normal form holds\n\n")
    # The real question first, then a control at 7 on this same code path so that
    # an UNSAT at 6 is believable rather than merely printed.
    six = hunt(rs, 6, 600)
    if six == "SAT":
        return 0
    sys.stdout.write("\n  positive control on THIS code path at the size the desk already holds:\n")
    seven = hunt(rs, 7, 600)
    if seven != "SAT":
        sys.stdout.write(
            "  the control did NOT return SAT at 7, where a circuit is known to exist."
            " So the encoding is unvalidated and the result at 6 proves nothing.\n"
        )
        return 1
    if six == "UNSAT":
        # The encoder fixes an EXACT gate count, and its normal form holds each
        # LEAST circuit only at its own size, so UNSAT at 6 alone does not rule
        # out a circuit of 5 or fewer. The row says `C.size <= 6`, so every size
        # below it has to be swept before the row can be called false.
        sys.stdout.write("\n  sweeping below 6, since the row says at most 6 and the encoder fixes exact:\n")
        for g in range(1, 6):
            v = hunt(rs, g, 300)
            if v != "UNSAT":
                sys.stdout.write(
                    f"  size {g} came back {v}, not UNSAT, so the row is NOT settled.\n"
                )
                return 1
        sys.stdout.write(
            "\n  every size from 1 to 6 is UNSAT and 7 is SAT on the same code path, with the\n"
            "  desk's own circuit accepted by these rows as an external check. The optimum is\n"
            "  exactly 7, so the posted row asking for at most 6 is FALSE by exhaustion.\n"
        )
    else:
        sys.stdout.write(f"\n  6 came back {six}, which is not an UNSAT and must not be read as one.\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
