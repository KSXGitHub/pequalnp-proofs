#!/usr/bin/env python3
"""Cube L-meta-16088 on (NOT position, NOT operand). Args: lo hi seconds."""

from __future__ import annotations

import sys

sys.path.insert(0, "/tmp/claude-0/-home-user-pequalnp-proofs/731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/pnp/jobs")

import sixinput as S  # noqa: E402


def main(argv: list[str]) -> int:
    lo = int(argv[0]) if argv else 0
    hi = int(argv[1]) if len(argv) > 1 else 0
    secs = int(argv[2]) if len(argv) > 2 else 40
    unsat = skipped = 0
    for pos in range(lo, hi + 1):
        for w in range(S.N + pos):
            st, info = S.solve_pinned_operand(S.BUDGET, pos, w, secs)
            if st == "SAT":
                sys.stdout.write(f"  *** WIN: NOT at gate {pos} reading wire {w} ***\n  {info}\n")
                return 0
            if st == "UNSAT":
                unsat += 1
            else:
                skipped += 1
                sys.stdout.write(f"  gate {pos} wire {w}: {st} {info[:40]}\n")
    sys.stdout.write(f"  gates {lo}..{hi}: {unsat} cubes UNSAT, {skipped} not resolved\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
