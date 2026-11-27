#!/usr/bin/env python3
"""Run the pinned-position split for L-meta-16088, one gate position per call slice."""

from __future__ import annotations

import sys

sys.path.insert(0, "/tmp/claude-0/-home-user-pequalnp-proofs/731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/pnp/jobs")

import sixinput as S  # noqa: E402


def main(argv: list[str]) -> int:
    lo = int(argv[0]) if argv else 0
    hi = int(argv[1]) if len(argv) > 1 else S.BUDGET - 1
    secs = int(argv[2]) if len(argv) > 2 else 110
    verdicts: list[str] = []
    for pos in range(lo, min(hi, S.BUDGET - 1) + 1):
        st, info = S.solve_pinned(S.BUDGET, pos, secs, False)
        sys.stdout.write(f"  NOT pinned at gate {pos}: {st}  {info[:110]}\n")
        verdicts.append(st)
        if st == "SAT":
            sys.stdout.write("  *** WIN - witness saved ***\n")
            return 0
    if all(v == "UNSAT" for v in verdicts):
        sys.stdout.write(f"  gates {lo}..{hi} are all UNSAT\n")
    else:
        sys.stdout.write("  not all UNSAT; unresolved positions remain\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
