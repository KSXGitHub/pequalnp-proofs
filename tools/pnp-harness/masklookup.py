#!/usr/bin/env python3
"""Decide a 4x4 one-a-side mask row in seconds, instead of spending a worker on it.

The desk posts a family of rows of the form "some AND/OR/NOT circuit of fan-in two
with at most B gates represents the 4 by 4 bipartite graph with mask M on the
one-a-side promise" - L-meta-20807 (mask 13279, B = 5) and L-meta-19071 (mask 858,
B = 7) are two we have seen. Every one of them is decided by the OPTIMUM of that
mask, and the optimum is cheap:

  * `lrat/mask4x4_gt6.txt` lists the 43416 masks whose optimum EXCEEDS 6, produced
    by a full sweep of all 65536 masks in 11 seconds (the column model of
    $P/p19071/scan.c over the depth-4 state set from export4.py). The counts are
    10366 masks at optimum <= 5, 22120 at <= 6, 43416 above.
  * below 7 the exact optimum comes from $P/p19071/rep44.py in about a tenth of a
    second per size, swept upward so every smaller size is a recorded UNSAT, and
    $P/p19071/loose.py gives an independent second opinion whose UNSAT covers every
    circuit of at most that size by padding monotonicity.

Validated against four masks whose optimum was already known by other means:
13279 (6, by our own exhaustion), 858 (8, by three independent methods), 3824 (6,
upstream's own V_ file) and 9999 (6, our value-row proof). Four for four.

So: budget >= optimum means the row is TRUE and the witness is free - rep44.py
prints a gate list that $P/p4873/mklean.py turns into a checkable Lean file.
Budget < optimum means the row is FALSE and should be released
`statement_seems_false`, which is a verdict backed by exhaustion here rather than
by a non-return - this family is the one place on the desk where we can say that
honestly.
"""

from __future__ import annotations

import os
import pathlib
import re
import subprocess
import sys
from typing import Final

S: Final = pathlib.Path(__file__).absolute().parent
TABLE: Final = S / "lrat" / "mask4x4_gt6.txt"
#: The synthesis engine lives in this session's own scratchpad, not in the
#: repository, because it is a working tool rather than a deliverable and it does
#: not meet this repo's lint rules. ruff's S108 flags the literal path as an
#: insecure temporary directory; that rule is aimed at world-writable /tmp files a
#: stranger could substitute, and this is a session-private directory whose name
#: carries the session id. Overridable so a later session can point at its own.
ENGINE: Final = pathlib.Path(
    os.environ.get(
        "PNP_ENGINE_DIR",
        "/tmp/claude-0/-home-user-pequalnp-proofs/731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/pnp/p19071",  # noqa: S108
    )
)


def gt6() -> set[int]:
    if not TABLE.is_file():
        return set()
    return {int(t) for t in TABLE.read_text().split()}


def exact_size(mask: int, gates: int) -> str:
    """rep44.py at an EXACT gate count, with symmetry breaking OFF.

    Loose on purpose: tight symmetry breaking makes UNSAT reachable and SAT much
    harder to find, and that asymmetry cost a sibling worker a known solution it
    could not rediscover in 330 seconds. Hunt loose.
    """
    p = subprocess.run(  # noqa: S603
        [
            sys.executable,
            "-I",
            str(ENGINE / "rep44.py"),
            "--mask",
            str(mask),
            "--gates",
            str(gates),
            "--no-symmetry",
            "--timeout",
            "300",
        ],
        capture_output=True,
        text=True,
        check=False,
        cwd=ENGINE,
    )
    m = re.search(r"RESULT:\s+(\w+)", p.stdout)
    return m.group(1) if m else "NORETURN"


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        sys.stderr.write("usage: masklookup.py <mask> <budget>\n")
        return 2
    mask, budget = int(argv[0]), int(argv[1])
    sys.stdout.write(f"mask {mask}, posted budget {budget}\n")
    if mask in gt6():
        sys.stdout.write("  table: optimum EXCEEDS 6\n")
        if budget <= 6:
            sys.stdout.write(
                f"  VERDICT: FALSE - no circuit of {budget} gates exists, since the optimum is at"
                " least 7. Release statement_seems_false; the sweep behind the table is an"
                " exhaustion, not a non-return\n"
            )
            return 0
        sys.stdout.write(
            "  the budget is 7 or more, which the table does not resolve. Settle it with"
            f" {ENGINE}/deep.c (solver-free, about 50 s for the 7-gate question) or rep44.py\n"
        )
        return 0
    sys.stdout.write("  table: optimum is at most 6; sweeping upward for the exact value\n")
    for g in range(1, 7):
        verdict = exact_size(mask, g)
        sys.stdout.write(f"    exactly {g} gates: {verdict}\n")
        if verdict == "SAT":
            if budget >= g:
                sys.stdout.write(
                    f"  VERDICT: TRUE - optimum is {g} and the budget is {budget}. The witness is"
                    " free: take rep44.py's gate list through $P/p4873/mklean.py, then claim the row"
                    " with `desk.sh next --proof-of <id>` and submit\n"
                )
            else:
                sys.stdout.write(
                    f"  VERDICT: FALSE - optimum is {g}, above the posted {budget}. Release"
                    " statement_seems_false; every smaller size above is a recorded UNSAT, so this"
                    " is an exhaustion\n"
                )
            return 0
        if verdict == "NORETURN":
            sys.stdout.write(
                "  a size DID NOT RETURN, so the optimum is unresolved. That is not an UNSAT and"
                " must not be reported as one\n"
            )
            return 1
    sys.stdout.write("  no size up to 6 was satisfiable, which contradicts the table - investigate\n")
    return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
