#!/usr/bin/env python3
"""Try to WIN a monotone promise row: search for a witness at exactly the posted budget.

This is the other half of promise.py. That tool refutes a row from below, which is
honest service and earns nothing; this one goes after the rows counting CANNOT
refute, because those are the ones that may be TRUE - and a witness for a posted
statement is a closed row.

HOW THE TWO FIT TOGETHER. For a row `RepSizeAtMost A s`:

  * promise.py gives a kernel-backed lower bound L. If s < L the row is false and
    there is nothing to hunt.
  * if s >= L the row is undecided, and the question is whether the true monotone
    optimum is at most s. That is what this tool asks, by exact-size search.

A SAT answer here is a WITNESS, and the witness IS the proof: the submission is the
gate list, `Monotone2` by `intro g hg; fin_cases hg <;> exact ...`, the size by
`simp`, and `Represents` by `decide` over the n*m promise rows. That is the shape
of the 354 V_ files upstream and it is a proof, not a reduction.

WHY A SEPARATE ENGINE COPY. rep44.py was written for `FanInTwo`, where NOT gates
are allowed and counted. `RepSizeAtMost` is `Monotone2` - AND and OR only - so a
SAT answer from the unmodified engine may use NOT gates and then says nothing
about the row. The copy at $PNP_MONO_DIR/rep44m.py adds a --monotone flag that
forbids the NOT forms; each gate picks exactly one form, so that is one unit clause
per NOT form and nothing else about the encoding, the normal form or the symmetry
breaking changes.

HOW THE MONOTONE MODE WAS VALIDATED, from both sides at once, on mask 249:

  * at 6 gates it returns UNSAT, and we have a KERNEL PROOF that 6 is impossible
    (notes/ours/L_promise_counting.lean, citing RepPath.path);
  * at 7 gates it returns SAT with a NOT-free circuit, re-simulated on all 15
    promise rows, and the desk's own sketch says it holds a 7-gate AND/OR circuit.

So the Lean proof and the solver agree where they overlap, in both directions. The
first use of it settled mask 3309: UNSAT at every size 1 to 7 and SAT at 8, which
makes its monotone optimum exactly 8 and the posted budget of 7 impossible.

THE CALIBRATION LAW. Tight symmetry breaking makes UNSAT reachable and makes SAT
much harder to FIND - cadical once missed a known 12-gate solution in 330 s with
symmetry on and found it in 16 s with it off. We are HUNTING here, so every call
is loose. Use the engine directly with symmetry on if you want an UNSAT.
"""

from __future__ import annotations

import json
import os
import pathlib
import re
import subprocess
import sys
from typing import Final

S: Final = pathlib.Path(__file__).absolute().parent
#: The monotone engine copy. It lives in the session scratchpad rather than in the
#: repository because it is a working tool, not a deliverable, and it does not meet
#: this repo's lint rules. Overridable so a later session can point at its own.
ENGINE: Final = pathlib.Path(
    os.environ.get(
        "PNP_MONO_DIR",
        "/tmp/claude-0/-home-user-pequalnp-proofs/731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/pnp/p20508",  # noqa: S108
    )
)


def is_unsat(verdict: str) -> bool:
    """True only for an exact UNSAT. Everything else is a non-result.

    The guard this replaces compared against the string "NORETURN" while the
    engine prints "DID NOT RETURN" on a timeout, so a timeout slipped past it
    and the tool recommended releasing a row as false on a search that never
    finished. Anything that is not exactly UNSAT - a timeout, an empty string, a
    lowercase spelling, a crash message - must read as "we do not know".
    """
    return verdict.strip() == "UNSAT"


def row_of(step_id: str) -> tuple[int, int, int, int] | None:
    """(mask, n, m, budget) read from the step's own statement, never typed by hand.

    Typing a budget from a row TITLE went wrong twice in one sitting: 20464 and
    20940 read 5 and 8 in their statements where their titles suggested 6 and 7,
    and with the wrong number one of them screened as undecided when it is false.
    """
    p = S / "steps" / f"{step_id}.json"
    if not p.is_file():
        sys.stderr.write(f"no statement on file for {step_id}; draw it first with desk.sh next\n")
        return None
    stmt = str((json.load(open(p)).get("gap") or {}).get("statement", ""))
    m = re.search(
        r"RepSizeAtMost\s*\(fun[^=]*Fin\s*(\d+)[^=]*Fin\s*(\d+)[^=]*=>\s*\(?\s*(\d+)"
        r"[^)]*\)?[^)]*\.testBit[^)]*\)\s*\)\s*(\d+)",
        stmt,
    )
    if not m:
        sys.stderr.write(
            f"{step_id} is not a monotone promise row (no RepSizeAtMost over a testBit mask).\n"
            "This tool only handles that family; read the statement and pick the right tool.\n"
        )
        return None
    n, mm, mask, budget = (int(g) for g in m.groups())
    return mask, n, mm, budget


def search(mask: int, n: int, m: int, gates: int, seconds: int) -> tuple[str, str]:
    """One exact-size monotone call, loose. Returns (verdict, full output)."""
    p = subprocess.run(  # noqa: S603
        [
            sys.executable,
            str(ENGINE / "rep44m.py"),
            "--mask",
            str(mask),
            "--n",
            str(n),
            "--m",
            str(m),
            "--gates",
            str(gates),
            "--monotone",
            "--no-symmetry",
            "--timeout",
            str(seconds),
            "--tag",
            f"hunt{gates}",
        ],
        capture_output=True,
        text=True,
        check=False,
        cwd=ENGINE,
    )
    out = p.stdout + p.stderr
    hit = re.search(r"RESULT:\s+([A-Z ]+)", out)
    return (hit.group(1).strip() if hit else "NORETURN"), out


def main(argv: list[str]) -> int:
    if not argv:
        sys.stderr.write("usage: promisehunt.py <step-id> [seconds-per-size]\n")
        return 2
    step_id = argv[0]
    seconds = int(argv[1]) if len(argv) > 1 else 300
    got = row_of(step_id)
    if got is None:
        return 2
    mask, n, m, budget = got
    sys.stdout.write(f"{step_id}: mask {mask} on {n}x{m}, posted budget {budget}\n")

    verdict, out = search(mask, n, m, budget, seconds)
    sys.stdout.write(f"  monotone, exactly {budget} gates, loose: {verdict}\n")

    if verdict == "SAT":
        gates_line = next((ln for ln in out.splitlines() if "lean gates" in ln), "")
        sys.stdout.write(
            "\n  *** WITNESS FOUND - THIS ROW IS WINNABLE ***\n"
            f"  {gates_line}\n\n"
            "  The witness IS the proof. Next:\n"
            "    1. build the file: the gate list above, Monotone2 by `intro g hg; fin_cases hg`,\n"
            "       the size by simp, Represents by decide over the promise rows\n"
            "    2. check.sh it, then lint.py the step id\n"
            f"    3. claim it even if someone else holds it: desk.sh next --proof-of {step_id}\n"
            "    4. submit\n"
            "  Build BEFORE claiming: a proof of a step you did not take earns only the floor.\n"
        )
        return 0

    # ONLY AN EXPLICIT UNSAT MAY PROCEED. This tested `verdict == "NORETURN"`,
    # but `search` returns whatever the engine printed, and a timeout prints
    # `RESULT: DID NOT RETURN`. So a timeout failed this check, fell through to
    # the branch below, and the tool announced "The row is FALSE" on the
    # strength of a search that never finished - the exact confusion every other
    # part of this harness exists to prevent, in the tool that recommends a
    # release. Seen live on L-meta-23111 at nine gates.
    if not is_unsat(verdict):
        sys.stdout.write(
            f"  the search returned {verdict!r}, which is NOT an UNSAT and must never be\n"
            "  reported as one. Give it longer, or leave the row alone and say plainly that\n"
            "  the budget was not reached. Do NOT release it as false.\n"
        )
        return 1

    # UNSAT AT EXACTLY THE BUDGET IS ALREADY ENOUGH, BY PADDING - no sweep.
    #
    # The encoder fixes an exact gate count, so the instinct is that an UNSAT at
    # the budget leaves a SMALLER circuit possible and every size below has to be
    # swept. It does not, in LOOSE mode. Suppose a circuit of size k <= budget
    # represents A, and let its last gate be `c = a op b`. In a monotone circuit
    # op is `and` or `or`, never `not`, so appending `d = c op a` gives
    #   op = or  : d = (a or b) or a  = a or b  = c
    #   op = and : d = (a and b) and a = a and b = c
    # on EVERY row, whatever the row set. So d has c's value, d is last, d is the
    # output, c is read, and no gate is unread: a circuit of size k + 1 in the
    # same normal form. Hence SAT at k implies SAT at k + 1, and by induction SAT
    # at every size up to the budget. Contrapositive: UNSAT at exactly the budget
    # means no circuit of size k <= budget exists, which is what the row denies.
    #
    # Verified rather than assumed: on mask 3824 the engine returns SAT at 5, 6,
    # 7, 8 and 9 with no gap, which is upward closure in action.
    #
    # THE ONE CONDITION: padding duplicates c's column, so --distinct-cols must
    # be OFF. `search` never passes it, and that is now load-bearing rather than
    # merely a hunting preference. It also needs op in {and, or}, which is why
    # this argument is sound for RepSizeAtMost (Monotone2) and must NOT be
    # reused as-is for a FanInTwo row, where the last gate could be a NOT.
    sys.stdout.write(
        f"  no circuit of exactly {budget} gates, and by padding that rules out every\n"
        f"  smaller size too: a monotone circuit of size k can be padded to k + 1 by\n"
        f"  appending `c op a` after its last gate `c = a op b`, so SAT at k would force\n"
        f"  SAT at {budget}. The row is FALSE.\n"
    )
    if "--sweep" in sys.argv:
        sys.stdout.write("  --sweep given, so confirming the padding argument size by size:\n")
        for g in range(1, budget):
            v, _ = search(mask, n, m, g, seconds)
            sys.stdout.write(f"    exactly {g}: {v}\n")
            if v != "UNSAT":
                sys.stdout.write(
                    f"  size {g} came back {v}, which CONTRADICTS the padding argument."
                    " Do not release; the encoding or the argument is wrong.\n"
                )
                return 1
    sys.stdout.write(
        "  Before releasing, confirm the engine returns SAT at some larger size on THIS\n"
        f"  mask - try {budget + 1} - because an UNSAT from a broken encoding looks exactly\n"
        "  like a real one, and that control is what the padding argument cannot replace.\n"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
