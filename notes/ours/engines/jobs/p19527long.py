#!/usr/bin/env python3
"""Hunt a 10-gate witness for L-meta-19527 for as long as it takes, in the background.

WHY THIS AND NOT AN UNSAT RUN. A worker established, with the 4x4 regressions
matching known answers and a 12-gate positive control returning SAT, that no
FanInTwo circuit of size 8 or less represents the 5x5 mask 3187468 - sizes 1
through 8 are each an exact-size UNSAT under the tight encoding. Size 9 did not
return in 400 s and size 10 did not return in 1641 s across four configurations.
Cost grows about 20x per gate on this mask (1.3 s, 11 s, 230 s at sizes 6, 7, 8),
which puts a size-10 UNSAT near a day of single-core solving - beyond the window.

The WITNESS side is the cheap half of the gamble, and it is the only half that
WINS the row: a 10-gate circuit, if one exists, closes a posted statement, and we
have never closed one. Solver time costs no tokens, so this runs unattended while
the session does other work. The poller keeps the lease alive meanwhile.

THE CALIBRATION LAW is why every configuration here is LOOSE. Tight symmetry
breaking makes UNSAT reachable and makes SAT much harder to find: cadical missed a
known 12-gate completion in 330 s with distinct/order constraints on and found it
in 16 s with them off. Hunting is loose work. Each run also gets its own seed, and
two run at once so the box keeps two of its four cores for everything else.
"""

from __future__ import annotations

import pathlib
import re
import subprocess
import sys
import time
from typing import Final

P: Final = pathlib.Path(
    "/tmp/claude-0/-home-user-pequalnp-proofs/731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/pnp"
)
ENGINE: Final = P / "p19071"
LOG: Final = P / "p19527long.out"
MASK: Final = 3187468
GATES: Final = 10
#: Per-call wall clock. Two run at a time, so a round costs this much, not twice it.
PER_CALL: Final = 2700
#: Seeds in pairs: each pair runs concurrently. Two rounds, so the whole job fits
#: inside the two-hour ceiling on a backgrounded command; relaunch for more.
ROUNDS: Final = ((1, 7919), (104729, 1299709))


def say(msg: str) -> None:
    stamp = time.strftime("%H:%M:%SZ", time.gmtime())
    line = f"{stamp} {msg}\n"
    with open(LOG, "a") as fh:
        fh.write(line)
    sys.stdout.write(line)
    sys.stdout.flush()


def launch(seed: int) -> subprocess.Popen[str]:
    cmd = [
        sys.executable,
        str(ENGINE / "rep44.py"),
        "--mask",
        str(MASK),
        "--n",
        "5",
        "--m",
        "5",
        "--gates",
        str(GATES),
        "--no-symmetry",
        "--timeout",
        str(PER_CALL),
        "--tag",
        f"long{seed}",
        # `--solver-arg --sat` does NOT work: argparse reads a value starting with
        # a dash as the next option, not as this option's argument, and the engine
        # exits with "expected one argument". The `=` form is required.
        "--solver-arg=--sat",
        f"--solver-arg=--seed={seed}",
    ]
    say(f"launch seed {seed}")
    return subprocess.Popen(  # noqa: S603
        cmd, cwd=ENGINE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True
    )


def main() -> int:
    say(f"=== 10-gate witness hunt, mask {MASK} on 5x5, loose, {len(ROUNDS)} rounds of 2 ===")
    for pair in ROUNDS:
        procs = [(seed, launch(seed)) for seed in pair]
        for seed, pr in procs:
            out = pr.communicate()[0] or ""
            m = re.search(r"RESULT:\s+(\w+)", out)
            verdict = m.group(1) if m else "NORETURN"
            say(f"seed {seed}: {verdict}")
            if verdict == "SAT":
                # A WIN. Keep every line: the gate list is the submission.
                say("*** SAT AT 10 GATES - this closes L-meta-19527 ***")
                with open(P / "p19527_WITNESS.txt", "w") as fh:
                    fh.write(out)
                say(f"full solver output saved to {P / 'p19527_WITNESS.txt'}")
                # Stop the sibling; its answer no longer matters.
                for _s, other in procs:
                    if other.poll() is None:
                        other.terminate()
                return 0
    say("no witness found in any round. This is NOT an UNSAT and must not be reported as one.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
