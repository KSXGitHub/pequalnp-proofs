#!/usr/bin/env python3
"""Keep the idle cores working: a queue of long solver runs, N at a time, forever.

WHY. This box has four cores and for most of the session nought to two were
busy, because long runs were launched one at a time and the cores idled between
them. Solver time costs no tokens - only CPU - so an idle core is pure waste,
and the runs that matter are exactly the ones that need 10^4 seconds rather than
10^2. Four cores over twelve hours is about 1.7 x 10^5 core-seconds, which is in
the range of the sizes that have so far come back DID NOT RETURN.

WHAT IT DOES. Holds SLOTS runs in flight. When one finishes it logs the verdict
and starts the next item in the queue. It never draws, releases, claims or
writes anything into the repository; it runs solvers and writes a log. A SAT on
a row we hold is the one thing worth waking up for, so it is logged in capitals
and the full output is saved where the heartbeat knows to look.

WHAT IT DELIBERATELY LEAVES ALONE. One core, so the poller, the sentinel and a
Lean check still have somewhere to run (check.sh already caps itself at two
concurrent checks, each of which can want several gigabytes of the fifteen).

ORDERING. The queue is value-ordered, not size-ordered:
  1. a WITNESS for a row we hold closes a posted statement, which we have never
     done. Loose, many seeds, because hunting is loose work.
  2. an UNSAT that moves a frontier we have already climbed to - sizes 1 to 8 of
     L-meta-19527 are a genuine tight exhaustion, so 9 and then 10 would settle
     the row outright.
  3. the one-NOT question at a size the measurement could not reach.
Each item says what its result would MEAN, because a verdict whose consequence
nobody recorded is a verdict that gets re-derived later.
"""

from __future__ import annotations

import pathlib
import re
import subprocess
import sys
import time
from typing import Final, NamedTuple

P: Final = pathlib.Path(
    "/tmp/claude-0/-home-user-pequalnp-proofs/731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/pnp"
)
LOG: Final = P / "campaign.out"
#: Three of four cores. The fourth is for the poller, the sentinel and Lean.
SLOTS: Final = 3
#: Per-run wall clock. Long on purpose: the point is to reach sizes that short
#: runs cannot, and a run cut off early is a DID NOT RETURN, which is worth
#: nothing at all.
SECONDS: Final = 5400


class Item(NamedTuple):
    name: str
    argv: list[str]
    cwd: pathlib.Path
    means: str


def mono(mask: int, n: int, m: int, gates: int, seed: int | None, monotone: bool) -> list[str]:
    a = [
        sys.executable, str(P / "p20508" / "rep44m.py"),
        "--mask", str(mask), "--n", str(n), "--m", str(m), "--gates", str(gates),
        "--no-symmetry", "--timeout", str(SECONDS), "--tag", f"camp{seed or 0}",
    ]
    if monotone:
        a.append("--monotone")
    if seed is not None:
        a += ["--solver-arg=--sat", f"--solver-arg=--seed={seed}"]
    return a


#: L-meta-19527: 5x5 mask 3187468, FanInTwo, posted budget 10. Sizes 1 to 8 are
#: a complete tight exhaustion already; 9 and 10 were never reached.
Q: Final[list[Item]] = [
    *[
        Item(
            f"19527 witness s10 seed {s}",
            mono(3187468, 5, 5, 10, s, False),
            P / "p20508",
            "SAT CLOSES L-meta-19527 - our first closed posted row. Route the gate list"
            " through p4873/mklean.py, check.sh it, claim with --proof-of, submit.",
        )
        for s in (104729, 1299709, 15485863, 32452843)
    ],
    Item(
        "19527 witness s9 loose",
        mono(3187468, 5, 5, 9, 86028121, False),
        P / "p20508",
        "SAT at 9 also closes the row, since 9 <= the posted 10, and would be a smaller"
        " witness than asked for.",
    ),
    Item(
        "19527 UNSAT s9 tight",
        [
            sys.executable, str(P / "p20508" / "rep44m.py"),
            "--mask", "3187468", "--n", "5", "--m", "5", "--gates", "9",
            "--distinct-cols", "--timeout", str(SECONDS), "--tag", "camptight9",
        ],
        P / "p20508",
        "UNSAT at 9 extends the tight exhaustion to 1..9. With 10 as well the row is"
        " FALSE outright. On its own it does not settle the row.",
    ),
]


def say(msg: str) -> None:
    line = f"{time.strftime('%H:%M:%SZ', time.gmtime())} {msg}\n"
    with open(LOG, "a") as fh:
        fh.write(line)


def verdict_of(out: str) -> str:
    m = re.search(r"RESULT:\s+([A-Z][A-Z ]*[A-Z]|[A-Z]+)", out)
    return m.group(1).strip() if m else "NO RESULT LINE"


def main() -> int:
    say(f"=== campaign up: {len(Q)} items, {SLOTS} at a time, {SECONDS}s each ===")
    pending = list(Q)
    live: list[tuple[Item, subprocess.Popen[str]]] = []
    while pending or live:
        while pending and len(live) < SLOTS:
            it = pending.pop(0)
            say(f"start  {it.name}")
            live.append(
                (
                    it,
                    subprocess.Popen(  # noqa: S603
                        it.argv,
                        cwd=it.cwd,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.STDOUT,
                        text=True,
                        start_new_session=True,
                    ),
                )
            )
        time.sleep(20)
        for it, pr in list(live):
            if pr.poll() is None:
                continue
            live.remove((it, pr))
            out = pr.stdout.read() if pr.stdout else ""
            v = verdict_of(out)
            say(f"done   {it.name}: {v}")
            if v == "SAT":
                say(f"*** SAT *** {it.name} -- {it.means}")
                (P / f"campaign_SAT_{it.name.replace(' ', '_')}.txt").write_text(out)
            elif v != "UNSAT":
                say(f"       {v} is NOT an UNSAT and must not be reported as one")
            else:
                say(f"       means: {it.means}")
    say("=== campaign done: queue empty ===")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
