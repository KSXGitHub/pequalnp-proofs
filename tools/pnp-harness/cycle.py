#!/usr/bin/env python3
"""Draw rows, classify them by shape, settle what is settleable, release the rest.

WHY THIS IS A FILE AND NOT A SHELL LOOP. This cycle was typed inline as Bash
every time it ran - a `for` loop around desk.sh, python -c, grep -A7 and awk.
Three consequences, all of which happened:

  * the `grep -A7` window found the verdict for a 3-row mask and NOTHING for a
    4-row one, and a missing verdict read as `undecided`, so two provably false
    rows were nearly kept as if they might be winnable;
  * nothing was ever reviewed or tested, because it existed only in a tool call;
  * a row got released on a verdict that had not been established, because the
    loop was also being used as a test fixture.

The decisions here are pure functions with tests. The I/O is thin and every
release prints the verdict it rests on.

WHAT IT CAN SETTLE, and what it must not touch:

  * MONO - a `RepSizeAtMost` row. promise.py decides it from below by counting,
    in milliseconds, citing a kernel-checked lemma. FALSE means release.
  * TWOLIT - a two-lit row. twolit.py runs an exact-size sweep with the desk's
    own circuit as a positive control, in seconds.
  * OTHER - anything else, including `Represents` + `FanInTwo` rows, where the
    monotone lemma does not apply and a 5x5 search at nine gates does not
    return. Those are reported, never guessed at.

A FALSE verdict is irreversible once released, so --dry-run prints every
decision without acting, and nothing is released without a verdict in hand.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
import sys
from enum import Enum
from typing import Final

S: Final = pathlib.Path(__file__).absolute().parent
#: The two-lit engine lives in the session scratchpad, overridable.
import os  # noqa: E402

TWOLIT: Final = (
    pathlib.Path(
        os.environ.get(
            "PNP_JOBS_DIR",
            "/tmp/claude-0/-home-user-pequalnp-proofs/731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/pnp/jobs",  # noqa: S108
        )
    )
    / "twolit.py"
)


class Shape(Enum):
    MONO = "MONO"
    TWOLIT = "TWOLIT"
    OTHER = "OTHER"


class Action(Enum):
    RELEASE_FALSE = "release statement_seems_false"
    SEARCH = "run the two-lit sweep"
    KEEP = "keep and look at it"
    RELEASE_UNREACHABLE = "release out_of_time"


def shape_of(statement: str) -> Shape:
    """Which family a posted statement belongs to.

    Deliberately keyed on the statement, never the title: titles truncate long
    masks (L-meta-24678's title says `mask 3463` where the statement says
    34630387391) and misreport budgets (L-meta-20464 and L-meta-20940 are posted
    at 5 and 8 while their titles suggest 6 and 7).
    """
    if "RepSizeAtMost" in statement:
        return Shape.MONO
    if "k = i" in statement and "min i.val j.val" in statement:
        return Shape.TWOLIT
    return Shape.OTHER


def action_for(shape: Shape, verdict: str) -> Action:
    """What to do, given the shape and whatever verdict the screen produced.

    `verdict` is promise.py's one word for a MONO row and is ignored otherwise.
    UNDECIDED means counting could not settle it, which is NOT evidence of
    falsity - those rows are the only ones that might be TRUE, so they are kept.
    """
    if shape is Shape.MONO:
        if verdict == "FALSE":
            return Action.RELEASE_FALSE
        if verdict == "UNDECIDED":
            return Action.KEEP
        return Action.KEEP
    if shape is Shape.TWOLIT:
        return Action.SEARCH
    return Action.KEEP


def statement_of(step_id: str) -> str:
    p = S / "steps" / f"{step_id}.json"
    try:
        return str((json.load(open(p)).get("gap") or {}).get("statement", ""))
    except (OSError, json.JSONDecodeError):
        return ""


def points_of(step_id: str) -> int:
    p = S / "steps" / f"{step_id}.json"
    try:
        rec = json.load(open(p))
    except (OSError, json.JSONDecodeError):
        return 0
    terms = (rec.get("lease") or {}).get("terms") or {}
    v = terms.get("points")
    return v if isinstance(v, int) else 0


def run(args: list[str], seconds: int = 900) -> tuple[int, str]:
    p = subprocess.run(  # noqa: S603
        args, capture_output=True, text=True, check=False, timeout=seconds, cwd=S
    )
    return p.returncode, (p.stdout or "") + (p.stderr or "")


def draw(selector: list[str]) -> str | None:
    _rc, out = run([str(S / "desk.sh"), "next", *selector], 60)
    for line in out.splitlines():
        if line.startswith("GOT "):
            return line.split()[1]
    return None


def verdict(step_id: str) -> str:
    _rc, out = run([sys.executable, str(S / "promise.py"), "--verdict", step_id], 120)
    return out.strip().splitlines()[-1].strip() if out.strip() else "NOTAROW"


def twolit_sweep(step_id: str) -> tuple[bool, str]:
    """(row is false by exhaustion, log tail)."""
    if not TWOLIT.is_file():
        return False, f"twolit engine not found at {TWOLIT}; set PNP_JOBS_DIR"
    _rc, out = run([sys.executable, "-I", str(TWOLIT), "--step", step_id], 900)
    tail = "\n".join(out.strip().splitlines()[-3:])
    return ("FALSE by exhaustion" in out), tail


def release(step_id: str, reason: str, dry: bool) -> str:
    if dry:
        return f"(dry-run) would release {reason}"
    _rc, out = run([str(S / "desk.sh"), "release", step_id, reason], 60)
    return "released" if '"released"' in out else f"RELEASE FAILED: {out.strip()[:120]}"


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--draws", type=int, default=3)
    ap.add_argument("--selector", action="append", default=[], help="repeatable, e.g. --selector --another")
    ap.add_argument("--dry-run", action="store_true", help="print decisions, change nothing")
    a = ap.parse_args(argv)
    sels = a.selector or ["--another"]

    for i in range(a.draws):
        step = draw([sels[i % len(sels)]])
        if step is None:
            sys.stdout.write("  no step offered\n")
            break
        stmt = statement_of(step)
        shape = shape_of(stmt)
        pts = points_of(step)
        v = verdict(step) if shape is Shape.MONO else "-"
        act = action_for(shape, v)
        sys.stdout.write(f"  {step:16} {pts:>5}pt {shape.value:7} verdict={v:10} -> {act.value}\n")
        if act is Action.RELEASE_FALSE:
            sys.stdout.write(f"      {release(step, 'statement_seems_false', a.dry_run)}\n")
        elif act is Action.SEARCH:
            false_by_sweep, tail = twolit_sweep(step)
            sys.stdout.write("      " + tail.replace("\n", "\n      ") + "\n")
            if false_by_sweep:
                sys.stdout.write(f"      {release(step, 'statement_seems_false', a.dry_run)}\n")
            else:
                sys.stdout.write("      NOT settled - keeping, and this is not an UNSAT\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
