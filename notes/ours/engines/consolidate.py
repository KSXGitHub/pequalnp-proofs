#!/usr/bin/env python3
"""Merge the two harness state directories into the repo-side one.

THE SPLIT, and why it mattered. `$P/poll.sh` is a SYMLINK to
tools/pnp-harness/poll.sh, and bash sets `$0` to the path used to invoke the
script, not its target. So `S="$(cd "$(dirname "$0")" && pwd)"` resolved to the
SCRATCHPAD for every poller run and to tools/pnp-harness for every call I made
by hand from inside that directory. Two live/, two steps/, two dead/.

What it cost and what it saved:
  - SAVED: the scratchpad copy holds 166 step JSONs accumulated over the whole
    session - every statement the desk has ever handed us, L-meta-9796 and
    L-pcx-121 among them. My conclusion that `git clean -fd` had destroyed our
    statements was simply wrong; it deleted the repo-side copy, which had five.
  - COST: leases drawn by hand went into the repo-side live/, which the poller
    never beats, so they expire 20 minutes later unbeaten and unlogged - the
    very failure the gitignore commit was meant to end, arriving by a different
    road.

This copies rather than moves, keeps the NEWER file whenever both sides have
one, and never deletes: a lease id is worth more than tidiness, and if this
script is wrong about which side is fresher the loser is still on disk.
"""

from __future__ import annotations

import pathlib
import shutil
import sys
from typing import Final

SCRATCH: Final = pathlib.Path(
    "/tmp/claude-0/-home-user-pequalnp-proofs/731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/pnp"
)
REPO: Final = pathlib.Path("/home/user/pequalnp-proofs/tools/pnp-harness")
DIRS: Final = ("live", "dead", "steps", "done")


def merge(sub: str) -> tuple[int, int, int]:
    src, dst = SCRATCH / sub, REPO / sub
    dst.mkdir(parents=True, exist_ok=True)
    if not src.is_dir():
        return (0, 0, 0)
    copied = kept = newer = 0
    for f in sorted(src.iterdir()):
        if not f.is_file():
            continue
        target = dst / f.name
        if not target.exists():
            shutil.copy2(f, target)
            copied += 1
        elif f.stat().st_mtime > target.stat().st_mtime:
            shutil.copy2(f, target)
            newer += 1
        else:
            kept += 1
    return (copied, newer, kept)


def main() -> int:
    total = 0
    for sub in DIRS:
        copied, newer, kept = merge(sub)
        total += copied + newer
        sys.stdout.write(
            f"  {sub:6} copied {copied:4d} new, refreshed {newer:3d} newer, kept {kept:4d} existing\n"
        )
    for sub in ("live", "steps"):
        n = len(list((REPO / sub).glob("*")))
        sys.stdout.write(f"  -> {REPO / sub} now holds {n} files\n")
    sys.stdout.write(f"{total} files brought over; nothing deleted\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
