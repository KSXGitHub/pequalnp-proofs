#!/usr/bin/env python3
"""Has upstream ALREADY answered this step? Check before spending a worker on it.

WHY THIS EXISTS. The desk posts rows whose truth it does not know, and sometimes
the answer is already merged. Two workers were spent today before anyone looked:

  * L-meta-9275 asks for a 10-gate circuit for mask 16237110. Its negation is
    proved VERBATIM on upstream/main in Outside/L_meta_9277.lean - a DIFFERENT,
    adjacent id - so the row is false and there is nothing to exhibit.
  * L-meta-10237 asks for the mask-7874358 lower bound, which Outside/
    L_meta_10237.lean on main already proves in full.

Both type-check in our tree right now. The desk's own sketch for 9275 even says
"the opposite row is offered beside it", so it knows both rows exist and hands
out whichever; believing the posted direction is our job, not the desk's.

So: before dispatching anyone, run this. It looks two ways.
  1. The step's OWN file on upstream/main. If Outside/L_<prog>_<n>.lean is there,
     the step is very likely closed.
  2. The distinctive LITERALS of the statement - long numbers like a mask or an
     edge-list constant - grepped across the merged corpus. That is what found
     L_meta_9277 for a step numbered 9275, which no name-based check would catch.

It never says "unproved": absence of a hit means only that this crude search
found nothing. Read what it points at.
"""

from __future__ import annotations

import json
import pathlib
import re
import subprocess
import sys
from typing import Final

S: Final = pathlib.Path(__file__).absolute().parent
REPO: Final = pathlib.Path("/home/user/pequalnp-proofs")
#: A literal worth grepping: long enough to be distinctive. Masks (16237110),
#: bitmask row sets and packed edge lists all land here; 2, 5, 11 do not.
LITERAL: Final = re.compile(r"\b(\d{5,})\b")


def git(*args: str) -> str:
    p = subprocess.run(  # noqa: S603
        ["/usr/bin/git", *args], cwd=REPO, capture_output=True, text=True, check=False
    )
    return p.stdout


def own_file(step_id: str) -> str | None:
    """`Outside/L_<prog>_<n>.lean` on upstream/main, if the step has one there."""
    m = re.fullmatch(r"L-([a-z0-9]+)-(\d+)", step_id)
    if m is None:
        return None
    path = f"lean/PEqualNP/Outside/L_{m.group(1)}_{m.group(2)}.lean"
    out = git("cat-file", "-e", f"upstream/main:{path}")
    return path if out == "" and git("cat-file", "-t", f"upstream/main:{path}").strip() == "blob" else None


def literal_hits(stmt: str, limit: int = 6) -> dict[str, list[str]]:
    """Merged files mentioning each distinctive literal of the statement."""
    found: dict[str, list[str]] = {}
    seen: set[str] = set()
    for lit in LITERAL.findall(stmt):
        if lit in seen:
            continue
        seen.add(lit)
        out = git("grep", "-l", lit, "upstream/main", "--", "lean/PEqualNP/")
        files = [line.split(":", 1)[-1] for line in out.splitlines() if line.strip()]
        if files:
            found[lit] = files[:limit]
        if len(found) >= limit:
            break
    return found


def report(step_id: str) -> int:
    p = S / "steps" / f"{step_id}.json"
    if not p.exists():
        sys.stdout.write(f"{step_id}: no step record on file\n")
        return 2
    gap = json.load(open(p)).get("gap")
    stmt = str(gap.get("statement", "")) if isinstance(gap, dict) else ""
    sys.stdout.write(f"{step_id}\n")
    mine = own_file(step_id)
    if mine is not None:
        sys.stdout.write(f"  ALREADY ON MAIN: {mine} - the step is very likely closed\n")
    hits = literal_hits(stmt)
    if not hits and mine is None:
        sys.stdout.write("  no merged file matches its own name or any distinctive literal\n")
        sys.stdout.write("  (that is NOT proof it is open - this search is crude. Read the statement.)\n")
        return 0
    for lit, files in hits.items():
        sys.stdout.write(f"  literal {lit} appears in:\n")
        for f in files:
            flag = "  <- ITS OWN FILE" if mine is not None and f == mine else ""
            sys.stdout.write(f"      {f}{flag}\n")
    sys.stdout.write("  READ THESE before dispatching: one may prove the statement, or its NEGATION.\n")
    sys.stdout.write("  A merged negation means the row is FALSE and there is nothing to exhibit.\n")
    return 0


def main(argv: list[str]) -> int:
    if argv and argv[0] != "--all":
        return report(argv[0])
    ids = sorted(p.stem for p in (S / "steps").glob("*.json"))
    flagged = 0
    for sid in ids:
        mine = own_file(sid)
        if mine is not None:
            sys.stdout.write(f"  {sid:16} ALREADY ON MAIN: {mine}\n")
            flagged += 1
    sys.stdout.write(f"\n{flagged} of {len(ids)} steps on file have their own merged L_ file upstream.\n")
    sys.stdout.write("Run `settled.py <step-id>` for the literal search, which catches a negation\n")
    sys.stdout.write("proved under a DIFFERENT id - how L-meta-9275 was found to be false.\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
