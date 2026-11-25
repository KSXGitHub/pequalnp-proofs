#!/usr/bin/env python3
"""Which steps are PROVEN open to reductions, from merged evidence.

Two reductions were closed unchecked today with:

    "this step is not open to reductions (its row in the desk file does not say
     reductions: true), so this reduction will not be checked"

The desk API does not expose that flag - /desk/step returns only state/prs/say -
and no desk file is reachable (every plausible URL 404s, and nothing in the
repository carries the rows). So eligibility cannot be read directly.

It can be INFERRED soundly in one direction: if a reduction of a step has been
MERGED upstream, that step's row must have said reductions: true. Checked against
every data point available:

    L-meta-5266   R_meta_5266_1 merged   -> eligible; our reduction was ACCEPTED
    L-meta-2373   three merged           -> eligible, but slots full
    L-meta-8647   none merged            -> NOT eligible; PR #12891 closed
    L-meta-3457   none merged            -> NOT eligible; PR #12936 closed

So the target is a step with ONE or TWO merged reductions: proven eligible, and
a slot still free under the cap of three. Zero merged reductions means
eligibility is UNKNOWN, and today's evidence is that unknown usually means no.

It also fixes a counting bug that caused the second loss: the earlier check
globbed the WORKING DIRECTORY, so it counted our own uncommitted
R_meta_8647_1.lean and reported "1/3 used" for a step with no merged reductions
at all. Counting must come from upstream/main.

usage: eligible.py            list steps with a free slot and proven eligibility
       eligible.py <step-id>   report one step
"""

from __future__ import annotations

import collections
import pathlib
import re
import subprocess
import sys
from typing import Final

REPO: Final = pathlib.Path("/home/user/pequalnp-proofs")
GIT: Final = "/usr/bin/git"
CAP: Final = 3


def merged_reductions() -> dict[str, list[str]]:
    """Step id -> merged reduction file names, read from upstream/main only."""
    p = subprocess.run(  # noqa: S603
        [GIT, "ls-tree", "-r", "--name-only", "upstream/main", "lean/PEqualNP/Outside/"],
        cwd=REPO,
        capture_output=True,
        text=True,
        check=False,
    )
    out: dict[str, list[str]] = collections.defaultdict(list)
    for line in p.stdout.splitlines():
        m = re.fullmatch(r"lean/PEqualNP/Outside/R_([a-z0-9]+)_(\d+)_(\d+)\.lean", line.strip())
        if m is not None:
            out[f"L-{m.group(1)}-{m.group(2)}"].append(line.rsplit("/", 1)[-1])
    return dict(out)


def report_one(step_id: str, table: dict[str, list[str]]) -> int:
    got = sorted(table.get(step_id, []))
    if not got:
        sys.stdout.write(
            f"{step_id}: NO merged reduction exists.\n"
            "  Eligibility UNKNOWN, and two submissions were closed unchecked in exactly this\n"
            "  situation today. Aim at a PROOF, not a reduction.\n"
        )
        return 1
    if len(got) >= CAP:
        sys.stdout.write(f"{step_id}: eligible, but SLOTS FULL ({len(got)}/{CAP}): {', '.join(got)}\n")
        return 1
    sys.stdout.write(
        f"{step_id}: PROVEN open to reductions ({len(got)}/{CAP} used: {', '.join(got)}).\n"
        "  A reduction here will at least be checked.\n"
    )
    return 0


def main(argv: list[str]) -> int:
    table = merged_reductions()
    if argv:
        return report_one(argv[0], table)
    free = {k: v for k, v in table.items() if 0 < len(v) < CAP}
    sys.stdout.write(
        f"{len(table)} steps have a merged reduction; {len(free)} of those have a free slot.\n"
        "These are the only steps where a reduction is known to be accepted:\n"
    )
    for k in sorted(free, key=lambda s: int(s.rsplit("-", 1)[1])):
        sys.stdout.write(f"  {k:<16} {len(free[k])}/{CAP}  {', '.join(sorted(free[k]))}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
