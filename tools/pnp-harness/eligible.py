#!/usr/bin/env python3
"""Is this step open to reductions? READ THE FLAG. Do not guess.

join.txt says: "If a step you hold is open to reductions (its row in the desk
file says reductions: true, and it is posted to be proved) and you cannot prove
it, you may submit a REDUCTION instead".

The desk publishes that row, and it was in hand the whole time. Not inside
`gap`, which is why a day went by without noticing it: it is a TOP-LEVEL key of
the /desk/next answer, a sibling of `gap` and `lease`.

    {"gap": {...}, "lease": {...}, "reductions_open": true}

Across the 44 steps leased so far it is present-and-true on 32 and absent on 12,
and it predicts every outcome on record:

    L-meta-5266   reductions_open: true   -> reduction ACCEPTED, then merged
    L-meta-2373   reductions_open: true   -> eligible (slots later filled)
    L-meta-8647   ABSENT                  -> PR #12891 closed UNCHECKED
    L-meta-3457   ABSENT                  -> PR #12936 closed UNCHECKED

Absent means no. Two pushes were spent learning that, each of which had passed
check, lint and decls: the gates certify the artifact is correct, never that
anyone will read it.

Two further conditions, neither of them the flag:

  * "posted to be proved" excludes a SEARCH step, whose answer carries `shard`
    and `shards`. Such a step asks for a witness in one range, so there is
    nothing to reduce however its row reads.
  * at most three reductions per step. That count is NOT in the lease answer, so
    it is counted from merged R_ files on upstream/main - and counted there
    rather than in the working tree, which is what made an earlier version
    report "1/3 used" for a step with no merged reductions at all: it was
    globbing our own uncommitted file.

usage: eligible.py             list held steps where a reduction is worth a push
       eligible.py <step-id>   report one step; exit 0 only if a reduction is OK
"""

from __future__ import annotations

import collections
import json
import pathlib
import re
import subprocess
import sys
from typing import Final

# absolute(), not resolve(): this file is symlinked into the live rig so that
# there is one copy of it, and the state it reads (steps/) sits beside the
# SYMLINK, not beside the tracked original. resolve() would follow the link and
# look for steps/ in the repository, finding none.
S: Final = pathlib.Path(__file__).absolute().parent
REPO: Final = pathlib.Path("/home/user/pequalnp-proofs")
GIT: Final = "/usr/bin/git"
CAP: Final = 3


def answer(step_id: str) -> dict[str, object] | None:
    """The whole /desk/next answer for a step, as saved when it was leased."""
    p = S / "steps" / f"{step_id}.json"
    if not p.exists():
        return None
    got: dict[str, object] = json.load(open(p))
    return got


def is_open(ans: dict[str, object]) -> bool:
    """The desk row, read from BOTH places it is published.

    It appears as the top-level `reductions_open` AND as `gap.reductions`, and
    THEY DISAGREE. Across the steps leased today, six carry gap.reductions true
    while the top-level key is absent entirely: 651, 1888, 1900, 2371, 4955 and
    7698. Reading only the top level therefore reported "NOT open to reductions"
    for steps that are open - the opposite of the error this file was written to
    prevent. L-meta-4955 was about to be written off that way with a slot free.
    """
    gap = ans.get("gap")
    in_gap = gap.get("reductions") is True if isinstance(gap, dict) else False
    return ans.get("reductions_open") is True or in_gap


def live_count(ans: dict[str, object]) -> int | None:
    """`gap.reductions_live`: how many reductions are live on this step, 0 to 3.

    This is the desk's own count and it beats inferring from merged R_ files,
    which only sees what has already landed on main. Returns None when the field
    is absent, and the merged-file count is then the only estimate available.
    """
    gap = ans.get("gap")
    if not isinstance(gap, dict):
        return None
    n = gap.get("reductions_live")
    return n if isinstance(n, int) else None


def is_search(ans: dict[str, object]) -> bool:
    """A search step is not `posted to be proved`, so nothing to reduce."""
    return "shard" in ans or "shards" in ans


def merged_reductions(fetch: bool = True) -> dict[str, list[str]]:
    """Step id -> merged reduction file names, read from upstream/main only.

    FETCHES FIRST by default. The fleet merges hundreds of files an hour, so this
    answer goes stale in minutes: L-meta-909 read 2/3 at 08:00 and 3/3 at 08:10,
    a third reduction having landed in between. Acting on the cached figure would
    have meant writing a hypothesis for a slot that no longer existed.
    """
    if fetch:
        subprocess.run(  # noqa: S603
            [GIT, "fetch", "-q", "upstream", "main"],
            cwd=REPO,
            capture_output=True,
            text=True,
            check=False,
        )
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


def report_one(step_id: str) -> int:
    ans = answer(step_id)
    if ans is None:
        sys.stdout.write(
            f"{step_id}: no lease answer saved, so the flag cannot be read.\n"
            "  Lease it again before deciding; do NOT assume reductions are open.\n"
        )
        return 1
    if not is_open(ans):
        sys.stdout.write(
            f"{step_id}: NOT open to reductions - the lease answer carries no "
            "reductions_open: true.\n"
            "  A reduction here is closed UNCHECKED (#12891, #12936 both were).\n"
            "  Aim at a proof, or release the step honestly.\n"
        )
        return 1
    if is_search(ans):
        sys.stdout.write(
            f"{step_id}: a SEARCH step (shard {ans.get('shard')} of {ans.get('shards')}), so it is "
            "not posted to be proved.\n  Search the range; a reduction does not apply.\n"
        )
        return 1
    # Prefer the desk's OWN live count over the merged-file proxy: a merged file
    # is only what has landed on main, while gap.reductions_live counts what is
    # live right now, which is what the cap of three is actually about.
    live = live_count(ans)
    got = sorted(merged_reductions().get(step_id, []))
    n = live if live is not None else len(got)
    src = "desk's reductions_live" if live is not None else "merged R_ files on upstream/main"
    if live is not None and live != len(got):
        sys.stdout.write(f"  (desk says {live} live, {len(got)} merged on main; using the desk's)\n")
    if n >= CAP:
        extra = f": {', '.join(got)}" if got else ""
        sys.stdout.write(f"{step_id}: open to reductions, but SLOTS FULL ({n}/{CAP}{extra})\n")
        return 1
    sys.stdout.write(
        f"{step_id}: OPEN to reductions ({n}/{CAP} used, per the {src}).\n  A reduction will be checked.\n"
    )
    return 0


def main(argv: list[str]) -> int:
    if argv:
        return report_one(argv[0])
    table = merged_reductions()
    rows: list[tuple[str, int, bool]] = []
    for p in sorted((S / "steps").glob("L-*.json")):
        ans = answer(p.stem)
        if ans is None or not is_open(ans) or is_search(ans):
            continue
        n = len(table.get(p.stem, []))
        rows.append((p.stem, n, n < CAP))
    free = [r for r in rows if r[2]]
    sys.stdout.write(f"{len(rows)} held steps are open to reductions; {len(free)} still have a free slot.\n")
    for gid, n, _ in sorted(free, key=lambda r: int(r[0].rsplit("-", 1)[1])):
        sys.stdout.write(f"  {gid:<16} {n}/{CAP} used\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
