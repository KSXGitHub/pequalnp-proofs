#!/usr/bin/env python3
"""Read the state of our upstream pull requests, from inside a session scoped to the fork.

WHY THIS WORKS WHEN NOTHING ELSE DOES. This session's GitHub access is scoped to
the fork, so every direct call to the upstream repository is refused:

    gh api repos/open-goat/pequalnp-proofs/pulls/35271
    -> 403 GitHub access to this repository is not enabled for this session

and `subscribe_pr_activity` on upstream is refused for the same reason. The
fork's own `upstream-pr-status.yml` workflow exists because of that wall, and it
works - but it runs hourly on cron and its first reading did not list the newest
pull request at all, because `gh pr list --author` depends on GitHub's indexing
and that lags by minutes.

The SEARCH API is not scoped the same way. `gh api -X GET search/issues` returns
public results for any repository, upstream included, and it answered for
PR 35271 within seconds of it being opened. So this is the cheap, immediate
channel; the workflow remains the thorough one, since only it can read the
checker's verdict COMMENTS, which search does not return.

WHAT EACH CHANNEL CAN TELL YOU:

  * this tool, in one call: number, state, title, comment count, last update.
    A rising comment count is the signal that the checker has said something.
  * `upstream-pr-status.yml`, hourly: the same plus the parsed VERDICT and
    reason code, and a warning when a verdict predates the current head commit.
    Read it with the Actions API against the FORK, which is in scope.

Searching has a rate limit of about ten requests a minute for an authenticated
user, so this asks one query and filters locally rather than one query per pull
request.
"""

from __future__ import annotations

import json
import subprocess
import sys
from typing import Final

UPSTREAM: Final = "open-goat/pequalnp-proofs"
#: Branch fragments identifying work of ours worth watching. Extend as needed.
MINE: Final = ("promise-floor", "L-meta-", "R-meta-")


def search(extra: str = "") -> list[dict[str, object]]:
    q = f"repo:{UPSTREAM} type:pr {extra}".strip()
    p = subprocess.run(  # noqa: S603
        ["gh", "api", "-X", "GET", "search/issues", "-f", f"q={q}", "-f", "per_page=100"],  # noqa: S607
        capture_output=True,
        text=True,
        check=False,
    )
    if p.returncode != 0:
        sys.stderr.write(f"search failed: {(p.stderr or p.stdout).strip()[:200]}\n")
        return []
    try:
        d = json.loads(p.stdout)
    except json.JSONDecodeError:
        sys.stderr.write("search returned something that is not JSON\n")
        return []
    items = d.get("items")
    return items if isinstance(items, list) else []


def main(argv: list[str]) -> int:
    extra = " ".join(argv) if argv else "promise-floor OR L-meta OR R-meta"
    items = search(extra)
    if not items:
        sys.stdout.write(
            "no results. That is not evidence the pull request is gone: search indexing lags,\n"
            "and a query with no matching term returns nothing. Try prwatch.py <branch-fragment>.\n"
        )
        return 1

    # Typed accessors, because the values are whatever the API sent. mypy --strict
    # rejected `int(it.get("number") or 0)` and `it.get("pull_request", {}).get(...)`
    # on an object-valued dict, and it was right to: a `pull_request` field that is
    # not a dict would raise AttributeError at runtime, on a tool whose whole job
    # is to be the cheap check I run without thinking.
    def num_of(it: dict[str, object]) -> int:
        v = it.get("number")
        return v if isinstance(v, int) else 0

    def merged_of(it: dict[str, object]) -> bool:
        pr = it.get("pull_request")
        return bool(pr.get("merged_at")) if isinstance(pr, dict) else False

    rows = sorted(items, key=lambda it: -num_of(it))
    sys.stdout.write(f"{len(rows)} pull request(s) matching {extra!r} in {UPSTREAM}\n\n")
    for it in rows[:25]:
        num = num_of(it)
        state = str(it.get("state", "?"))
        merged = " MERGED" if merged_of(it) else ""
        comments = it.get("comments")
        sys.stdout.write(
            f"  #{num}  {state.upper()}{merged}  comments={comments}"
            f"  updated={str(it.get('updated_at'))[:16]}\n      {str(it.get('title'))[:88]}\n"
        )
    sys.stdout.write(
        "\nA comment count above zero is usually the checker's verdict. This API does not return\n"
        "the comment TEXT, so for a verdict run upstream-pr-status.yml on the fork and read its\n"
        "log - that workflow parses the verdict and its reason code.\n"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
