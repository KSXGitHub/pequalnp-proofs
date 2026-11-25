#!/usr/bin/env python3
"""Report the checker's verdict for one pull request, for a workflow to read.

Reads a JSON array of comments on standard input, oldest first, and writes
shell-assignable lines on standard output:

    VERDICT=REJECTED
    CODE=reduce-extra
    RUN_ID=45502817502
    IS_REJECTION=1
    VERDICT_AT=2026-11-24T23:05:11Z
    IS_STALE=1

Each array element is either a bare body string or an object with `body` and
`created_at` (GitHub's own spelling) or `createdAt`. Given the head commit's
date via `--head-committed-at`, IS_STALE says whether the verdict predates the
commit it is shown against: `1` stale, `0` current, `unknown` when either date
is missing. Unknown is never reported as current, because a stale rejection
reads exactly like a fresh one and acting on one wastes a repair.

With `--log`, reads an Actions log on standard input instead and writes the
checker's own diagnostic lines, one per line, with the echoed script dropped.
"""

from __future__ import annotations

import argparse
import json
import shlex
import sys

from lib.verdict import Comment, diagnostic_lines, is_stale, latest_verdict


def _emit(values: dict[str, str]) -> None:
    """Write shell-assignable lines, each value quoted.

    The caller `eval`s these. The values are already narrow - a verdict name, a
    regex-restricted reason code, digits, an ISO date - but quoting them means a
    comment body can never widen into a command, rather than relying on every
    future regex staying narrow.
    """
    for key, value in values.items():
        sys.stdout.write(f"{key}={shlex.quote(value)}\n")


def _as_comment(item: object) -> Comment:
    """One array element as a Comment, accepting a bare body or an object."""
    if isinstance(item, dict):
        stamp = item.get("created_at") or item.get("createdAt")
        return Comment(str(item.get("body", "")), str(stamp) if stamp else None)
    return Comment(str(item))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log", action="store_true", help="filter an Actions log instead")
    parser.add_argument("--limit", type=int, default=0, help="at most this many diagnostic lines, 0 for all")
    parser.add_argument(
        "--head-committed-at",
        default="",
        help="the pull request head commit's date, to date the verdict against",
    )
    args = parser.parse_args(argv)
    text = sys.stdin.read()

    if args.log:
        lines = diagnostic_lines(text)
        if args.limit > 0:
            lines = lines[: args.limit]
        for line in lines:
            sys.stdout.write(line + "\n")
        return 0

    try:
        items = json.loads(text) if text.strip() else []
    except json.JSONDecodeError as error:
        sys.stderr.write(f"could not read the comments as JSON: {error}\n")
        return 2
    if not isinstance(items, list):
        sys.stderr.write("expected a JSON array of comments\n")
        return 2

    found = latest_verdict([_as_comment(item) for item in items])
    stale = is_stale(found, args.head_committed_at or None)
    stale_word = "unknown" if stale is None else str(int(stale))
    if found is None:
        _emit(
            {"VERDICT": "none", "CODE": "", "RUN_ID": "", "IS_REJECTION": "0", "VERDICT_AT": "", "IS_STALE": stale_word}
        )
        return 0
    _emit(
        {
            "VERDICT": found.name,
            "CODE": found.code or "",
            "RUN_ID": found.run_id or "",
            "IS_REJECTION": "1" if found.is_rejection else "0",
            "VERDICT_AT": found.created_at or "",
            "IS_STALE": stale_word,
        }
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
