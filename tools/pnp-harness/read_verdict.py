#!/usr/bin/env python3
"""Report the checker's verdict for one pull request, for a workflow to read.

Reads a JSON array of comment bodies on standard input, oldest first, and
writes shell-assignable lines on standard output:

    VERDICT=REJECTED
    CODE=reduce-extra
    RUN_ID=45502817502
    IS_REJECTION=1

With `--log`, reads an Actions log on standard input instead and writes the
checker's own diagnostic lines, one per line, with the echoed script dropped.
"""

from __future__ import annotations

import argparse
import json
import sys

from lib.verdict import diagnostic_lines, latest_verdict


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log", action="store_true", help="filter an Actions log instead")
    parser.add_argument("--limit", type=int, default=0, help="at most this many diagnostic lines, 0 for all")
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
        bodies = json.loads(text) if text.strip() else []
    except json.JSONDecodeError as error:
        sys.stderr.write(f"could not read the comments as JSON: {error}\n")
        return 2
    if not isinstance(bodies, list):
        sys.stderr.write("expected a JSON array of comment bodies\n")
        return 2

    found = latest_verdict([str(body) for body in bodies])
    if found is None:
        sys.stdout.write("VERDICT=none\nCODE=\nRUN_ID=\nIS_REJECTION=0\n")
        return 0
    sys.stdout.write(
        f"VERDICT={found.name}\n"
        f"CODE={found.code or ''}\n"
        f"RUN_ID={found.run_id or ''}\n"
        f"IS_REJECTION={1 if found.is_rejection else 0}\n"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
