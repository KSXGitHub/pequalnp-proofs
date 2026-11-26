#!/usr/bin/env python3
"""Stop named dead-end solver jobs, verifying each PID before signalling it.

Why this is a script and not a `pkill -f`: a pattern kill has already done real
damage in this session. The 4873 worker reported two "DID NOT RETURN" results
that were its own `pkill -f` matching the wrapping shell and taking its detached
jobs down - it mistook self-inflicted kills for solver timeouts. And a pattern
broad enough to catch these four jobs also catches the crown search and the
cleanliness sweep, which are the two searches that can still settle something.

So: every PID is named explicitly, and its /proc cmdline must still contain the
expected marker before it is signalled. A PID that has exited, been recycled, or
does not match is reported and left alone.
"""

from __future__ import annotations

import os
import pathlib
import signal
import sys

#: pid -> a substring that must appear in that process's cmdline. The four
#: 4873 jobs: two CEGAR drivers and the cadical child of each. Their positive
#: control at 28 gates - where a solution provably exists - also never returned,
#: so the Fano-scale instances are out of reach and this CPU is pure waste.
TARGETS: dict[int, str] = {
    30654: "cegar4873.py",
    30655: "ceg27p_fano_g27",
    30337: "cegar4873.py",
    30338: "dk4tl_dualK4_g15",
    # Stale `tail -f` followers left over from the same worker.
    30386: "dk4_at15.log",
    30687: "ceg27p.log",
    29706: "cegpos28.log",
    29475: "ceg27.log",
}

#: Markers that must NEVER be signalled, as a second belt: the crown rigidity
#: search and the two pcx/cleanliness searches are live and productive.
PROTECTED: tuple[str, ...] = ("crown_n", "work30/", "work93/", "poll.sh")


def cmdline(pid: int) -> str | None:
    try:
        raw = pathlib.Path(f"/proc/{pid}/cmdline").read_bytes()
    except (FileNotFoundError, ProcessLookupError, PermissionError):
        return None
    return raw.replace(b"\0", b" ").decode("utf-8", "replace")


def main() -> int:
    killed, skipped = 0, 0
    for pid, marker in TARGETS.items():
        cl = cmdline(pid)
        if cl is None:
            sys.stdout.write(f"  {pid}: already gone\n")
            skipped += 1
            continue
        if any(p in cl for p in PROTECTED):
            sys.stdout.write(f"  {pid}: PROTECTED, refusing ({cl[:60]})\n")
            skipped += 1
            continue
        if marker not in cl:
            sys.stdout.write(f"  {pid}: cmdline no longer matches {marker!r}, leaving alone\n")
            skipped += 1
            continue
        try:
            os.kill(pid, signal.SIGTERM)
        except OSError as e:
            sys.stdout.write(f"  {pid}: {e}\n")
            skipped += 1
            continue
        sys.stdout.write(f"  {pid}: SIGTERM sent ({marker})\n")
        killed += 1
    sys.stdout.write(f"reaped {killed}, left {skipped}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
