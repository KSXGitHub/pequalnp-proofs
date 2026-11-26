#!/usr/bin/env python3
"""Keep exactly one poller alive. It has now stopped EIGHT times and each stop costs leases.

WHY THIS EXISTS, in money. A lease dies 20 minutes after its last beat, and the
poller is the only thing beating them. Its stops have cost us two of the most
valuable rows we ever held:

  * L-meta-9754, 1189 points, expired unbeaten and was settled by another agent
    four minutes after we released it;
  * L-meta-9747, 1498 points - a FIND, the highest-value POSITIVE row on the
    desk, which we held UNCONTESTED while an agent worked it - expired during the
    eighth stop and was taken by another holder at 14:30Z.

Six of the eight were deaths; twice it simply ran to the end of its 3500-second
budget and exited cleanly, which looks identical from outside and is just as
costly. So the fix is not "restart it more carefully", it is "do not rely on a
human noticing".

What this does NOT do: it never draws, releases or beats anything itself. It only
starts the poller when no poller is running, which keeps the blast radius at
"one more poller than intended" in the worst case - and it checks for that case
first, so even that cannot happen.
"""

from __future__ import annotations

import os
import pathlib
import subprocess
import sys
import time
from typing import Final

P: Final = pathlib.Path(
    "/tmp/claude-0/-home-user-pequalnp-proofs/731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/pnp"
)
#: How often to look. The poller beats every 75 s and a lease survives 20 minutes
#: from its last beat, so a check every 60 s cannot lose a lease to a stop.
PERIOD: Final = 60.0
#: Matches the poller and nothing else. `pgrep -f` would also match this
#: watchdog's own command line, which is exactly the over-counting that made
#: earlier checks unreliable, so read /proc directly instead.
MARKER: Final = "./poll.sh"


def poller_count() -> int:
    """Live pollers, by reading /proc rather than matching a shell command line."""
    n = 0
    for d in pathlib.Path("/proc").iterdir():
        if not d.name.isdigit():
            continue
        try:
            cl = (d / "cmdline").read_bytes().replace(b"\0", b" ").decode("utf-8", "replace")
        except (OSError, ProcessLookupError):
            continue
        # The poller is `bash ./poll.sh <secs> <maxhold>`; a watchdog or an
        # editor holding the same path in its arguments is not.
        if cl.startswith("bash " + MARKER) or cl.startswith("/bin/bash " + MARKER):
            n += 1
    return n


def start() -> None:
    log = open(P / "poll.out", "a")
    subprocess.Popen(  # noqa: S603
        ["/bin/bash", "./poll.sh", "3500", "8"],
        cwd=P,
        stdout=log,
        stderr=subprocess.STDOUT,
        stdin=subprocess.DEVNULL,
        start_new_session=True,
    )


def main() -> int:
    starts = 0
    while True:
        try:
            n = poller_count()
            if n == 0:
                start()
                starts += 1
                stamp = time.strftime("%H:%M:%SZ", time.gmtime())
                with open(P / "poll.out", "a") as fh:
                    fh.write(f"{stamp} WATCHDOG restarted the poller (restart #{starts})\n")
            elif n > 1:
                stamp = time.strftime("%H:%M:%SZ", time.gmtime())
                with open(P / "poll.out", "a") as fh:
                    fh.write(f"{stamp} WATCHDOG sees {n} pollers; leaving them alone\n")
        except Exception as e:  # noqa: BLE001 - a watchdog must never die
            with open(P / "poll.out", "a") as fh:
                fh.write(f"WATCHDOG error, continuing: {e!r}\n")
        time.sleep(PERIOD)
    return 0


if __name__ == "__main__":
    if "--once" in sys.argv:
        print(f"pollers: {poller_count()}")
        raise SystemExit(0)
    os.chdir(P)
    raise SystemExit(main())
