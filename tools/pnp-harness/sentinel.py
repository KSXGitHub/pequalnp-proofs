#!/usr/bin/env python3
"""Watch the rows we are working and say the moment one stops being worth working.

WHY THIS EXISTS, in time wasted. A worker spent about an hour and a half on
L-meta-909 and only discovered at the very end, because it had been told to
re-check, that the desk had closed the row underneath it: `state: not_open`,
"it is checked already, or the fleet stood it down". Everything it computed was
still true and some of it was worth publishing, but the row could not be claimed
and the last hour of solving bought nothing. Nobody was watching the row while
the work happened.

WHAT A NAME CHECK DOES AND DOES NOT CATCH. The obvious test is whether the step's
own file is on upstream/main - `lean/PEqualNP/Outside/L_<prog>_<n>.lean` - and it
is one git call. It is also the weakest of the three tests, and it would have
missed 909 completely, because 909 was closed WITHOUT any file of that name ever
appearing. Two other ways a row dies:

  * the same mathematics is merged under a DIFFERENT id. L-meta-9275 asked for a
    10-gate circuit whose negation is proved verbatim in L_meta_9277.lean, two
    numbers away. settled.py catches that by grepping the distinctive literals of
    the statement - a mask, an edge list - across the merged corpus.
  * the fleet stands the row down, and no file appears anywhere. Only the desk
    knows. That is 909.

So the authoritative test is the desk's own `state`, one HTTP call per row, and
this tool polls it. The file check comes along for free because it is cheap and
because when it DOES fire it tells you who closed the row.

WHAT IT DOES NOT DO. It never releases a lease, never draws, never kills a
process, and never edits anything a worker is using. It writes a marker file and
a log line, and that is all - a watcher that can take actions of its own is a
watcher that eventually takes a wrong one. Acting on the marker is deliberate.

HOW A WORKER USES IT. Before each long solver call, a worker checks for
`abandon/<step-id>` beside this script; if it exists, the row is dead and the
worker should stop and report what it has. That costs the worker one stat() and
no tokens, which is the point - polling the desk from inside a worker costs a
tool call each time and workers forget.
"""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys
import time
from typing import Final

S: Final = pathlib.Path(__file__).absolute().parent
REPO: Final = S.parent.parent
ABANDON: Final = S / "abandon"
LOG: Final = S / "sentinel.out"
#: Every five minutes. A lease lives 20 minutes from its last beat, so this
#: notices a dead row well inside the window in which work could still be saved.
PERIOD: Final = 300.0
#: The desk states that mean the row can still be claimed by us. Anything else is
#: a reason to stop: `not_open` is closed or stood down, and an unknown state is
#: reported rather than guessed at.
ALIVE: Final = frozenset({"leased", "open", "offerable"})


def say(msg: str) -> None:
    line = f"{time.strftime('%H:%M:%SZ', time.gmtime())} {msg}\n"
    with open(LOG, "a") as fh:
        fh.write(line)
    sys.stdout.write(line)
    sys.stdout.flush()


def held() -> list[str]:
    """The rows we hold a live lease on - exactly the rows a worker may be on."""
    return sorted(p.stem for p in (S / "live").glob("*.lease"))


def desk_state(step_id: str) -> tuple[str, bool | None, str]:
    """(state, mine, raw) from the desk.

    `mine` is the field that matters as much as the state. A reply of
    `state: leased, mine: true` says the row is ours and a worker on it is
    working something it can claim. `state: leased` WITHOUT `mine` says someone
    ELSE holds it - which is what happens when our lease expires unbeaten, and
    that has cost us two of the most valuable rows we ever held (L-meta-9754 at
    1189 points and L-meta-9747 at 1498). A worker in that position is doing
    unclaimable work just as surely as one on a closed row.

    A call that fails or does not parse returns state "?" and mine None. That is
    NOT a death: the first version of this tool treated it as one and marked a
    perfectly live row dead on a single transient curl failure.
    """
    p = subprocess.run(  # noqa: S603
        [str(S / "desk.sh"), "state", step_id],
        capture_output=True,
        text=True,
        check=False,
        cwd=S,
    )
    raw = ((p.stdout or "") + (p.stderr or "")).strip()
    try:
        d = json.loads(raw)
    except (json.JSONDecodeError, ValueError):
        return "?", None, raw[:200]
    mine = d.get("mine")
    return str(d.get("state", "?")), (bool(mine) if mine is not None else None), raw


def merged_file(step_id: str) -> str | None:
    """The step's own declared file, if it is already on upstream/main."""
    rec = S / "steps" / f"{step_id}.json"
    if not rec.is_file():
        return None
    try:
        path = str((json.load(open(rec)).get("gap") or {}).get("file") or "")
    except (OSError, json.JSONDecodeError):
        return None
    if not path:
        return None
    # S607 flags `git` as a partial executable path, i.e. one resolved through
    # PATH. Suppressed with a reason: the arguments are a fixed literal plus a
    # path read from the desk's own step record, the call only tests existence of
    # a blob in an already-fetched ref, and pinning an absolute git would break
    # on any container that puts it elsewhere.
    p = subprocess.run(  # noqa: S603
        ["git", "cat-file", "-e", f"upstream/main:{path}"],  # noqa: S607
        capture_output=True,
        text=True,
        check=False,
        cwd=REPO,
    )
    return path if p.returncode == 0 else None


def sweep() -> int:
    """One pass. Returns the number of rows newly marked dead."""
    ABANDON.mkdir(exist_ok=True)
    rows = held()
    if not rows:
        say("holding nothing; nothing to watch")
        return 0
    dead = 0
    for step_id in rows:
        state, mine, raw = desk_state(step_id)
        marker = ABANDON / step_id

        # A FAILED CALL IS NOT A DEATH. Report it and move on, leaving any
        # existing marker exactly as it was.
        if state == "?":
            say(f"{step_id}: desk unreachable or unparseable, NOT treating as dead: {raw[:120]}")
            continue

        mf = merged_file(step_id)
        if state in ALIVE and mine is not False and mf is None:
            if marker.exists():
                # It came back. Clear the marker rather than leave a stale one
                # that would stop the next worker for no reason.
                marker.unlink()
                say(f"{step_id}: state {state} and ours again, marker CLEARED")
            continue

        # An UNKNOWN state is reported, never acted on: the vocabulary may grow
        # and a word we have not seen is not evidence of anything.
        if state not in ALIVE and state != "not_open":
            say(f"{step_id}: unfamiliar desk state {state!r} - reporting only, no marker: {raw[:120]}")
            continue

        if state == "not_open":
            why = "state=not_open - checked already, or the fleet stood it down"
        elif mine is False:
            why = f"state={state} but NOT ours any more - our lease is gone and another holder has it"
        else:
            why = f"state={state}"
        if mf:
            why += f"; the step's own file is merged upstream: {mf}"

        if marker.exists():
            continue
        marker.write_text(f"{why}\n{raw}\n")
        dead += 1
        say(
            f"{step_id}: DEAD - {why}. Marker written. Stop any worker on this row and"
            " keep whatever it has established; the row cannot be claimed as it stands"
        )
    return dead


def main(argv: list[str]) -> int:
    if "--once" in argv:
        return 0 if sweep() == 0 else 1
    say(f"=== sentinel up, watching {len(held())} held row(s) every {int(PERIOD)}s ===")
    while True:
        try:
            sweep()
        # Broad on purpose: a watcher must never die. BLE001 is not enabled in
        # this project, so no suppression is needed and ruff flags an unused one.
        except Exception as e:
            say(f"error, continuing: {e!r}")
        time.sleep(PERIOD)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
