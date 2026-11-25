"""Reading the tournament checker's verdict off a pull request.

The faults that retired the shell this replaces are recorded as tests.

A keyword grep over an Actions log reported the checker's OWN SOURCE as its
output: in an Actions log every line of the running script is echoed with an
ANSI `36;1` prefix, and those lines contain the words a grep looks for, because
they are the code that prints them. So `grep REJECTED` returned
`echo "REFUSED: ..."` from the step definition and never reached the verdict.

A second fault was mechanical: piping a long log into `head` closes the pipe
early and kills the writer with SIGPIPE, which littered the report with
`Broken pipe` lines. Nothing here truncates a stream; a caller slices a list.

The verdict comment itself looks like this, and the two things worth having are
the reason code in the parentheses and the run that holds the diagnostics:

    Checked on the base repository at commit `5021e8b7a8`.

    **REJECTED (reduce-extra)**

    Run: https://github.com/open-goat/pequalnp-proofs/actions/runs/45502817502

    This is an automatic message. A new commit on this pull request is checked again.
"""

from __future__ import annotations

import re
from collections.abc import Sequence
from dataclasses import dataclass
from datetime import datetime
from typing import Final

#: The three verdicts the checker posts. FAULT is its own machine failing: it
#: says nothing about the proof and the file is checked again, so it must never
#: be treated as a rejection.
VERDICTS: Final = ("ACCEPTED", "REJECTED", "FAULT")

#: Actions prefixes each echoed line of the running script with this. A line
#: carrying it is the script, not its output.
ECHOED_SCRIPT: Final = "\033[36;1m"

_VERDICT_RE: Final = re.compile(r"\b(ACCEPTED|REJECTED|FAULT)\b(?:\s*\(([a-z0-9][a-z0-9-]*)\))?")
_RUN_RE: Final = re.compile(r"https://github\.com/[\w.-]+/[\w.-]+/actions/runs/(\d+)")
#: A log line the checker itself emitted, which it prefixes with a pipe.
_DIAGNOSTIC_RE: Final = re.compile(r"^\s*\|\s?(.*)$")
#: Actions puts "<job>\t<step>\t<timestamp> " before each line of output.
_LOG_PREFIX_RE: Final = re.compile(r"^(?:[^\t]*\t){0,2}\d{4}-\d{2}-\d{2}T[\d:.]+Z?\s?")


@dataclass(frozen=True)
class Verdict:
    """What a verdict comment says."""

    name: str
    """One of VERDICTS."""
    code: str | None
    """The reason in parentheses, such as `reduce-extra`, when the checker gave one."""
    run_id: str | None
    """The id of the Actions run holding the diagnostics, when the comment linked one."""
    created_at: str | None = None
    """When the comment was posted, as GitHub's ISO-8601 string, when known.

    This is the only way to tell a verdict on the CURRENT head from one left on
    an earlier commit: the comment body names the base repository's commit, not
    the pull request's own head, so the body alone cannot date itself.
    """

    @property
    def is_rejection(self) -> bool:
        """Whether this verdict means the proof was refused.

        FAULT is not a rejection: the checker's machine failed and the file is
        checked again. Treating it as one would discard a sound proof.
        """
        return self.name == "REJECTED"


@dataclass(frozen=True)
class Comment:
    """One pull request comment: what it says and when it was posted."""

    body: str
    created_at: str | None = None


def take_verdict(body: str, created_at: str | None = None) -> Verdict | None:
    """Read the verdict out of one comment body, or decline.

    The LAST verdict named in the body wins, so a comment that quotes an earlier
    one does not override what it reports.
    """
    matches = list(_VERDICT_RE.finditer(body))
    if not matches:
        return None
    last = matches[-1]
    run = _RUN_RE.search(body)
    return Verdict(
        name=last.group(1),
        code=last.group(2),
        run_id=run.group(1) if run else None,
        created_at=created_at,
    )


def latest_verdict(comments: Sequence[Comment | str]) -> Verdict | None:
    """Read the verdict from the newest comment that names one.

    `comments` is oldest first. A later FAULT or ACCEPTED therefore overrides an
    earlier REJECTED, which is what lets a repaired pull request survive. Plain
    strings are accepted so a caller with no timestamps still works; the verdict
    then simply carries no date and cannot be dated against a commit.
    """
    for item in reversed(comments):
        comment = Comment(item) if isinstance(item, str) else item
        found = take_verdict(comment.body, comment.created_at)
        if found is not None:
            return found
    return None


def _moment(stamp: str | None) -> datetime | None:
    """GitHub's ISO-8601 string as a datetime, or None if absent or unreadable."""
    if not stamp:
        return None
    try:
        return datetime.fromisoformat(stamp.replace("Z", "+00:00"))
    except ValueError:
        return None


def is_stale(verdict: Verdict | None, head_committed_at: str | None) -> bool | None:
    """Whether this verdict was posted BEFORE the pull request's current head.

    A stale verdict judged a commit that no longer exists on the branch, so
    acting on it means acting on an answer to a question no longer being asked.
    This matters because a repair push does not delete the old verdict comment:
    the rejection stays visible and reads exactly like a fresh one.

    Returns None when it cannot be known - either timestamp missing or
    unreadable. None is deliberately not False: twice I diagnosed a rejection by
    inferring its age from surrounding evidence and was wrong both times, so an
    unknown must be reported as unknown and never quietly read as current.
    """
    if verdict is None:
        return None
    posted, committed = _moment(verdict.created_at), _moment(head_committed_at)
    if posted is None or committed is None:
        return None
    return posted < committed


def is_echoed_script(line: str) -> bool:
    """Whether this log line is the running script being echoed, not its output."""
    return ECHOED_SCRIPT in line


def strip_log_prefix(line: str) -> str:
    """Drop the job, step and timestamp columns Actions puts before each line."""
    return _LOG_PREFIX_RE.sub("", line, count=1)


def diagnostic_lines(log: str) -> list[str]:
    """The checker's own diagnostics, in order, with its pipe prefix removed.

    Only lines the checker emitted are returned: echoed script lines are dropped
    first, which is the fault this function exists to prevent.
    """
    found: list[str] = []
    for raw in log.splitlines():
        if is_echoed_script(raw):
            continue
        line = strip_log_prefix(raw)
        matched = _DIAGNOSTIC_RE.match(line)
        if matched is not None:
            found.append(matched.group(1).rstrip())
        elif line.startswith("VERDICT:"):
            found.append(line.rstrip())
    return found
