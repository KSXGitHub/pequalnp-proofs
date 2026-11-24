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
from dataclasses import dataclass
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

    @property
    def is_rejection(self) -> bool:
        """Whether this verdict means the proof was refused.

        FAULT is not a rejection: the checker's machine failed and the file is
        checked again. Treating it as one would discard a sound proof.
        """
        return self.name == "REJECTED"


def take_verdict(body: str) -> Verdict | None:
    """Read the verdict out of one comment body, or decline.

    The LAST verdict named in the body wins, so a comment that quotes an earlier
    one does not override what it reports.
    """
    matches = list(_VERDICT_RE.finditer(body))
    if not matches:
        return None
    last = matches[-1]
    run = _RUN_RE.search(body)
    return Verdict(name=last.group(1), code=last.group(2), run_id=run.group(1) if run else None)


def latest_verdict(bodies: list[str]) -> Verdict | None:
    """Read the verdict from the newest comment that names one.

    `bodies` is oldest first. A later FAULT or ACCEPTED therefore overrides an
    earlier REJECTED, which is what lets a repaired pull request survive.
    """
    for body in reversed(bodies):
        found = take_verdict(body)
        if found is not None:
            return found
    return None


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
