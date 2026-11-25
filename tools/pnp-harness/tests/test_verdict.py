"""What the checker's verdict comments and logs actually say.

Every fixture here is real output from the tournament, including the two that
retired the shell this replaces: a log line that is the echoed script must be
reported as nothing, and a long log must not be truncated by a pipe.
"""

from __future__ import annotations

import json
import pathlib
import shlex
import subprocess
import sys
import tempfile
import unittest

from lib.verdict import (
    Comment,
    Verdict,
    diagnostic_lines,
    is_echoed_script,
    is_stale,
    latest_verdict,
    strip_log_prefix,
    take_verdict,
)

REAL_REJECTION = """Checked on the base repository at commit `5021e8b7a8`.

**REJECTED (reduce-extra)**

Run: https://github.com/open-goat/pequalnp-proofs/actions/runs/45502817502

This is an automatic message. A new commit on this pull request is checked again.
"""

# The line that broke the old grep: it is the checker's SCRIPT, echoed by
# Actions with an ANSI 36;1 prefix, and it contains the word REFUSED because it
# is the code that prints it.
ECHOED_LINE = (
    "check\tRefuse malformed inputs\t2026-11-24T22:38:33.1091268Z \x1b[36;1m"
    '[ "$GITHUB_REF" = "refs/heads/$DEFAULT_BRANCH" ] || { echo "REFUSED: start this run"; exit 1; }\x1b[0m'
)

REAL_DIAGNOSTICS = (
    "check\tVerdict\t2026-11-24T22:40:02.1000000Z   | REJECTED (reduce-extra): "
    "PEqualNP.Outside.R_meta_5266_1 declares more than its theorem: "
    "[PEqualNP.TopForm.centreless.congr_simp, PEqualNP.CircuitLowerBounds.Circuit.size.eq_1]. "
    "A reduction file holds the one theorem and nothing else\n"
    "check\tVerdict\t2026-11-24T22:40:02.2000000Z VERDICT: REJECTED (checker exit 1)\n"
)


class TakeVerdict(unittest.TestCase):
    def test_reads_the_real_rejection_whole(self) -> None:
        self.assertEqual(
            take_verdict(REAL_REJECTION),
            Verdict(name="REJECTED", code="reduce-extra", run_id="45502817502"),
        )

    def test_reads_an_acceptance_without_a_code(self) -> None:
        self.assertEqual(
            take_verdict("**ACCEPTED**"),
            Verdict(name="ACCEPTED", code=None, run_id=None),
        )

    def test_a_fault_is_not_a_rejection(self) -> None:
        fault = take_verdict("**FAULT** our machine failed")
        assert fault is not None
        self.assertFalse(fault.is_rejection)

    def test_a_rejection_is_a_rejection(self) -> None:
        rejection = take_verdict(REAL_REJECTION)
        assert rejection is not None
        self.assertTrue(rejection.is_rejection)

    def test_declines_a_comment_that_names_no_verdict(self) -> None:
        self.assertIsNone(take_verdict("thanks for the contribution"))

    def test_does_not_read_a_lowercase_word_as_a_verdict(self) -> None:
        self.assertIsNone(take_verdict("this was rejected earlier"))


class LatestVerdict(unittest.TestCase):
    def test_a_later_fault_overrides_an_earlier_rejection(self) -> None:
        found = latest_verdict(["**REJECTED (reduce-extra)**", "**FAULT**"])
        assert found is not None
        self.assertEqual(found.name, "FAULT")
        self.assertFalse(found.is_rejection)

    def test_skips_comments_that_name_no_verdict(self) -> None:
        found = latest_verdict(["**ACCEPTED**", "a human comment"])
        assert found is not None
        self.assertEqual(found.name, "ACCEPTED")

    def test_declines_when_nothing_names_a_verdict(self) -> None:
        self.assertIsNone(latest_verdict(["hello", "world"]))


class EchoedScript(unittest.TestCase):
    def test_recognises_the_line_that_broke_the_old_grep(self) -> None:
        self.assertTrue(is_echoed_script(ECHOED_LINE))

    def test_ordinary_output_is_not_echoed_script(self) -> None:
        self.assertFalse(is_echoed_script("  | REJECTED (reduce-extra): something"))


class StripLogPrefix(unittest.TestCase):
    def test_removes_job_step_and_timestamp(self) -> None:
        self.assertEqual(
            strip_log_prefix("check\tVerdict\t2026-11-24T22:40:02.1000000Z hello"),
            "hello",
        )

    def test_removes_a_bare_timestamp(self) -> None:
        self.assertEqual(strip_log_prefix("2026-11-24T22:40:02.1000000Z hello"), "hello")

    def test_leaves_a_line_with_no_prefix_alone(self) -> None:
        self.assertEqual(strip_log_prefix("hello"), "hello")


class DiagnosticLines(unittest.TestCase):
    def test_reports_the_checkers_own_diagnostics(self) -> None:
        found = diagnostic_lines(REAL_DIAGNOSTICS)
        self.assertEqual(len(found), 2)
        self.assertTrue(found[0].startswith("REJECTED (reduce-extra): PEqualNP.Outside.R_meta_5266_1"))
        self.assertIn("declares more than its theorem", found[0])
        self.assertEqual(found[1], "VERDICT: REJECTED (checker exit 1)")

    def test_reports_nothing_for_an_echoed_script_line(self) -> None:
        self.assertEqual(diagnostic_lines(ECHOED_LINE), [])

    def test_a_long_log_is_not_truncated(self) -> None:
        # The old shell piped into `head`, which killed the writer with SIGPIPE.
        log = "".join(f"x\ty\t2026-11-24T00:00:0{i % 10}.0Z   | line {i}\n" for i in range(500))
        self.assertEqual(len(diagnostic_lines(log)), 500)


if __name__ == "__main__":
    unittest.main()


class StalenessTests(unittest.TestCase):
    """Dating a verdict against the commit it was supposed to judge.

    These encode a real situation. PR #10475 was rejected for `reduce-extra`,
    repaired, and pushed again as efbf664 at 23:18Z. The rejection comment from
    before the repair was still the newest verdict on the pull request, and read
    exactly like a current one. Twice I diagnosed that rejection by inferring
    its age from repository archaeology, and twice I was wrong; the fix is to
    compare timestamps instead of reasoning about them.
    """

    REJECTION_AT = "2026-11-24T23:05:11Z"
    HEAD_AT = "2026-11-24T23:18:00Z"

    def _verdict(self, created_at: str | None) -> Verdict:
        found = take_verdict(REAL_REJECTION, created_at)
        assert found is not None
        return found

    def test_a_verdict_older_than_the_head_commit_is_stale(self) -> None:
        self.assertIs(True, is_stale(self._verdict(self.REJECTION_AT), self.HEAD_AT))

    def test_a_verdict_newer_than_the_head_commit_is_current(self) -> None:
        self.assertIs(False, is_stale(self._verdict("2026-11-24T23:40:00Z"), self.HEAD_AT))

    def test_a_verdict_at_the_very_moment_of_the_commit_is_current(self) -> None:
        self.assertIs(False, is_stale(self._verdict(self.HEAD_AT), self.HEAD_AT))

    def test_an_unknown_comment_date_is_unknown_not_current(self) -> None:
        self.assertIsNone(is_stale(self._verdict(None), self.HEAD_AT))

    def test_an_unknown_commit_date_is_unknown_not_current(self) -> None:
        self.assertIsNone(is_stale(self._verdict(self.REJECTION_AT), None))

    def test_an_unreadable_date_is_unknown_not_current(self) -> None:
        self.assertIsNone(is_stale(self._verdict("last Tuesday"), self.HEAD_AT))

    def test_no_verdict_at_all_is_unknown(self) -> None:
        self.assertIsNone(is_stale(None, self.HEAD_AT))

    def test_offsets_are_compared_as_instants_not_as_text(self) -> None:
        # 23:05Z and 00:05+01:00 are the same instant; a string compare would
        # call the second one newer.
        self.assertIs(False, is_stale(self._verdict("2026-11-25T00:05:11+01:00"), self.REJECTION_AT))

    def test_the_newest_dated_comment_supplies_the_date(self) -> None:
        found = latest_verdict(
            [
                Comment(REAL_REJECTION, self.REJECTION_AT),
                Comment("no verdict here", "2026-11-24T23:50:00Z"),
            ]
        )
        assert found is not None
        self.assertEqual(self.REJECTION_AT, found.created_at)

    def test_plain_strings_still_work_and_carry_no_date(self) -> None:
        found = latest_verdict([REAL_REJECTION])
        assert found is not None
        self.assertEqual("REJECTED", found.name)
        self.assertIsNone(found.created_at)


class EmitQuotingTests(unittest.TestCase):
    """The workflow `eval`s read_verdict.py's output, so values must be quoted."""

    def _run(self, payload: str, *args: str) -> str:
        proc = subprocess.run(  # noqa: S603
            [sys.executable, "read_verdict.py", *args],
            input=payload,
            capture_output=True,
            text=True,
            cwd=pathlib.Path(__file__).resolve().parent.parent,
            check=True,
        )
        return proc.stdout

    def test_a_hostile_comment_body_cannot_escape_into_a_command(self) -> None:
        hostile = "'; touch /tmp/pwned; '"
        payload = json.dumps([{"body": "**REJECTED (reduce-extra)**", "created_at": hostile}])
        out = self._run(payload)
        # Each line must assign exactly one token, and that token must be the
        # original value. shlex.quote only adds quotes where they are needed, so
        # assert the property rather than a particular quoting style.
        got = {}
        for line in out.splitlines():
            key, _, raw = line.partition("=")
            tokens = shlex.split(raw) or [""]
            self.assertEqual(1, len(tokens), f"{key} assigns more than one token: {raw!r}")
            got[key] = tokens[0]
        self.assertEqual("REJECTED", got["VERDICT"])
        self.assertEqual(hostile, got["VERDICT_AT"])

    def test_a_real_shell_eval_recovers_the_values_unchanged(self) -> None:
        # The workflow does `eval "$(... read_verdict.py)"`, so run that for real
        # against a value engineered to break out, inside a temporary directory
        # so the test leaves nothing behind wherever it runs.
        with tempfile.TemporaryDirectory() as box:
            probe = pathlib.Path(box) / "pwned"
            hostile = f"'; touch {probe}; '"
            payload = json.dumps([{"body": "**REJECTED (reduce-extra)**", "created_at": hostile}])
            out = self._run(payload)
            shown = subprocess.run(  # noqa: S603
                ["/usr/bin/env", "bash", "-c", 'eval "$1"; printf "%s" "$VERDICT_AT"', "_", out],
                capture_output=True,
                text=True,
                check=True,
            )
            self.assertFalse(probe.exists(), "eval of the output ran an injected command")
            self.assertEqual(hostile, shown.stdout)
