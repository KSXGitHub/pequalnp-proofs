"""What the checker's verdict comments and logs actually say.

Every fixture here is real output from the tournament, including the two that
retired the shell this replaces: a log line that is the echoed script must be
reported as nothing, and a long log must not be truncated by a pipe.
"""

from __future__ import annotations

import unittest

from lib.verdict import (
    Verdict,
    diagnostic_lines,
    is_echoed_script,
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
