"""Tests for the guard that decides whether a search result is an UNSAT.

THE BUG THIS PINS. promisehunt.py recommends releasing a row as false, so its
one job is to tell a finished search from an unfinished one. The guard compared
the verdict against the string "NORETURN" while the engine prints
`RESULT: DID NOT RETURN` on a timeout. So a timeout failed the check, fell
through to the branch below it, and the tool printed

    monotone, exactly 9 gates, loose: DID NOT RETURN
    ... by padding that rules out every smaller size too ... The row is FALSE.

on L-meta-23111, a row that is simply unresolved. Releasing a row as false
cannot be undone, and the whole harness exists to keep a non-return from being
read as a negative result; the tool that recommends the release was the one
place it had crept back in.

So the rule is inverted: only an exact UNSAT counts, and everything else means
we do not know - a timeout, an empty string, a different spelling, a crash
message, or any future wording the engine might print.
"""

from __future__ import annotations

import unittest

import promisehunt


class IsUnsat(unittest.TestCase):
    def test_exact_unsat_is_the_only_truth(self) -> None:
        self.assertTrue(promisehunt.is_unsat("UNSAT"))

    def test_surrounding_whitespace_is_tolerated(self) -> None:
        # The engine's RESULT line is matched with a trailing-space pattern.
        self.assertTrue(promisehunt.is_unsat("UNSAT "))
        self.assertTrue(promisehunt.is_unsat("  UNSAT\n"))

    def test_a_timeout_is_not_an_unsat(self) -> None:
        # The exact string the engine prints, which the old guard let through.
        self.assertFalse(promisehunt.is_unsat("DID NOT RETURN"))

    def test_the_old_sentinel_is_not_an_unsat_either(self) -> None:
        self.assertFalse(promisehunt.is_unsat("NORETURN"))

    def test_sat_is_not_an_unsat(self) -> None:
        self.assertFalse(promisehunt.is_unsat("SAT"))

    def test_nothing_else_counts(self) -> None:
        for v in ("", " ", "unsat", "Unsat", "UNKNOWN", "NO RESULT LINE", "UNSATISFIABLE", "error"):
            self.assertFalse(promisehunt.is_unsat(v), repr(v))

    def test_unsatisfiable_is_rejected_on_purpose(self) -> None:
        # The solver's own word is UNSATISFIABLE; this engine normalises it to
        # UNSAT before we see it. If a future change stops normalising, this
        # must fail loudly rather than quietly accept a different string.
        self.assertFalse(promisehunt.is_unsat("UNSATISFIABLE"))


if __name__ == "__main__":
    unittest.main()
