"""Tests for the cycle's decisions, which used to be an untested shell loop.

The two pure functions are where a mistake costs a row, so they are tested and
the I/O around them is kept thin. The cases that matter:

* AN UNDECIDED MONO ROW MUST BE KEPT, never released. Those are the only rows of
  that family that might be TRUE - every one counting refutes is false, so an
  undecided verdict is the only place a win can come from. Releasing one would
  throw away the only winnable shape.
* A MISSING OR MALFORMED VERDICT MUST NOT RELEASE ANYTHING. The shell loop read
  a missing verdict as `undecided` by accident, which was harmless only because
  undecided happens to mean keep; the opposite default would have released
  provably-true rows.
* SHAPE COMES FROM THE STATEMENT. Titles truncate masks and misreport budgets.
"""

from __future__ import annotations

import unittest

import cycle


class ShapeOf(unittest.TestCase):
    def test_monotone_promise_row(self) -> None:
        nat = chr(0x2115)
        stmt = (
            "PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => "
            f"(249 : {nat}).testBit (5 * u.val + v.val)) 6"
        )
        self.assertIs(cycle.shape_of(stmt), cycle.Shape.MONO)

    def test_two_lit_row(self) -> None:
        nat = chr(0x2115)
        stmt = (
            "exists C, FanInTwo C and C.size <= 6 and forall i j : Fin 6, C.eval "
            "(List.ofFn fun k : Fin 6 => decide (k = i or k = j)) = "
            f"(20287 : {nat}).testBit (6 * min i.val j.val + max i.val j.val)"
        )
        self.assertIs(cycle.shape_of(stmt), cycle.Shape.TWOLIT)

    def test_fanintwo_represents_row_is_other(self) -> None:
        # The monotone lemma does NOT apply once NOT gates are allowed, and a
        # 5x5 search at nine gates does not return. Must not be mistaken for a
        # row we can settle.
        nat = chr(0x2115)
        stmt = (
            "exists C, FanInTwo C and C.size <= 9 and PEqualNP.Represents.Represents "
            f"(fun u v : Fin 5 => (7880921 : {nat}).testBit (5 * u.val + v.val)) C"
        )
        self.assertIs(cycle.shape_of(stmt), cycle.Shape.OTHER)

    def test_empty_statement_is_other(self) -> None:
        self.assertIs(cycle.shape_of(""), cycle.Shape.OTHER)


class ActionFor(unittest.TestCase):
    def test_false_mono_is_released(self) -> None:
        self.assertIs(cycle.action_for(cycle.Shape.MONO, "FALSE"), cycle.Action.RELEASE_FALSE)

    def test_undecided_mono_is_kept(self) -> None:
        # The only rows of this family that might be TRUE.
        self.assertIs(cycle.action_for(cycle.Shape.MONO, "UNDECIDED"), cycle.Action.KEEP)

    def test_unparsed_or_missing_verdict_never_releases(self) -> None:
        for v in ("NOTAROW", "", "banana", "false", "FALSE "):
            act = cycle.action_for(cycle.Shape.MONO, v)
            if v == "FALSE ":
                # Trailing whitespace is not the verdict word; it must not release.
                self.assertIsNot(act, cycle.Action.RELEASE_FALSE, repr(v))
            else:
                self.assertIsNot(act, cycle.Action.RELEASE_FALSE, repr(v))

    def test_two_lit_always_searches_rather_than_guessing(self) -> None:
        for v in ("FALSE", "UNDECIDED", "NOTAROW", "-"):
            self.assertIs(cycle.action_for(cycle.Shape.TWOLIT, v), cycle.Action.SEARCH)

    def test_other_shapes_are_kept_for_a_human_look(self) -> None:
        for v in ("FALSE", "UNDECIDED", "NOTAROW"):
            self.assertIs(cycle.action_for(cycle.Shape.OTHER, v), cycle.Action.KEEP)


if __name__ == "__main__":
    unittest.main()
