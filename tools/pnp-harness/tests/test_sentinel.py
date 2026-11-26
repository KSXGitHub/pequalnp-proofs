"""Tests for the sentinel's decision, which is where all its mistakes have been.

`classify` is pure so these need no network. Each case is a failure that has
happened or has cost a row:

* A FAILED DESK CALL IS NOT A DEATH. The first version marked a live row dead on
  one transient curl error, and a marker tells a worker to stop.
* `mine` IS FALSE MEANS THE ROW IS GONE even though the desk still says `leased`:
  that is a lease of ours that expired while another holder took the row, which
  is how L-meta-9754 (1189 points) and L-meta-9747 (1498 points) were lost. A
  worker on such a row is doing unclaimable work just as surely as one on a
  closed row.
* AN UNFAMILIAR STATE IS REPORTED, NEVER ACTED ON. The desk's vocabulary can
  grow, and a word we have not seen is not evidence of anything.
"""

from __future__ import annotations

import unittest

import sentinel


class Classify(unittest.TestCase):
    def test_unreachable_desk_is_not_a_death(self) -> None:
        fate, why = sentinel.classify("?", None, None)
        self.assertEqual(fate, "UNREACHABLE")
        self.assertIn("did not answer", why)

    def test_unreachable_stays_unreachable_whatever_else_is_known(self) -> None:
        for mine in (True, False, None):
            fate, _ = sentinel.classify("?", mine, None)
            self.assertEqual(fate, "UNREACHABLE", f"mine={mine}")

    def test_leased_and_ours_is_alive(self) -> None:
        self.assertEqual(sentinel.classify("leased", True, None)[0], "ALIVE")

    def test_leased_without_a_mine_field_is_alive(self) -> None:
        # The desk omits `mine` when answering about a row it does not think is
        # ours to report on; we hold a lease file, so absence is not evidence
        # against us and must not trigger a marker.
        self.assertEqual(sentinel.classify("leased", None, None)[0], "ALIVE")

    def test_open_is_alive(self) -> None:
        self.assertEqual(sentinel.classify("open", None, None)[0], "ALIVE")

    def test_leased_but_not_ours_is_dead(self) -> None:
        fate, why = sentinel.classify("leased", False, None)
        self.assertEqual(fate, "DEAD")
        self.assertIn("NOT ours", why)

    def test_not_open_is_dead(self) -> None:
        fate, why = sentinel.classify("not_open", None, None)
        self.assertEqual(fate, "DEAD")
        self.assertIn("not_open", why)

    def test_unfamiliar_state_is_reported_not_acted_on(self) -> None:
        fate, why = sentinel.classify("quarantined", None, None)
        self.assertEqual(fate, "UNKNOWN")
        self.assertIn("quarantined", why)

    def test_alive_but_already_merged_upstream_is_dead(self) -> None:
        fate, why = sentinel.classify("open", True, "lean/PEqualNP/Outside/L_meta_1234.lean")
        self.assertEqual(fate, "DEAD")
        self.assertIn("merged upstream", why)

    def test_every_verdict_carries_a_reason(self) -> None:
        for state, mine, merged in (
            ("?", None, None),
            ("leased", True, None),
            ("leased", False, None),
            ("not_open", None, None),
            ("weird", None, None),
        ):
            _fate, why = sentinel.classify(state, mine, merged)
            self.assertTrue(why.strip(), f"{state}/{mine}/{merged} gave no reason")


class AliveVocabulary(unittest.TestCase):
    def test_alive_set_is_what_the_desk_actually_says(self) -> None:
        # Observed in replies this session. If the desk adds a word, classify
        # reports UNKNOWN rather than guessing, which is the safe direction.
        for word in ("leased", "open"):
            self.assertIn(word, sentinel.ALIVE)
        self.assertNotIn("not_open", sentinel.ALIVE)


if __name__ == "__main__":
    unittest.main()
