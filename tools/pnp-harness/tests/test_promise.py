"""Tests for the counting screen, built from the mistakes it has actually made.

Every case here is a regression, not a hypothetical:

* SOUNDNESS. The bound is a lower bound on monotone size, so it must never
  exceed the true optimum of a mask whose optimum is independently known. Three
  such masks are on file, and if the bound ever rises above one of them the tool
  has started refuting true rows - the worst failure available to it, since a
  wrong FALSE is released irreversibly.
* THE FIFTEEN REFUTED ROWS. Each must still come back FALSE with the floor the
  upstream file quotes. The Lean file is GENERATED from this code, so a silent
  change here would silently change proofs that have already been submitted.
* THE WITNESS. RepPath.path needs its four cells and two side conditions to hold
  exactly; the Lean proof passes the indices this code produces straight into
  the kernel, so a wrong index is a file that will not compile - or, worse, one
  that compiles about the wrong mask.
* THE BUDGET SOURCE. Budgets must come from the posted statement, never a title:
  L-meta-20464 and L-meta-20940 are posted at 5 and 8 while their titles suggest
  6 and 7, and reading a title produced a wrong verdict once.
* --verdict ON A 4-ROW MASK. Callers used to grep --scan with a fixed -A window,
  which found the verdict for 3-row masks and nothing for 4-row ones; a missing
  verdict read as undecided, and two provably false rows nearly survived.
"""

from __future__ import annotations

import unittest

import promise


class Soundness(unittest.TestCase):
    """The bound may never exceed a known optimum."""

    #: (mask, n, m, independently known monotone-or-better optimum, how we know)
    KNOWN = (
        (3824, 4, 4, 6, "upstream's own V_ file"),
        (9999, 4, 4, 6, "our value-row proof"),
        (854, 4, 4, 7, "two independent encoders, UNSAT 1-6 and SAT at 7"),
    )

    def test_bound_never_exceeds_known_optimum(self) -> None:
        for mask, n, m, optimum, how in self.KNOWN:
            least, _lhs, _rhs, _wit = promise.bound(mask, n, m)
            self.assertLessEqual(
                least,
                optimum,
                f"mask {mask}: bound {least} exceeds the known optimum {optimum} ({how});"
                " the screen would now refute a TRUE row",
            )

    def test_known_optima_are_not_refuted_at_their_own_size(self) -> None:
        for mask, n, m, optimum, _how in self.KNOWN:
            least, _l, _r, _w = promise.bound(mask, n, m)
            self.assertLessEqual(least, optimum)


class RefutedRows(unittest.TestCase):
    """The fifteen rows the upstream pull request proves false."""

    #: (step, mask, n, m, posted budget, floor this code must still produce)
    ROWS = (
        ("L-meta-20523", 3517, 3, 5, 7, 8),
        ("L-meta-20940", 101624, 4, 5, 8, 9),
        ("L-meta-20531", 7535, 3, 5, 6, 7),
        ("L-meta-20464", 1093, 3, 5, 5, 6),
        ("L-meta-20460", 249, 3, 5, 6, 7),
        ("L-meta-20456", 111, 3, 5, 5, 6),
        ("L-meta-20525", 3575, 3, 5, 6, 7),
        ("L-meta-20452", 47, 3, 5, 5, 6),
        ("L-meta-21834", 288447, 4, 6, 8, 9),
        ("L-meta-23395", 840563, 4, 6, 9, 10),
        ("L-meta-23335", 815608, 4, 6, 9, 10),
        ("L-meta-23463", 1865321, 4, 6, 9, 10),
        ("L-meta-20922", 39770, 4, 5, 8, 9),
        ("L-meta-21819", 276333, 4, 6, 8, 9),
        ("L-meta-21851", 292863, 4, 6, 7, 8),
    )

    def test_floor_is_unchanged(self) -> None:
        for step, mask, n, m, budget, floor in self.ROWS:
            least, _l, _r, wit = promise.bound(mask, n, m)
            self.assertIsNotNone(wit, f"{step}: lost its path witness")
            self.assertEqual(least, floor, f"{step}: floor moved from {floor} to {least}")
            self.assertLess(budget, least, f"{step}: no longer refuted")

    def test_witness_satisfies_every_hypothesis_of_path(self) -> None:
        for step, mask, n, m, _budget, _floor in self.ROWS:
            a = promise.matrix(mask, n, m)
            wit = promise.path_witness(a, n, m)
            self.assertIsNotNone(wit, step)
            assert wit is not None
            u, x, v, w = wit
            self.assertTrue(a[u][v], f"{step}: A u v must be true")
            self.assertTrue(a[u][w], f"{step}: A u w must be true")
            self.assertTrue(a[x][v], f"{step}: A x v must be true")
            self.assertFalse(a[x][w], f"{step}: A x w must be false")
            self.assertTrue(any(not a[u][q] for q in range(m)), f"{step}: row u needs a false entry")
            self.assertTrue(any(not a[q][v] for q in range(n)), f"{step}: column v needs a false entry")
            self.assertNotEqual(u, x)
            self.assertNotEqual(v, w)


class ForcedSets(unittest.TestCase):
    """forcedL and forcedR against a matrix counted by hand."""

    def test_hand_counted(self) -> None:
        # mask 249 on 3x5 is rows 1..11 / 111.. / ..... - the first row has a
        # true entry in column 0, which row 2 leaves false, so row 0 is forced;
        # row 2 has no true entry at all, so it is not.
        a = promise.matrix(249, 3, 5)
        self.assertEqual(a[0], [True, False, False, True, True])
        self.assertEqual(a[1], [True, True, True, False, False])
        self.assertEqual(a[2], [False] * 5)
        self.assertEqual(promise.forced_left(a, 3, 5), [0, 1])
        self.assertEqual(promise.forced_right(a, 3, 5), [0, 1, 2, 3, 4])

    def test_all_zero_matrix_forces_nothing(self) -> None:
        a = promise.matrix(0, 3, 5)
        self.assertEqual(promise.forced_left(a, 3, 5), [])
        self.assertEqual(promise.forced_right(a, 3, 5), [])
        self.assertIsNone(promise.path_witness(a, 3, 5))

    def test_all_one_matrix_forces_nothing(self) -> None:
        # Every column is true everywhere, so no column is false elsewhere and
        # nothing is forced. A full matrix is also representable by a constant.
        n, m = 3, 5
        a = promise.matrix((1 << (n * m)) - 1, n, m)
        self.assertEqual(promise.forced_left(a, n, m), [])
        self.assertEqual(promise.forced_right(a, n, m), [])


class StatementParsing(unittest.TestCase):
    """The budget and shape come from the statement, never from a title."""

    def test_budget_is_read_from_the_statement(self) -> None:
        nat = chr(0x2115)
        cases = (
            # (statement, mask, n, m, budget) - 20464 and 20940, whose titles disagree
            (
                f"PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (1093 : {nat})"
                ".testBit (5 * u.val + v.val)) 5",
                "1093",
                "3",
                "5",
                "5",
            ),
            (
                f"PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (101624 : {nat})"
                ".testBit (5 * u.val + v.val)) 8",
                "101624",
                "4",
                "5",
                "8",
            ),
            # The untyped binder form upstream also uses.
            (
                f"PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5515944280522376865 : {nat})"
                ".testBit (8 * u.val + v.val)) 24",
                "5515944280522376865",
                "8",
                "8",
                "24",
            ),
        )
        for stmt, mask, n, m, budget in cases:
            got = promise.parse_row(stmt)
            self.assertIsNotNone(got, f"did not parse: {stmt[:70]}")
            assert got is not None
            self.assertEqual(got, (int(mask), int(n), int(m), int(budget)), stmt[:70])

    def test_shared_binder_form_parses(self) -> None:
        # `fun u v : Fin 8 =>` shares one annotation between both binders, which
        # the per-binder pattern does not reach. Rows written this way - the 8 by
        # 8 L-meta-20378 and every 5 by 5 one - were silently reported as not
        # promise rows and never screened.
        nat = chr(0x2115)
        stmt = f"PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7880921 : {nat}).testBit (5 * u.val + v.val)) 9"
        self.assertEqual(promise.parse_row(stmt), (7880921, 5, 5, 9))

    def test_shared_binder_stride_must_match_the_shape(self) -> None:
        # A stride disagreeing with the binder's Fin is not a shape this tool
        # understands, and guessing one would screen the wrong matrix.
        nat = chr(0x2115)
        stmt = f"PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7880921 : {nat}).testBit (6 * u.val + v.val)) 9"
        self.assertIsNone(promise.parse_row(stmt))

    def test_a_two_lit_statement_is_not_mistaken_for_a_promise_row(self) -> None:
        nat = chr(0x2115)
        stmt = (
            "exists C, FanInTwo C and C.size <= 6 and forall i j : Fin 6, C.eval "
            f"(List.ofFn fun k : Fin 6 => decide (k = i or k = j)) = (20287 : {nat}).testBit "
            "(6 * min i.val j.val + max i.val j.val)"
        )
        self.assertIsNone(promise.parse_row(stmt))


class VerdictMode(unittest.TestCase):
    """One row in, one word out - no grep window to get wrong."""

    def test_four_row_masks_reach_a_verdict(self) -> None:
        # The -A7 window found the verdict for a 3-row mask and NOTHING for a
        # 4-row one, and a missing verdict read as undecided.
        for mask, n, m, budget in ((815608, 4, 6, 9), (1865321, 4, 6, 9)):
            least, _l, _r, wit = promise.bound(mask, n, m)
            self.assertIsNotNone(wit)
            self.assertLess(budget, least, f"mask {mask} must be refuted")

    def test_undecided_when_the_budget_meets_the_floor(self) -> None:
        # mask 3309 on 3x5 has floor exactly 7 and was posted at 7: counting
        # cannot settle it, and the row was false only by a separate exhaustion.
        least, _l, _r, _w = promise.bound(3309, 3, 5)
        self.assertEqual(least, 7)
        self.assertGreaterEqual(7, least)


if __name__ == "__main__":
    unittest.main()
