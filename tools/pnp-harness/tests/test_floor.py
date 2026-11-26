"""Regression tests for the cover-size floor screen.

Three things are pinned here, because all three were got wrong at least once:

* the GENERAL count `(s-1)m + k - 1` reproduces every case whose answer we know
  independently - the 15 lines of GQ(2,2) at 34 (the size the desk holds for L-meta-18856),
  the Fano plane at 16, and the width-2 graph of L-meta-9820 at 18;
* the SIDE CONDITION is box-freeness, not pairwise intersection: K(3,3)'s edges pairwise
  share at most one vertex yet its edge function costs 5 gates, so a screen that accepted it
  would call a 5-gate target an 11-gate impossibility;
* the IMPOSSIBILITY SHAPES are read the right way round, including the two that carry no
  leading negation and no literal budget.
"""

from __future__ import annotations

import unittest
from collections.abc import Sequence

import floor
import pointsets


def floor_of(terms: Sequence[tuple[int, ...]]) -> int | None:
    """The gate floor of a term system given as tuples, or None if its shape forbids one."""
    sysm = floor.TermSystem(
        terms=[frozenset(t) for t in terms],
        n=1 + max(p for t in terms for p in t),
        source="test",
        absorbed=0,
        widths={},
    )
    for t in sysm.terms:
        sysm.widths[len(t)] = sysm.widths.get(len(t), 0) + 1
    return floor.count_terms(sysm).floor_for("gates")


def perfect_matchings_of_k6() -> list[tuple[int, ...]]:
    """The 15 perfect matchings of K6 over lexicographic edge indices: the doily's lines."""
    index: dict[tuple[int, int], int] = {}
    for a in range(6):
        for b in range(a + 1, 6):
            index[a, b] = len(index)
    out: list[tuple[int, ...]] = []

    def rec(rest: frozenset[int], acc: tuple[int, ...]) -> None:
        if not rest:
            out.append(tuple(sorted(acc)))
            return
        lo = min(rest)
        for other in sorted(rest - {lo}):
            rec(rest - {lo, other}, (*acc, index[lo, other]))

    rec(frozenset(range(6)), ())
    return out


FANO: list[tuple[int, ...]] = [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]
#: L-meta-9820's graph: the Petersen graph less two edges of a path.
G9820: list[tuple[int, ...]] = [
    (1, 2),
    (3, 4),
    (0, 4),
    (0, 5),
    (1, 6),
    (2, 7),
    (3, 8),
    (4, 9),
    (5, 7),
    (7, 9),
    (6, 9),
    (6, 8),
    (5, 8),
]
K33: list[tuple[int, ...]] = [(i, 3 + j) for i in range(3) for j in range(3)]


class TestKnownFloors(unittest.TestCase):
    def test_doily_is_34(self) -> None:
        lines = perfect_matchings_of_k6()
        self.assertEqual(len(lines), 15)
        self.assertEqual(floor_of(lines), 34)

    def test_fano_is_16(self) -> None:
        self.assertEqual(floor_of(FANO), 16)

    def test_width_two_matches_the_graph_path(self) -> None:
        graph = pointsets.Graph({(u, v) for u, v in G9820}, 10)
        tau, _covers = graph.min_covers()
        self.assertEqual(len(graph.edges) + tau - 1, 18)
        self.assertEqual(floor_of(G9820), 18)

    def test_hitting_set_is_the_vertex_cover_at_width_two(self) -> None:
        for edges in (G9820, K33, FANO[:3]):
            if max(len(t) for t in edges) != 2:
                continue
            graph = pointsets.Graph({(u, v) for u, v in edges}, 1 + max(p for t in edges for p in t))
            tau, _covers = graph.min_covers()
            got, how = floor.min_hitting_set([frozenset(t) for t in edges])
            self.assertEqual(got, tau, how)


class TestShapeCondition(unittest.TestCase):
    def test_k33_is_refused_because_of_its_boxes(self) -> None:
        self.assertEqual(floor.pairwise_max([frozenset(t) for t in K33]), 1)
        self.assertGreater(floor.box_count([frozenset(t) for t in K33]), 0)
        self.assertIsNone(floor_of(K33))

    def test_box_freeness_is_c4_freeness_at_width_two(self) -> None:
        for edges in (G9820, K33):
            graph = pointsets.Graph({(u, v) for u, v in edges}, 1 + max(p for t in edges for p in t))
            boxes = floor.box_count([frozenset(t) for t in edges])
            self.assertEqual(bool(graph.c4_pairs()), bool(boxes))

    def test_a_shared_pair_of_variables_is_refused_above_width_two(self) -> None:
        shared = [(0, 1, 2, 3), (0, 1, 2, 4), (5, 6, 7, 8)]
        self.assertEqual(floor.pairwise_max([frozenset(t) for t in shared]), 3)
        self.assertIsNone(floor_of(shared))

    def test_mixed_widths_get_no_floor(self) -> None:
        self.assertIsNone(floor_of([(0, 1), (2, 3, 4)]))


class TestClaimShapes(unittest.TestCase):
    def test_negated_min_size_is_a_find_one_below_the_threshold(self) -> None:
        stmt = (
            f"{chr(0x00AC)} ({chr(0x2200)} t : {chr(0x2115)}, PEqualNP.MetaComplexity.HasCircuitSize 9 "
            f"(fun x : Fin 9 {chr(0x2192)} Bool => (x 0 && x 4) || (x 1 && x 5)) t {chr(0x2192)} "
            f"15 {chr(0x2264)} t)"
        )
        got = floor.minsize_claim(stmt)
        self.assertIsNotNone(got)
        if got is not None:
            self.assertEqual((got[0], got[1]), ("find", 14))

    def test_positive_min_size_is_a_lower_bound_claim(self) -> None:
        stmt = (
            f"{chr(0x2200)} t : {chr(0x2115)}, PEqualNP.MetaComplexity.HasCircuitSize 9 "
            f"(fun x : Fin 9 {chr(0x2192)} Bool => (x 0 && x 4) || (x 1 && x 5)) t {chr(0x2192)} "
            f"16 {chr(0x2264)} t"
        )
        got = floor.minsize_claim(stmt)
        self.assertIsNotNone(got)
        if got is not None:
            self.assertEqual((got[0], got[1]), ("lower-bound", 16))

    def test_universal_with_false_conclusion_inverts(self) -> None:
        stmt = (
            f"{chr(0x2200)} (C : Circuit), Monotone2 C {chr(0x2192)} C.size {chr(0x2264)} (27 : {chr(0x2115)}) "
            f"{chr(0x2192)} False"
        )
        self.assertEqual(floor.negation_shape(stmt), "universal-false")

    def test_a_plain_find_has_no_shape(self) -> None:
        stmt = "PEqualNP.MetaComplexity.HasCircuitSize 10 (fun x => x 0 && x 1) 17"
        self.assertEqual(floor.negation_shape(stmt), "")
        self.assertIsNone(floor.minsize_claim(stmt))


class TestTermDecoder(unittest.TestCase):
    def test_three_wide_conjuncts_are_read_as_triples(self) -> None:
        stmt = "fun x : Fin 15 " + chr(0x2192) + " Bool => (x 0 && x 9 && x 14) || (x 1 && x 6 && x 14)"
        sysm = floor.term_system(stmt)
        self.assertIsNotNone(sysm)
        if sysm is not None:
            self.assertEqual(sysm.width, 3)
            self.assertEqual(sorted(sorted(t) for t in sysm.terms), [[0, 9, 14], [1, 6, 14]])

    def test_an_absorbed_term_is_dropped(self) -> None:
        stmt = "fun x : Fin 9 " + chr(0x2192) + " Bool => (x 0 && x 1) || (x 0 && x 1 && x 2) || (x 3 && x 4)"
        sysm = floor.term_system(stmt)
        self.assertIsNotNone(sysm)
        if sysm is not None:
            self.assertEqual(sysm.absorbed, 1)
            self.assertEqual(sysm.width, 2)


if __name__ == "__main__":
    unittest.main()


class MismatchAndCutSlices(unittest.TestCase):
    """The fourth impossibility shape, and the slices the floor must not judge.

    Both were found the same way: by reading two freshly drawn steps by hand after the tool
    had already pronounced on them, and finding it wrong about both. Lean characters are
    built with `chr` here for the same reason as in floor.py - this source stays ASCII.
    """

    FORALL = chr(0x2200)
    EXISTS = chr(0x2203)
    ARROW = chr(0x2192)
    IMPL = chr(0x2192)
    LE = chr(0x2264)
    NAT = chr(0x2115)
    NEG = chr(0x00AC)
    IFF = chr(0x2194)
    AND = chr(0x2227)

    def test_mismatch_conclusion_is_a_lower_bound(self) -> None:
        """`exists input, not (eval <-> f)` says "does not compute", so it is a lower bound.

        The shape of L-meta-1894. There is no leading negation and no trailing `False`, so the
        two earlier guards both miss it, and the tool read PG(2,4) at 124 against a floor of
        125 as BELOW FLOOR / likely false - advice to release a step the floor SUPPORTS.
        """
        c = self
        stmt = (
            f"{c.FORALL} (x1 : PEqualNP.CircuitLowerBounds.Circuit), "
            f"PEqualNP.MetaComplexity.Monotone2 x1 {c.IMPL} x1.size {c.LE} (124 : {c.NAT}) {c.IMPL} "
            f"{c.EXISTS} (x5 : Fin (42 : {c.NAT}) {c.ARROW} Bool), "
            f"{c.NEG}(x1.eval (List.ofFn x5) = Bool.true {c.IFF} "
            f"{c.EXISTS} (x6 : Fin (42 : {c.NAT})), x5 x6 = Bool.true)"
        )
        self.assertEqual(floor.negation_shape(stmt), "mismatch")

    def test_nested_parens_do_not_defeat_the_scan(self) -> None:
        """The negated group contains `(List.ofFn x5)`, which a `[^)]*` regex would stop at."""
        stmt = f"{self.NEG}(x1.eval (List.ofFn x5) = Bool.true {self.IFF} True)"
        self.assertIn(self.IFF, floor.negated_group(stmt, 1))

    def test_a_plain_find_is_still_not_a_mismatch(self) -> None:
        """No `not (... <-> ...)` anywhere, so the shape must stay empty and the sign hold."""
        c = self
        stmt = (
            f"{c.EXISTS} (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size {c.LE} (63 : {c.NAT}) {c.AND} "
            f"{c.FORALL} (x2 : Fin (26 : {c.NAT}) {c.ARROW} Bool), x1.eval (List.ofFn x2) = Bool.true"
        )
        self.assertEqual(floor.negation_shape(stmt), "")

    def test_cut_slice_withholds_the_dispatch_advice(self) -> None:
        """A slice of a cut parent gets no dispatch verdict, whichever way the floor fell.

        L-meta-2397's parent reads "... has at least 64 gates" and its own `size <= 63` is the
        assumption the parent refutes, so BELOW FLOOR / "likely false" is backwards. The
        original tag is kept inside the detail so nothing is hidden, only demoted.
        """
        v = floor.Verdict("BELOW FLOOR", "slack 1; do not dispatch", 64, 63)
        out = floor.cut_substep(v, {"title": "A step toward: Order-3 plane: at least 64 gates"})
        self.assertEqual(out.tag, "CUT SLICE - NO DISPATCH VERDICT")
        self.assertIn("BELOW FLOOR", out.detail)
        self.assertEqual((out.effective, out.posted), (64, 63))

    def test_a_standalone_claim_keeps_its_verdict(self) -> None:
        v = floor.Verdict("FLOOR SUPPORTS THE NEGATION", "the floor is 125 > posted 124", 125, 124)
        self.assertEqual(floor.cut_substep(v, {"title": "No circuit of at most 124 gates"}).tag, v.tag)
