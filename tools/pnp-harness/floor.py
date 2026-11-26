#!/usr/bin/env python3
"""Screen a FIND step against the COVER SIZE FLOOR before dispatching an agent.

Why this exists. A FIND step asks for a small monotone circuit for a given function. When
that function is an OR of m AND-terms, each of width s over a point set, group the terms
under a hitting set of size k (every term contains a chosen CENTRE, each term assigned to
one). A group of d terms at centre p costs

    (s - 2) internal ANDs per term   (s-2)m    the s-1 non-centre reads of each term
  + (d - 1) ORs per group            m - k     combining a group's terms
  + one AND per group                k         against the centre
  + (k - 1) top ORs                  k - 1
  ------------------------------------------
                                     (s-1)m + k - 1

s = 2 is the GRAPH case: terms are edges, a hitting set is a vertex cover, and the count is
the familiar star cover |E| + tau - 1 (for bipartite G, Koenig makes tau the maximum
matching). s = 3 covers point-line systems: the 15 perfect matchings of K6, which are the 15
lines of the generalized quadrangle GQ(2,2), give 2*15 + 5 - 1 = 34, exactly the size the
desk holds for L-meta-18856, whose posted 27 is seven gates below it.

The side condition is NOT "the terms pairwise share at most one variable", which is vacuous
at s = 2 and would pass K(3,3) (whose edge function costs 5 gates against a formula value of
11). What the floor needs is that no PRODUCT OF ORs covers several terms at once, i.e. that
there is no 2x2 BOX: no (s-2)-set C and pairs {a,a'}, {b,b'} with all four of C+{a,b},
C+{a,b'}, C+{a',b}, C+{a',b'} terms. At s = 2 that is precisely C4-freeness (checked here
against `pointsets.c4_pairs` on random graphs). At s >= 3 a box forces two terms sharing
s-1 >= 2 variables, so demanding pairwise intersections of at most one variable implies it -
and that same demand also stops two terms sharing an internal sub-product, which would beat
the count. So: s = 2 wants C4-freeness, s >= 3 wants a partial linear space.

A step whose posted gate bound is BELOW the floor is almost certainly FALSE and must not be
dispatched; a step AT it is constructible and is the best kind of target; a step ABOVE it is
genuinely open.

Three steps drawn today were killed by this count done by hand. It is automated here so the
next hundred cost seconds rather than an agent each.

usage:
    floor.py <step-id>      one step, in full
    floor.py --all          every step record, as a table sorted by points
    floor.py --all --csv    the same table, comma separated
"""

from __future__ import annotations

import json
import pathlib
import re
import sys
from dataclasses import dataclass, field
from typing import Final

import pointsets

#: Lean characters, built with `chr` so this source file stays ASCII: ruff's RUF001/RUF003
#: reject the characters themselves as confusables, and this directory takes no per-file
#: ignore for that.
NAT: Final = chr(0x2115)
LE: Final = chr(0x2264)
NE: Final = chr(0x2260)
ARROW: Final = chr(0x2192)
IN: Final = chr(0x2208)
UPCAST: Final = chr(0x2191)
WEDGE: Final = chr(0x2227)
VEE: Final = chr(0x2228)

#: `x1.size <= (59 : N)` and `C.size <= 9`: the posted bound, ascribed or bare.
SIZE_LE_RE: Final = re.compile(rf"(\w+)\.size\s*{LE}\s*\(?\s*(\d+)\s*(?::\s*{NAT}\s*)?\)?")
#: `x1.size = (18 : N)`: a size clause can be an equality rather than a bound.
SIZE_EQ_RE: Final = re.compile(rf"(\w+)\.size\s*=\s*\(?\s*(\d+)\s*(?::\s*{NAT}\s*)?\)?")
#: `HasCircuitSize 10 (fun ... ) 17`: the budget is the LAST argument, so anchor at the end
#: of the statement. pointsets' own pattern wants a closing paren after the number, which
#: L-meta-9820 does not have, so it reads no budget there at all.
HASSIZE_TAIL_RE: Final = re.compile(rf"HasCircuitSize\b[\s\S]*?\)\s*\(?\s*(\d+)\s*(?::\s*{NAT}\s*)?\)?\s*$")
HASSIZE_ANY_RE: Final = re.compile(r"\)\s*\(?\s*(\d+)\s*\)?")

#: The MODULAR BIPARTITE form, the third way a relation arrives. Two shapes occur.
#:
#: Sum form (L-meta-7161): `(^x1 + ^x2) % (13 : N) in [(0 : N), (1 : N), (3 : N), (9 : N)]`.
MOD_SUM_RE: Final = re.compile(
    rf"\(\s*{UPCAST}?(\w+)\s*\+\s*{UPCAST}?(\w+)\s*\)\s*%\s*\(?\s*(\d+)\s*(?::\s*{NAT}\s*)?\)?\s*{IN}\s*\[([^]]*)\]"
)
#: Offset (difference) form (L-meta-4027): a chain
#: `x4 = x5 or x4 = x5 + (1 : Fin (13 : N)) or x4 = x5 + (3 : Fin ...) or ...`.
MOD_OFF_HEAD_RE: Final = re.compile(rf"\(?\s*(\w+)\s*=\s*(\w+)\s*(?:{VEE}|\))")
MOD_OFF_TERM_RE: Final = re.compile(r"(\w+)\s*=\s*(\w+)\s*\+\s*\(?\s*(\d+)\s*(?::\s*Fin\s*\(?\s*(\d+))?")
#: The GUARDED DIFFERENCE form, a fourth modular shape and the one L-meta-5877 posts:
#: `(^x6 + (21 : N) - ^x5) % (21 : N) in [(0 : N), (5 : N), ...]` with the side guards
#: `^x5 < (21 : N)` and `(21 : N) <= ^x6` beside it. The `+ n` only keeps the subtraction
#: inside N, so the relation is `(b - a) % n` with `a` the low-block index and `b` the raw
#: high-block input index. The sum-form pattern does not match it (there is a subtraction),
#: nor does the offset chain (there is no `=`), so this 298-point step decoded to nothing.
MOD_DIFF_RE: Final = re.compile(
    rf"\(\s*{UPCAST}?(\w+)\s*\+\s*\(?\s*(\d+)\s*(?::\s*{NAT}\s*)?\)?\s*-\s*{UPCAST}?(\w+)\s*\)\s*%"
    rf"\s*\(?\s*(\d+)\s*(?::\s*{NAT}\s*)?\)?\s*{IN}\s*\[([^]]*)\]"
)
#: `x5 != (1 : Fin (13 : N))`: a vertex excluded from one side.
EXCL_RE: Final = re.compile(rf"(\w+)\s*{NE}\s*\(?\s*(\d+)\s*(?::\s*Fin\s*\(?\s*(\d+))?")
#: `Finset (Fin (13 : N)) := {(0 : Fin (13 : N)), (1 : ...), (3 : ...), (9 : ...)}`: the offset
#: set posted as a Finset rather than written into the relation, as L-meta-3773 and
#: L-meta-2091 do. Which of the two shapes it then feeds is decided by its USE below.
FINSET_OFF_RE: Final = re.compile(r"Finset\s*\(\s*Fin\s*\(?\s*(\d+)[^{]*?:=\s*\{([^}]*)\}")
#: `x3 + x4 ` + membership in that Finset: the sum form (L-meta-3773).
FINSET_SUM_USE_RE: Final = re.compile(rf"(\w+)\s*\+\s*(\w+)\s*{IN}")
#: `exists c in that Finset, x2 = x3 + c`: the offset form (L-meta-2091).
FINSET_OFF_USE_RE: Final = re.compile(r"(\w+)\s*=\s*(\w+)\s*\+\s*(\w+)\b")

#: An explicit list of vertex PAIRS, `([(0, 13), (0, 14), ...] : List (N x N))`. The FOURTH
#: source of an edge list and a common one: L-meta-650 posts the whole order-3 plane this
#: way, and the two NEGATED steps L-meta-9728 / L-meta-9789 post their graphs like it too.
#: Neither the number-list scan nor the DNF scan sees anything in these at all.
PAIR_LIST_RE: Final = re.compile(r"\[\s*\(\s*\d+\s*,\s*\d+\s*\)(?:\s*,\s*\(\s*\d+\s*,\s*\d+\s*\))+\s*\]")
PAIR_RE: Final = re.compile(r"\(\s*(\d+)\s*,\s*(\d+)\s*\)")

#: ONE `x i` read of an explicitly written DNF, in either spelling the statements use:
#: ascribed `x4 (0 : Fin (10 : N))` or bare `x 0`. Terms are then grouped by the text
#: BETWEEN consecutive reads, so a term may have ANY width.
#:
#: This is what the pair-only decoders cannot do, and the failure is not silent-safe: on
#: L-meta-18856's 3-wide conjuncts `(x 0 && x 9 && x 14)` the bare-pair pattern matched the
#: FIRST TWO reads of each and the tool reported "explicit DNF of 15 `x i && x j` conjuncts",
#: a 15-edge graph that is nowhere in the statement, then withheld a verdict because that
#: invented graph was not C4-free. The real system is 15 lines of three points with a floor of
#: 34 against a posted 27. A mis-decode that produces a plausible graph is worse than no
#: decode, so width is read first and the pair path is used only when every term is a pair.
READ_RE: Final = re.compile(
    rf"(?P<var>\w+)\s*(?:\(\s*(?P<asc>\d+)\s*:\s*Fin\s*\(\s*(?P<arity>\d+)\s*:\s*{NAT}\s*\)\s*\)"
    rf"|[ \t](?P<bare>\d+)\b)"
)
#: The text between two reads of the SAME term: an `&&`, with parentheses allowed on either
#: side. A `||`, a comma or anything else ends the term, so `(x 1 && x 2) || (x 3 && x 4)`
#: reads as two terms and not as one of width four.
AND_GAP_RE: Final = re.compile(r"[\s)]*&&[\s(]*")

#: A NEGATED statement, `not (exists C, ... size <= N ...)`: "no circuit this small computes
#: f". The floor still applies but its MEANING INVERTS, so this must be detected or a
#: winnable refutation is reported as an impossibility. L-meta-9728 and L-meta-9789 are both
#: of this shape.
NEG: Final = chr(0x00AC)
EXISTS: Final = chr(0x2203)
FORALL: Final = chr(0x2200)
NEG_RE: Final = re.compile(rf"^\s*{NEG}\s*\(")
#: What the negation is OF decides whether the floor translates. Negating an EXISTENTIAL
#: claim ("some circuit of at most N gates computes f", which is what `HasCircuitSize` and
#: `RepSizeAtMost` unfold to) inverts cleanly. Negating a UNIVERSAL one does NOT: many steps
#: here read `not (for all t, HasCircuitSize n f t -> ...)`, whose truth has nothing to do
#: with whether a star cover fits in a budget, and the budget is a bound variable anyway.
#: Inverting those would be a silent category error, so they get no floor verdict at all.
EXISTS_HEADS: Final = (EXISTS, "HasCircuitSize", "RepSizeAtMost")

#: The MIN-SIZE shape, `for all t : N, HasCircuitSize n f t -> B <= t`, with or without a
#: leading negation. It posts its budget as a BOUND VARIABLE with a threshold beside it, so
#: `posted_bound` finds no number and fifteen records - two of them over 225 points - were
#: refused for having no bound at all. Both readings are mechanical:
#:
#:   NEGATED:  not (for all t, HasCircuitSize f t -> B <= t)  ==  HasCircuitSize f (B-1),
#:             because `HasCircuitSize f t` is monotone in t. A plain FIND at B-1 gates.
#:   POSITIVE: for all t, HasCircuitSize f t -> B <= t        ==  minimum size >= B.
#:             A LOWER-BOUND claim: the cover count supports it when the count is at least
#:             B, and REFUTES it when the cover is smaller, because then the cover itself is
#:             a circuit below B and we hold that witness.
#:
#: This is a different shape from the blanket forall-negation guard below, which stays: there
#: the budget is bound by a quantifier whose body is not a size claim at all.
MINSIZE_RE: Final = re.compile(
    rf"({NEG}\s*\(\s*)?{FORALL}\s*(\w+)\s*:\s*{NAT}\s*,[\s\S]*?(?:HasCircuitSize|RepSizeAtMost)\b[\s\S]*?"
    rf"\)\s*\2\s*{ARROW}\s*\(?\s*(\d+)\s*(?::\s*{NAT}\s*)?\)?\s*{LE}\s*\2"
)

#: Which half of the input block each variable indexes. `Fin.castAdd k v` is the LOW block,
#: `Fin.natAdd k v` the HIGH one, so these fix which side of the bipartition is which.
CASTADD_RE: Final = re.compile(rf"Fin\.castAdd\s*\(?\s*(\d+)\s*(?::\s*{NAT}\s*)?\)?\s*(\w+)")
NATADD_RE: Final = re.compile(rf"Fin\.natAdd\s*\(?\s*(\d+)\s*(?::\s*{NAT}\s*)?\)?\s*(\w+)")

#: The side condition this tool CAN cost: a named wire forced equal to `x i || x j`.
#: L-meta-4027 demands one, and whether it is free decides that step.
WIRE_OR_RE: Final = re.compile(
    r"getD[\s\S]{0,120}?=\s*\(\s*(\w+)\s*\(?\s*(\d+)[^|]{0,40}?\|\|\s*\1\s*\(?\s*(\d+)",
)
#: Side conditions this tool can only NAME, not cost.
OUTPUT_POS_RE: Final = re.compile(r"\w+\.output")
WIRE_READ_RE: Final = re.compile(r"\.wires\b")

#: `AndCountCircuit`: the size counts AND GATES ONLY, ORs are free. The all-gates floor says
#: nothing there - a star cover uses one AND per centre, so its AND count is tau, not
#: |E| + tau - 1. L-meta-909 posts 6 AND gates on Petersen (tau = 6), and reading that
#: against the all-gates floor of 20 made the tool declare a 14-gate shortfall on a step that
#: is in fact exactly at its own floor. Cost model before count, always.
ANDCOUNT_RE: Final = re.compile(r"AndCount")

#: Model predicates. The floor binds a MONOTONE model only.
MONO_RE: Final = re.compile(r"Monotone2|IsAO2|AndOrOnly")
#: `x4.op = ...and or x4.op = ...or` written out, as L-meta-4027 does: monotone in all but name.
MONO_OPS_RE: Final = re.compile(rf"op\s*=\s*\S*GateOp\.and\s*{VEE}\s*\w+\.op\s*=\s*\S*GateOp\.or")
NOT_MODEL_RE: Final = re.compile(r"FanInTwo|HasCircuitSize|GateOp\.not")

Edge = tuple[int, int]


def say(line: str) -> None:
    """One report line. `sys.stdout.write`, not `print`: the harness bans T201."""
    sys.stdout.write(line + "\n")


def steps_dir() -> pathlib.Path:
    """Where the step records live.

    `floor.py` is invoked through a symlink beside the step records (the same arrangement
    `pointsets.py` uses), so `__file__` is the symlink's path and its parent holds `steps/`.
    A real path is tried as well so the tool also works when run from the harness directory.
    """
    here = pathlib.Path(__file__).absolute().parent
    argv0 = pathlib.Path(sys.argv[0]).absolute().parent if sys.argv and sys.argv[0] else here
    for cand in (here / "steps", argv0 / "steps", pathlib.Path.cwd() / "steps"):
        if cand.is_dir():
            return cand
    return here / "steps"


@dataclass
class Meta:
    """The scoring fields of a step record.

    `points` is what the desk pays and what the coordinator sorts by; it lives under
    `lease.terms`, NOT under `gap`, and `gap.weight` is a different, smaller number. Reading
    the wrong one ranked a 1013-point step as a 55-point one, so both are kept and printed.
    """

    points: int
    weight: int
    level: str
    kind: str


def meta_of(rec: dict[str, object]) -> Meta:
    gap = rec.get("gap")
    gapd: dict[str, object] = gap if isinstance(gap, dict) else {}
    lease = rec.get("lease")
    leased: dict[str, object] = lease if isinstance(lease, dict) else {}
    terms = leased.get("terms")
    termsd: dict[str, object] = terms if isinstance(terms, dict) else {}

    def num(*cands: object) -> int:
        for c in cands:
            if isinstance(c, int):
                return c
        return 0

    def text(*cands: object) -> str:
        for c in cands:
            if isinstance(c, str) and c:
                return c
        return "?"

    weight = num(gapd.get("weight"))
    return Meta(
        points=num(termsd.get("points"), gapd.get("weight")),
        weight=weight,
        level=text(termsd.get("level"), gapd.get("level")),
        kind=text(termsd.get("kind"), gapd.get("kind")),
    )


# --------------------------------------------------------------------------------------
# relations
# --------------------------------------------------------------------------------------


@dataclass
class Relation:
    """A decoded graph: edges over vertices 0 .. n-1, plus how it was read."""

    edges: set[Edge]
    n: int
    source: str
    sides: tuple[frozenset[int], frozenset[int]] | None = None
    excluded: list[str] = field(default_factory=list)


def _offsets(blob: str, modulus: int) -> list[int]:
    """The offsets listed inside a `[...]` or `{...}`, one per comma-separated element.

    The LEADING numeral of each element only. A naive scan of every numeral in the blob also
    picks the modulus out of each element's own ascription - `(0 : Fin (13 : N))` would yield
    both 0 and 13 - which reported `offsets [0, 1, 3, 9, 13]` for L-meta-3773. Reducing mod
    the modulus happens to hide that one (13 = 0), but it would not hide the next.
    """
    out: set[int] = set()
    for piece in blob.split(","):
        m = re.search(r"\d+", piece)
        if m is not None:
            k = int(m.group(0))
            out.add(k % modulus if modulus else k)
    return sorted(out)


def modular_relation(stmt: str) -> Relation | None:
    """A bipartite incidence graph given by modular arithmetic over Fin n x Fin n.

    Two shapes are read. The SUM form joins `a` on the low block to `b` on the high block
    when `(a + b) % n` is one of the listed offsets. The OFFSET form joins them when
    `a = b + c` for one of the listed `c` (a chain of disjuncts, the bare `a = b` meaning
    offset 0). An inequality such as `b != 1` deletes that vertex from its side.

    The two blocks are vertices `0 .. n-1` and `n .. 2n-1`, which is exactly how the
    statements lay the inputs out (`Fin.castAdd` low, `Fin.natAdd` high), so the vertex
    numbers here are input indices.
    """
    msum = MOD_SUM_RE.search(stmt)
    off: list[int]
    if msum is not None:
        va, vb, modulus = msum.group(1), msum.group(2), int(msum.group(3))
        off = _offsets(msum.group(4), modulus)
        form = "sum"
    elif FINSET_OFF_RE.search(stmt) is not None:
        fm = FINSET_OFF_RE.search(stmt)
        if fm is None:
            return None
        modulus = int(fm.group(1))
        off = _offsets(fm.group(2), modulus)
        use_sum = FINSET_SUM_USE_RE.search(stmt)
        use_off = FINSET_OFF_USE_RE.search(stmt)
        if use_sum is not None:
            va, vb, form = use_sum.group(1), use_sum.group(2), "sum, offsets posted as a Finset"
            msum = use_sum
        elif use_off is not None:
            va, vb, form = use_off.group(1), use_off.group(2), "offset, offsets posted as a Finset"
        else:
            return None
    else:
        terms = [m for m in MOD_OFF_TERM_RE.finditer(stmt) if m.group(4)]
        if not terms:
            return None
        va, vb = terms[0].group(1), terms[0].group(2)
        terms = [m for m in terms if m.group(1) == va and m.group(2) == vb]
        modulus = int(terms[0].group(4))
        found = {int(m.group(3)) for m in terms}
        # a bare `va = vb` disjunct in the same chain is offset 0
        if re.search(rf"{re.escape(va)}\s*=\s*{re.escape(vb)}\s*(?:{VEE}|\))", stmt):
            found.add(0)
        off = sorted(found)
        form = "offset"
    if modulus <= 0 or not off:
        return None

    # which variable indexes which input block
    low = {m.group(2) for m in CASTADD_RE.finditer(stmt)}
    high = {m.group(2) for m in NATADD_RE.finditer(stmt)}
    if vb in low and va in high:
        va, vb = vb, va
        form += ", sides swapped to match castAdd/natAdd"

    drop_a: set[int] = set()
    drop_b: set[int] = set()
    notes: list[str] = []
    for m in EXCL_RE.finditer(stmt):
        if m.group(3) is None or int(m.group(3)) != modulus:
            continue
        k = int(m.group(2))
        if m.group(1) == va:
            drop_a.add(k)
            notes.append(f"low-block vertex {k} excluded")
        elif m.group(1) == vb:
            drop_b.add(k)
            notes.append(f"high-block vertex {k + modulus} (index {k} of its side) excluded")

    edges: set[Edge] = set()
    for a in range(modulus):
        if a in drop_a:
            continue
        for b in range(modulus):
            if b in drop_b:
                continue
            hit = (a + b) % modulus in off if msum is not None else (a - b) % modulus in off
            if hit:
                edges.add((a, modulus + b))
    sides = (
        frozenset(a for a in range(modulus) if a not in drop_a),
        frozenset(modulus + b for b in range(modulus) if b not in drop_b),
    )
    src = f"modular bipartite incidence over Fin {modulus} x Fin {modulus}, offsets {off} ({form})"
    return Relation(edges, 2 * modulus, src, sides, notes)


def modular_diff_relation(stmt: str) -> Relation | None:
    """A bipartite incidence graph given by a GUARDED DIFFERENCE, `(b + n - a) % n in [...]`.

    `a` is the low block (guarded `a < n`) and `b` the high one (guarded `n <= b`), which is
    how the inputs are laid out: vertices `0 .. n-1` then `n .. 2n-1`. The `+ n` inside the
    bracket is there only so the subtraction stays in N, so the edge condition is
    `(b - n - a) % n in offsets` on the side indices. If the guards do not name the two
    variables, the orientation is unknown and nothing is returned rather than guessed.
    """
    m = MOD_DIFF_RE.search(stmt)
    if m is None:
        return None
    vb, shift, va, modulus = m.group(1), int(m.group(2)), m.group(3), int(m.group(4))
    if modulus <= 0 or shift != modulus:
        return None
    off = _offsets(m.group(5), modulus)
    if not off:
        return None
    num = rf"\(?\s*{modulus}\s*(?::\s*{NAT}\s*)?\)?"
    hi_b = re.search(rf"{num}\s*{LE}\s*{UPCAST}?{re.escape(vb)}\b", stmt) is not None
    hi_a = re.search(rf"{num}\s*{LE}\s*{UPCAST}?{re.escape(va)}\b", stmt) is not None
    if hi_a and not hi_b:
        va, vb = vb, va
    elif not hi_b:
        return None
    edges = {(a, modulus + b) for a in range(modulus) for b in range(modulus) if (b - a) % modulus in off}
    sides = (frozenset(range(modulus)), frozenset(range(modulus, 2 * modulus)))
    src = f"modular bipartite incidence over Fin {modulus} x Fin {modulus}, offsets {off} (guarded difference form)"
    return Relation(edges, 2 * modulus, src, sides, [])


def graph_relation(stmt: str) -> Relation | None:
    """A graph from the two forms `pointsets.py` already decodes.

    An explicit DNF of `x i && x j` conjuncts (ascribed or bare), or a bracketed list of
    plain numerals every member of which has exactly two bits. Both are delegated, not
    reimplemented: a sibling may be using that module.
    """
    dnf, dnf_n = pointsets.dnf_edges(stmt)
    n = pointsets.arity(stmt) or dnf_n
    lists = [[int(x) for x in pointsets.NUM_RE.findall(m.group(0))] for m in pointsets.LIST_RE.finditer(stmt)]
    lists = [xs for xs in lists if len(xs) >= 2]
    if n == 0 and lists:
        n = 1 + max(x.bit_length() for xs in lists for x in xs)
    two_bit = [xs for xs in lists if xs and all(len(pointsets.bits(x, n)) == 2 for x in xs)] if n else []
    if two_bit:
        xs = max(two_bit, key=len)
        edges = {(min(pointsets.bits(x, n)), max(pointsets.bits(x, n))) for x in xs}
        return Relation(edges, n, f"number list of {len(xs)} two-bit members")
    if dnf and n:
        return Relation(dnf, n, f"explicit DNF of {len(dnf)} `x i && x j` conjuncts")
    return None


def pair_list_relation(stmt: str) -> Relation | None:
    """A graph from an explicit list of vertex pairs, `([(0, 13), (0, 14), ...] : List (N x N))`.

    The vertex count comes from the `Fin n -> Bool` binder. The longest such list in the
    statement is taken: a step can also carry a short list of offsets or of gate inputs, and
    the edge list is the long one.
    """
    best: list[tuple[int, int]] = []
    for m in PAIR_LIST_RE.finditer(stmt):
        got = [(int(a), int(b)) for a, b in PAIR_RE.findall(m.group(0))]
        if len(got) > len(best):
            best = got
    if len(best) < 3:
        return None
    w = pointsets.WIDTH_RE.search(stmt)
    n = int(w.group(1) or w.group(2)) if w else 0
    if not n:
        n = 1 + max(max(u, v) for u, v in best)
    edges = {(min(u, v), max(u, v)) for u, v in best if u != v and u < n and v < n}
    if not edges:
        return None
    return Relation(edges, n, f"explicit list of {len(edges)} vertex pairs")


def minsize_claim(stmt: str) -> tuple[str, int, str] | None:
    """The MIN-SIZE shape, as (reading, posted bound, how it was read), or None.

    `find` is the negated reading: a circuit of at most B-1 gates is claimed to exist, so it
    is screened exactly like any other FIND. `lower-bound` is the positive reading: every
    circuit for the function is claimed to need at least B gates, which the cover count
    supports or refutes the other way round.
    """
    m = MINSIZE_RE.search(stmt)
    if m is None:
        return None
    threshold = int(m.group(3))
    if m.group(1) is not None:
        if threshold < 1:
            return None
        return (
            "find",
            threshold - 1,
            f"negated min-size claim: some circuit has size < {threshold}, i.e. at most {threshold - 1} gates",
        )
    return (
        "lower-bound",
        threshold,
        f"min-size claim: every circuit for the function needs at least {threshold} gates",
    )


def negation_shape(stmt: str) -> str:
    """ "", `exists`, `forall`, `other` or `universal-false`: what, if anything, is negated.

    Decided by which marker comes FIRST after the leading `not (`, so a `have ...;` preamble
    and any nesting further in are both harmless.

    `universal-false` is the shape `for all C, ... C.size <= N ... -> False`, which is a
    negated existential wearing a universal's clothes: no leading `not` to find, so the tool
    read three such steps as FIND rows and INVERTED their verdicts - L-meta-2091 and
    L-meta-2116 were printed BELOW FLOOR / "do not dispatch, likely false" when the floor is
    exactly what makes their size hypothesis unsatisfiable and the claim TRUE, and
    L-meta-7698 was printed AT FLOOR / "best kind of target" when the cover fitting the
    budget is what makes its hypothesis satisfiable. Being wrong-signed about which steps to
    dispatch is the one failure this screen must not have.
    """
    if NEG_RE.search(stmt) is None:
        body = stmt.rstrip()
        if body.endswith("False") and (ARROW in body or FORALL in body):
            return "universal-false"
        return ""
    body = stmt[stmt.index(NEG) + 1 :]
    hits = [body.index(h) for h in EXISTS_HEADS if h in body]
    i_e = min(hits) if hits else None
    i_a = body.index(FORALL) if FORALL in body else None
    if i_e is None:
        return "forall" if i_a is not None else "other"
    if i_a is None or i_e < i_a:
        return "exists"
    return "forall"


def relation(stmt: str) -> Relation | None:
    return graph_relation(stmt) or pair_list_relation(stmt) or modular_relation(stmt) or modular_diff_relation(stmt)


# --------------------------------------------------------------------------------------
# term systems: the same count for AND-terms of any width
# --------------------------------------------------------------------------------------


@dataclass
class TermSystem:
    """An OR of AND-terms read off a statement: the terms, how they were read, their widths."""

    terms: list[frozenset[int]]
    n: int
    source: str
    absorbed: int
    widths: dict[int, int]

    @property
    def width(self) -> int | None:
        """The common term width s, or None when the terms are of mixed width."""
        return next(iter(self.widths)) if len(self.widths) == 1 else None

    @property
    def points(self) -> list[int]:
        return sorted({p for t in self.terms for p in t})


def dnf_terms(stmt: str) -> tuple[list[frozenset[int]], int]:
    """The AND-terms of an explicitly written DNF, of any width, plus the arity.

    A term is a maximal run of reads of the SAME variable joined by `&&`. Runs of one read
    are not terms: a lone `x 0` is no conjunct, and requiring two keeps stray matches such as
    `HasCircuitSize 15` (which the bare branch reads as the variable `HasCircuitSize`) out.
    A repeated index inside a term collapses, so `x 1 && x 1 && x 2` is the pair {1, 2}.
    """
    reads: list[tuple[str, int, int, int]] = []
    arity = 0
    for m in READ_RE.finditer(stmt):
        asc, bare = m.group("asc"), m.group("bare")
        if asc is not None:
            arity = max(arity, int(m.group("arity")))
            idx = int(asc)
        elif bare is not None:
            idx = int(bare)
        else:
            continue
        reads.append((m.group("var"), idx, m.start(), m.end()))
    if not arity:
        w = pointsets.WIDTH_RE.search(stmt)
        arity = int(w.group(1) or w.group(2)) if w is not None else 0

    terms: list[frozenset[int]] = []
    run: list[int] = []
    prev: tuple[str, int, int, int] | None = None
    for cur in reads:
        joined = prev is not None and cur[0] == prev[0] and AND_GAP_RE.fullmatch(stmt[prev[3] : cur[2]]) is not None
        if joined:
            run.append(cur[1])
        else:
            if len(run) >= 2:
                terms.append(frozenset(run))
            run = [cur[1]]
        prev = cur
    if len(run) >= 2:
        terms.append(frozenset(run))

    if arity:
        terms = [t for t in terms if all(0 <= i < arity for i in t)]
    out: list[frozenset[int]] = []
    seen: set[frozenset[int]] = set()
    for t in terms:
        if len(t) >= 2 and t not in seen:
            seen.add(t)
            out.append(t)
    return out, arity


def term_system(stmt: str) -> TermSystem | None:
    """The DNF of a statement as a term system, with absorbed terms dropped.

    A term that strictly CONTAINS another is redundant in an OR (x1x2 || x1x2x3 = x1x2), so
    it is dropped before the widths are judged: otherwise one absorbed term would make a
    uniform system look mixed and the floor would be withheld for no reason.
    """
    terms, n = dnf_terms(stmt)
    if len(terms) < 2:
        return None
    kept = [t for t in terms if not any(o < t for o in terms)]
    widths: dict[int, int] = {}
    for t in kept:
        widths[len(t)] = widths.get(len(t), 0) + 1
    shape = "x".join(str(w) for w in sorted(widths)) if len(widths) > 1 else str(next(iter(widths)))
    src = f"explicit DNF of {len(kept)} AND-terms of width {shape}"
    return TermSystem(kept, n, src, len(terms) - len(kept), widths)


def pairwise_max(terms: list[frozenset[int]]) -> int:
    """The largest number of variables two distinct terms share."""
    best = 0
    for i, a in enumerate(terms):
        for b in terms[i + 1 :]:
            best = max(best, len(a & b))
    return best


def box_count(terms: list[frozenset[int]]) -> int:
    """How many 2x2 BOXES the system contains: the obstruction the floor must rule out.

    A box is a common (s-2)-set C and pairs {a,a'}, {b,b'} with all four C+{a,b} terms, which
    is covered by the single product (OR of {a,a'}) AND (OR of {b,b'}) AND C - four terms for
    the price of about one. Two terms sharing exactly s-2 variables leave two variables each;
    either way of pairing those off is a candidate box, so both are tried. At s = 2 this
    counts C4s, and it agrees with `pointsets.Graph.c4_pairs` being nonzero.
    """
    table = set(terms)
    count_ = 0
    for i, a in enumerate(terms):
        for b in terms[i + 1 :]:
            common = a & b
            if len(common) + 2 != len(a) or len(a) != len(b):
                continue
            (u1, u2), (v1, v2) = sorted(a - common), sorted(b - common)
            for x, y in (((u1, v2), (u2, v1)), ((u1, v1), (u2, v2))):
                if (common | set(x)) in table and (common | set(y)) in table:
                    count_ += 1
                    break
    return count_


#: Branch and bound nodes a minimum hitting set may cost before the tool gives up. A
#: non-return is never a verdict, so exceeding this prints NOT COMPUTED and withholds the
#: floor rather than hanging the screen on one pathological record.
HITTING_NODE_CAP: Final = 300_000


def min_hitting_set(terms: list[frozenset[int]]) -> tuple[int | None, str]:
    """The size of a minimum hitting set of the terms, exactly, or None if the search caps.

    Branch and bound: branch on the smallest uncovered term (one of its points must be
    chosen), bound below by a greedy packing of pairwise disjoint uncovered terms, each of
    which needs a point of its own. For width-2 systems this is the minimum vertex cover,
    and it is checked against `pointsets.Graph.min_covers` on random graphs.
    """
    if not terms:
        return 0, "no terms"
    greedy: set[int] = set()
    for t in sorted(terms, key=sorted):
        if not (t & greedy):
            greedy.add(min(t))
    best = len(greedy)
    nodes = 0
    capped = False

    def lower_bound(rem: list[frozenset[int]]) -> int:
        used: set[int] = set()
        packed = 0
        for t in rem:
            if not (t & used):
                packed += 1
                used |= t
        return packed

    def rec(rem: list[frozenset[int]], chosen: int) -> None:
        nonlocal best, nodes, capped
        if capped:
            return
        nodes += 1
        if nodes > HITTING_NODE_CAP:
            capped = True
            return
        if not rem:
            best = min(best, chosen)
            return
        if chosen + lower_bound(rem) >= best:
            return
        pivot = min(rem, key=len)
        for p in sorted(pivot):
            rec([t for t in rem if p not in t], chosen + 1)

    rec(sorted(terms, key=sorted), 0)
    if capped:
        return None, f"NOT COMPUTED (branch and bound passed {HITTING_NODE_CAP} nodes)"
    return best, "exhaustive minimum hitting set (branch and bound)"


@dataclass
class TermCounted:
    """Everything the floor is computed from, for a term system of any width."""

    sys: TermSystem
    pair_max: int
    boxes: int
    k: int | None
    k_how: str

    @property
    def shape_ok(self) -> bool:
        """Whether the cover count can be a floor at all for this system's shape."""
        if self.sys.width is None or self.boxes:
            return False
        return self.sys.width == 2 or self.pair_max <= 1

    def floor_for(self, kind: str) -> int | None:
        s, k = self.sys.width, self.k
        if s is None or k is None or not self.shape_ok:
            return None
        m = len(self.sys.terms)
        if kind == "ands":
            return (s - 2) * m + k
        if kind == "gates":
            return (s - 1) * m + k - 1
        return None

    def formula_for(self, kind: str) -> str:
        s, m, k = self.sys.width, len(self.sys.terms), self.k
        if kind == "ands":
            return f"(s-2)m + k = {s}-2 times {m} + {k}"
        return f"(s-1)m + k - 1 = ({s} - 1)*{m} + {k} - 1"

    def no_floor_reason(self, kind: str) -> str:
        if kind == "unknown":
            return "the cost model is not recognised, so the posted number may not count gates at all"
        if self.sys.width is None:
            shape = ", ".join(f"{c} of width {w}" for w, c in sorted(self.sys.widths.items()))
            return f"the terms are of MIXED width ({shape}); this count needs one width and does not average"
        if self.boxes:
            return (
                f"the system has {self.boxes} 2x2 box(es), so a product of ORs covers several terms at"
                " once and the cover count is not a floor (at width 2 this is exactly a C4)"
            )
        if self.pair_max > 1:
            return (
                f"two terms share {self.pair_max} variables, so they can share an internal sub-product"
                " (and a box may exist); the count needs a partial linear space at width >= 3"
            )
        if self.k is None:
            return f"k {self.k_how}"
        return "no floor"

    def evidence_note(self) -> str:
        if self.sys.width is not None and self.sys.width >= 3:
            return (
                " [width >= 3: the cover SHAPE is unproven for us - tightness was only checked in small"
                " sub-cases by exact synthesis, so this is WEAKER evidence than the width-2 case]"
            )
        return ""

    def structural_note(self) -> str:
        if self.sys.width is None:
            return "mixed term widths"
        bits = [f"s={self.sys.width}"]
        if self.boxes:
            bits.append(f"{self.boxes} box(es)")
        elif self.pair_max > 1:
            bits.append(f"two terms share {self.pair_max} variables")
        elif self.sys.width >= 3:
            bits.append("cover shape unproven: weaker evidence")
        if self.sys.absorbed:
            bits.append(f"{self.sys.absorbed} absorbed term(s) dropped")
        return "; ".join(bits)

    def cover_label(self) -> str:
        return "cover" if self.sys.width != 2 else "star cover"


def count_terms(sys_: TermSystem) -> TermCounted:
    k, how = min_hitting_set(sys_.terms)
    return TermCounted(sys_, pairwise_max(sys_.terms), box_count(sys_.terms), k, how)


# --------------------------------------------------------------------------------------
# the count
# --------------------------------------------------------------------------------------


def max_matching(adj: dict[int, set[int]], left: frozenset[int]) -> int:
    """Maximum matching by augmenting paths, so Koenig gives tau on a bipartite graph."""
    mate: dict[int, int] = {}

    def augment(u: int, seen: set[int]) -> bool:
        for v in sorted(adj.get(u, set())):
            if v in seen:
                continue
            seen.add(v)
            if v not in mate or augment(mate[v], seen):
                mate[v] = u
                return True
        return False

    return sum(1 for u in sorted(left) if adj.get(u) and augment(u, set()))


@dataclass
class Counted:
    """Everything the floor is computed from."""

    rel: Relation
    graph: pointsets.Graph
    c4_pairs: int
    bipartite: tuple[frozenset[int], frozenset[int]] | None
    tau: int | None
    tau_how: str
    side_costs: list[tuple[str, int]]

    def floor_for(self, kind: str) -> int | None:
        """The cheapest star cover under the given cost model, or None if it says nothing."""
        if self.tau is None or self.c4_pairs:
            return None
        if kind == "ands":
            return self.tau
        if kind == "gates":
            return len(self.graph.edges) + self.tau - 1
        return None

    def formula_for(self, kind: str) -> str:
        if kind == "ands":
            return "one AND per centre: tau"
        return f"|E| + tau - 1 = {len(self.graph.edges)} + {self.tau} - 1"

    def no_floor_reason(self, kind: str) -> str:
        """Why this graph yields no floor. The width-2 instance of the general shape test."""
        if kind == "unknown":
            return "the cost model is not recognised, so the posted number may not count gates at all"
        if self.c4_pairs:
            return "graph is not C4-free"
        return f"tau {self.tau_how}"

    def evidence_note(self) -> str:
        """Width 2 is the case the star normal form argument covers, so nothing extra to add."""
        return ""

    def structural_note(self) -> str:
        return f"not C4-free ({self.c4_pairs} pairs)" if self.c4_pairs else ""

    def cover_label(self) -> str:
        return "star cover"


#: Brute-forcing a minimum cover enumerates C(n, k) subsets; past this many vertices the
#: tool says it did not compute tau rather than hanging. A non-return is never a verdict.
BRUTE_VERTEX_CAP: Final = 24


def count(rel: Relation) -> Counted:
    g = pointsets.Graph(rel.edges, rel.n)
    c4 = g.c4_pairs()
    parts = rel.sides if rel.sides is not None else g.bipartition()
    if parts is not None:
        a, b = parts
        touched = {v for e in g.edges for v in e}
        if not all(({u, v} & a) and ({u, v} & b) for u, v in g.edges):
            parts = g.bipartition()
            a, b = parts if parts is not None else (frozenset(), frozenset())
        tau: int | None = max_matching(g.adj, a) if parts is not None else None
        how = "maximum matching (Koenig)"
        side_costs = [
            (f"low-side centres ({len(a & touched)})", len(g.edges) + len(a & touched) - 1),
            (f"high-side centres ({len(b & touched)})", len(g.edges) + len(b & touched) - 1),
        ]
    elif rel.n <= BRUTE_VERTEX_CAP:
        tau, _covers = g.min_covers()
        how = "exhaustive minimum vertex cover"
        side_costs = []
    else:
        tau, how, side_costs = None, f"NOT COMPUTED (non-bipartite on {rel.n} vertices)", []
    return Counted(rel, g, c4, parts, tau, how, side_costs)


#: Either kind of decoded target. Both expose the same handful of methods, which is all the
#: verdict and the table need; only `report` looks at the pieces underneath. Declared here
#: because `Counted` is defined just above and this is a runtime alias, not an annotation.
FloorSource = Counted | TermCounted


# --------------------------------------------------------------------------------------
# the posted bound, the model, the side conditions
# --------------------------------------------------------------------------------------


def posted_bound(stmt: str) -> tuple[int, str] | None:
    """The gate budget the step posts, in whichever of four shapes it uses."""
    m = SIZE_LE_RE.search(stmt)
    if m is not None:
        return int(m.group(2)), f"{m.group(1)}.size <= {m.group(2)}"
    m = SIZE_EQ_RE.search(stmt)
    if m is not None:
        return int(m.group(2)), f"{m.group(1)}.size = {m.group(2)}"
    if "HasCircuitSize" in stmt:
        tail = HASSIZE_TAIL_RE.search(stmt)
        if tail is not None:
            return int(tail.group(1)), f"HasCircuitSize budget {tail.group(1)}"
        hits = HASSIZE_ANY_RE.findall(stmt)
        if hits:
            return int(hits[-1]), f"HasCircuitSize budget {hits[-1]} (last parenthesised argument)"
    return None


@dataclass
class CostModel:
    """What the posted number counts, and whether NOT gates are allowed.

    `kind` is `gates` (every gate counted, the usual case), `ands` (AND gates only, ORs
    free) or `unknown`. An unknown cost model gets NO floor verdict: a number compared
    against the wrong measure is worse than no number.
    """

    kind: str
    monotone: bool
    desc: str


def model_of(stmt: str) -> CostModel:
    if ANDCOUNT_RE.search(stmt) is not None:
        return CostModel("ands", True, "AND gates only, ORs free (AndCountCircuit)")
    mono = MONO_RE.search(stmt)
    if mono is not None:
        return CostModel("gates", True, f"monotone ({mono.group(0)})")
    if MONO_OPS_RE.search(stmt) is not None:
        return CostModel("gates", True, "monotone (an explicit `op = and or op = or` conjunct)")
    hit = NOT_MODEL_RE.search(stmt)
    if hit is not None:
        return CostModel("gates", False, f"AND/OR/NOT ({hit.group(0)}) - NOT gates allowed")
    return CostModel("unknown", False, "model predicate not recognised")


@dataclass
class SideConditions:
    """Conjuncts beyond the size bound and the function spec."""

    named: list[str] = field(default_factory=list)
    extra_gates: int = 0
    costed: list[str] = field(default_factory=list)

    @property
    def any(self) -> bool:
        return bool(self.named or self.costed)


def side_conditions(stmt: str, counted: Counted) -> SideConditions:
    """Name every extra demand, and cost the one shape this tool can cost.

    The costable shape is a wire forced equal to `x u || x v`. In a star-cover circuit the
    OR wires available for free are the internal nodes of some centre's tree, i.e. ORs of
    subsets of one centre's neighbourhood, plus the top ORs of whole stars. So `x u || x v`
    is free exactly when u and v have a COMMON NEIGHBOUR; with none, it is no node of any
    tree and costs at least one gate more. That is what decides L-meta-4027.
    """
    out = SideConditions()
    g = counted.graph
    for m in WIRE_OR_RE.finditer(stmt):
        u, v = int(m.group(2)), int(m.group(3))
        if u == v or u >= g.n or v >= g.n:
            continue
        common = sorted(g.adj[u] & g.adj[v])
        if common:
            out.costed.append(
                f"a wire must equal (x {u} || x {v}); vertices {u},{v} share neighbour(s) "
                f"{common}, so that OR can be an internal node of that centre's tree - no extra gate forced"
            )
        else:
            out.extra_gates = max(out.extra_gates, 1)
            out.costed.append(
                f"a wire must equal (x {u} || x {v}); vertices {u},{v} have NO common neighbour, "
                f"so that OR is no internal node of any star tree and no top-OR node -> at least 1 extra gate"
            )
    if OUTPUT_POS_RE.search(stmt) is not None:
        out.named.append("the output wire's position is constrained")
    if len(WIRE_READ_RE.findall(stmt)) > 0:
        out.named.append("a named wire other than the output is read and constrained")
    if re.search(rf"\w+\s*<\s*\w+\s*{WEDGE}", stmt) is not None:
        out.named.append("an ordered pair of wires must be re-read by a further gate")
    return out


# --------------------------------------------------------------------------------------
# report
# --------------------------------------------------------------------------------------

CAUTIONS: Final = (
    "CAUTIONS, all four of which must be read before this number is used.",
    "  1. The cover cost needs NO 2x2 BOX below the function: only then does no product of ORs",
    "     cover several terms at once. At term width 2 that is exactly C4-FREENESS (every biclique",
    "     below the function is then a star); at width >= 3 it follows from the terms pairwise",
    "     sharing at most one variable, which is also what stops two terms sharing an internal",
    "     sub-product. This tool prints both counts and withholds the floor without them.",
    "  2. This is NOT a licence to cite PEqualNP.MetaComplexity.L204, whose hypotheses are",
    "     girth >= 7 and degree->=3 vertices at least 7 apart. The floor is a number to put in a",
    "     hypothesis, not a theorem to cite.",
    "  3. The floor binds a MONOTONE model only. With a NOT gate available it is EVIDENCE, not a",
    "     bound. And star-cover optimality itself rests on the star normal form theorem, which is",
    "     our own merged reduction R_meta_5691_3 whose hypotheses are not yet proved. So every",
    "     verdict below is strong structural evidence and NEVER a proof.",
    "  4. WIDTH >= 3 IS WEAKER STILL. At width 2 the cover SHAPE has at least that normal form",
    "     argument behind it; at width 3 and up we have proved nothing about the shape at all. Its",
    "     tightness was checked only in small sub-cases by exact synthesis (3 lines pairwise meeting:",
    "     7 optimal, one gate below UNSAT; 4 lines on 6 points: 9 optimal; the 3-line pencil of",
    "     GQ(2,2): 6 optimal), and the full systems did not return. Treat a width >= 3 verdict as a",
    "     reason to look harder before dispatching, not as a reason to call a step false.",
)


@dataclass
class Verdict:
    tag: str
    detail: str
    effective: int | None
    posted: int | None


def verdict_of(
    counted: FloorSource,
    bound: tuple[int, str] | None,
    sides: SideConditions,
    model: CostModel,
    negated: str = "",
) -> Verdict:
    """Compare the posted bound with the floor.

    For a NEGATED statement ("no circuit of at most N gates computes f") the same count says
    the opposite thing, so the tags invert. N below the floor means no such circuit exists
    and the claim stands; N at or above it means the star cover IS such a circuit and refutes
    the claim outright - and we hold the witness. Reporting a negated step as BELOW FLOOR /
    do-not-dispatch would throw away exactly the steps the count WINS.
    """
    base = counted.floor_for(model.kind)
    if base is None:
        return Verdict("NO FLOOR APPLIES", counted.no_floor_reason(model.kind), None, bound[0] if bound else None)
    if bound is None:
        return Verdict("NO FLOOR APPLIES", "no posted gate bound found in the statement", base, None)
    eff = base + sides.extra_gates
    posted = bound[0]
    if negated in {"forall", "other"}:
        return Verdict(
            "NO FLOOR APPLIES",
            f"the statement negates a {negated} claim, which the floor does not translate into",
            eff,
            posted,
        )
    if negated == "lower-bound":
        #: The claim is "every circuit needs at least `posted` gates", so the comparison runs
        #: the other way: a cover BELOW the threshold is a witness against it.
        if eff >= posted:
            detail = (
                f"the cheapest cover costs {eff} >= the claimed {posted}, so the claim is plausible"
                " - a target, though the Lean proof is a lower bound and not a witness"
            )
            tag = "FLOOR SUPPORTS THE CLAIM"
        else:
            detail = (
                f"a {counted.cover_label()} of {eff} gates is BELOW the claimed minimum {posted}, so the"
                " claim is likely FALSE - and the cover is the explicit counterexample"
            )
            tag = "STAR COVER REFUTES IT"
        if not model.monotone:
            detail += " [model admits NOT, so this is evidence only]"
        detail += counted.evidence_note()
        return Verdict(tag, detail, eff, posted)
    if negated == "universal-false":
        #: `for all C, ... size <= N ... -> False`. The floor makes the size hypothesis
        #: UNSATISFIABLE when it exceeds N, which proves the claim whatever the further
        #: hypotheses are. When the cover fits the budget the hypothesis is satisfiable, and
        #: those further hypotheses - which this tool does not cost - decide the step, so no
        #: verdict is given rather than a wrong-signed one.
        if posted < eff:
            detail = (
                f"the floor is {eff} > posted {posted}, so no circuit of at most {posted} gates computes"
                " the function at all: the size hypothesis is unsatisfiable and the claim holds whatever"
                " its further hypotheses say - a target, proved by a lower bound and not by a witness"
            )
            if not model.monotone:
                detail += " [model admits NOT, so this is evidence only]"
            detail += counted.evidence_note()
            return Verdict("FLOOR SUPPORTS THE NEGATION", detail, eff, posted)
        return Verdict(
            "NO FLOOR APPLIES",
            f"the statement is an impossibility claim in universal form and a {counted.cover_label()} of"
            f" {eff} gates fits the posted {posted}, so its size hypothesis is satisfiable and the step"
            " turns on the further hypotheses this tool does not cost",
            eff,
            posted,
        )
    if negated == "exists":
        if posted < eff:
            tag = "FLOOR SUPPORTS THE NEGATION"
            detail = (
                f"the floor is {eff} > posted {posted}, so no circuit that small exists and the"
                " negation is likely TRUE - a target, though the Lean proof is a lower bound, not a witness"
            )
        else:
            tag = "STAR COVER REFUTES IT"
            detail = (
                f"a {counted.cover_label()} of {eff} gates is at most the posted {posted}, so such a circuit"
                " DOES exist and the negation is likely FALSE - and the cover is the explicit counterexample"
            )
        if not model.monotone:
            detail += " [model admits NOT, so this is evidence only]"
        detail += counted.evidence_note()
        return Verdict(tag, detail, eff, posted)
    if posted < eff:
        tag, detail = "BELOW FLOOR", f"slack {eff - posted}; do not dispatch, the statement is likely false"
    elif posted == eff:
        if sides.any and sides.extra_gates == 0:
            tag, detail = (
                "AT FLOOR (function only)",
                "the function alone is exactly constructible, but uncosted side conditions remain:"
                " not AT FLOOR overall",
            )
        else:
            tag, detail = "AT FLOOR", f"exactly constructible by a {counted.cover_label()} - the best kind of target"
    else:
        tag, detail = "ABOVE FLOOR", f"{posted - eff} gate(s) of room; genuinely open, dispatch"
    if not model.monotone:
        detail += " [model admits NOT, so this is evidence only]"
    detail += counted.evidence_note()
    return Verdict(tag, detail, eff, posted)


def analyse(gid: str) -> tuple[Verdict, FloorSource | None, SideConditions, CostModel, Meta, str] | None:
    """Decode one step and compare its posted bound with the cover floor.

    WIDTH DECIDES THE PATH, and it is read before anything else. A DNF every term of which
    is a pair is a graph and goes down the original path unchanged - that is what keeps the
    graph verdicts exactly as they were. A DNF with any wider term goes down the term-system
    path instead, because the pair decoders would otherwise read the first two reads of each
    wide term and invent a graph (see READ_RE). A statement with no DNF at all is unaffected:
    number lists, vertex-pair lists and the modular forms are still tried in order.
    """
    path = steps_dir() / f"{gid}.json"
    if not path.is_file():
        return None
    with open(path) as fh:
        rec = json.load(fh)
    info = meta_of(rec)
    gap = rec.get("gap")
    stmt = str(gap.get("statement", "")) if isinstance(gap, dict) else ""
    model = model_of(stmt)
    bound = posted_bound(stmt)
    negated = negation_shape(stmt)
    claim = minsize_claim(stmt)
    if claim is not None:
        #: A min-size statement posts its budget as a bound variable, so the claim shape -
        #: not `posted_bound` and not the blanket forall-negation guard - decides both the
        #: number and which way the comparison runs.
        negated = "" if claim[0] == "find" else "lower-bound"
        bound = (claim[1], claim[2])

    tsys = term_system(stmt)
    rel = relation(stmt) if tsys is None or tsys.width == 2 else None
    if rel is None and tsys is not None:
        tcounted = count_terms(tsys)
        sides = SideConditions()
        return verdict_of(tcounted, bound, sides, model, negated), tcounted, sides, model, info, stmt
    if rel is None:
        return (
            Verdict(
                "NO FLOOR APPLIES", "no graph relation decoded from the statement", None, bound[0] if bound else None
            ),
            None,
            SideConditions(),
            model,
            info,
            stmt,
        )
    counted = count(rel)
    sides = side_conditions(stmt, counted)
    return verdict_of(counted, bound, sides, model, negated), counted, sides, model, info, stmt


def report_terms(counted: TermCounted, verdict: Verdict, model: CostModel) -> int:
    """The body of a report for a term system of any width (the width-2 case keeps its own)."""
    sysm = counted.sys
    say(f"  RELATION: {sysm.source}")
    if sysm.absorbed:
        say(f"            {sysm.absorbed} term(s) dropped as absorbed (a term containing another)")
    shape = ", ".join(f"{c} of width {w}" for w, c in sorted(sysm.widths.items()))
    say(f"  TERMS: m = {len(sysm.terms)} ({shape}) over {len(sysm.points)} of {sysm.n} inputs")
    say(f"         largest overlap of two terms: {counted.pair_max} variable(s)")
    need = "C4-freeness" if sysm.width == 2 else "a partial linear space (overlap <= 1)"
    say(f"         2x2 boxes: {counted.boxes} (box-free: {counted.boxes == 0}); this width needs {need}")
    say(f"  COVER: k = {counted.k} by {counted.k_how}")
    base = counted.floor_for(model.kind)
    if base is not None:
        say(f"  FLOOR: {counted.formula_for(model.kind)} = {base}")
    say(f"  POSTED: {verdict.posted if verdict.posted is not None else 'nothing found'}")
    say(f"  VERDICT: {verdict.tag} - {verdict.detail}")
    say("")
    for line in CAUTIONS:
        say(line)
    return 0


def report(gid: str) -> int:
    got = analyse(gid)
    if got is None:
        say(f"{gid}: no step record under {steps_dir()}")
        return 2
    verdict, counted, sides, model, info, stmt = got
    say(f"{gid}  points {info.points}  weight {info.weight}  level {info.level}  kind {info.kind}")
    hint = "" if model.monotone else "   <- NOT gates allowed, so the floor below is EVIDENCE, not a bound"
    say(f"  MODEL: {model.desc}{hint}")
    if model.kind == "ands":
        say("         size counts AND gates only, so the floor is tau, NOT |E| + tau - 1")
    claim = minsize_claim(stmt)
    shape = "" if claim is not None else negation_shape(stmt)
    if claim is not None:
        say(f"  SHAPE: {claim[2]}")
        if claim[0] == "lower-bound":
            say("         - a lower-bound claim, so a cover BELOW the threshold refutes it")
    if shape == "exists":
        say("  SHAPE: NEGATED existential (no circuit this small computes f) - the floor's meaning INVERTS")
    elif shape == "universal-false":
        say("  SHAPE: impossibility claim in UNIVERSAL form (for all C, ... size <= N ... -> False)")
        say("         - a negated existential with no leading negation, so the floor's meaning INVERTS")
    elif shape:
        say(f"  SHAPE: negation of a {shape} claim - the floor does NOT translate into it")
    if counted is None:
        say("  RELATION: none decoded - no DNF of `x i && x j`, no two-bit number list, no modular form")
        say(f"  VERDICT: {verdict.tag} - {verdict.detail}")
        return 0
    if isinstance(counted, TermCounted):
        return report_terms(counted, verdict, model)

    g = counted.graph
    say(f"  RELATION: {counted.rel.source}")
    for note in counted.rel.excluded:
        say(f"            {note}")
    touched = sorted({v for e in g.edges for v in e})
    say(f"  GRAPH: {len(g.edges)} edges, {len(touched)} non-isolated vertices of {g.n} inputs")
    if counted.bipartite is not None:
        a, b = counted.bipartite
        da = sorted(len(g.adj[v]) for v in sorted(a) if g.adj[v])
        db = sorted(len(g.adj[v]) for v in sorted(b) if g.adj[v])
        say(f"         BIPARTITE {len(a & set(touched))} + {len(b & set(touched))}; degrees low {da} high {db}")
    else:
        say(f"         degrees {g.degrees}")
    say(f"         vertex pairs with >=2 common neighbours: {counted.c4_pairs} (C4-free: {counted.c4_pairs == 0})")
    named = g.name()
    if named:
        say(f"         THIS IS {named}")
    say(f"  COVER: tau = {counted.tau} by {counted.tau_how}")
    for label, cost in counted.side_costs:
        say(f"         {label}: |E| + centres - 1 = {cost}")
    base = counted.floor_for(model.kind)
    if base is not None:
        say(f"  FLOOR: {counted.formula_for(model.kind)} = {base}")
    if sides.any:
        say(f"  SIDE CONDITIONS: {len(sides.costed) + len(sides.named)} found")
        for line in sides.costed:
            say(f"    - {line}")
        for line in sides.named:
            say(f"    - {line} (NOT costed by this tool)")
        if sides.extra_gates:
            say(f"    => effective floor {base} + {sides.extra_gates} = {verdict.effective}")
    #: A min-size statement has no literal bound to quote, so the claim reading supplies it.
    claim_bound = minsize_claim(stmt)
    bound = (claim_bound[1], claim_bound[2]) if claim_bound is not None else posted_bound(stmt)
    say(f"  POSTED: {bound[1] if bound else 'nothing found'}")
    say(f"  VERDICT: {verdict.tag} - {verdict.detail}")
    say("")
    for line in CAUTIONS:
        say(line)
    return 0


RANK: Final = {
    "STAR COVER REFUTES IT": 0,
    "FLOOR SUPPORTS THE NEGATION": 1,
    "FLOOR SUPPORTS THE CLAIM": 1,
    "AT FLOOR": 2,
    "AT FLOOR (function only)": 3,
    "ABOVE FLOOR": 4,
    "BELOW FLOOR": 5,
}


def table(csv: bool) -> int:
    rows: list[tuple[int, str, Verdict, str, str]] = []
    for path in sorted(steps_dir().glob("*.json")):
        gid = path.stem
        got = analyse(gid)
        if got is None:
            continue
        verdict, counted, sides, model, info, _stmt = got
        pts = info.points
        notes: list[str] = []
        if counted is not None and counted.structural_note():
            notes.append(counted.structural_note())
        if sides.extra_gates:
            notes.append(f"+{sides.extra_gates} side condition")
        elif sides.any:
            notes.append("uncosted side conditions")
        if not model.monotone and verdict.tag != "NO FLOOR APPLIES":
            notes.append("NOT allowed: evidence only")
        if model.kind == "ands":
            notes.append("AND-count model: floor is tau")
        rows.append((pts, gid, verdict, "; ".join(notes), info.level))
    rows.sort(key=lambda r: (-r[0], RANK.get(r[2].tag, 9), r[1]))

    #: `margin` is posted - floor: negative is BELOW the floor, 0 is AT it, positive ABOVE.
    head = ("points", "step", "verdict", "posted", "floor", "margin", "level", "notes")
    if csv:
        say(",".join(head))
    else:
        say(f"{head[0]:>6}  {head[1]:<14} {head[2]:<24} {head[3]:>6} {head[4]:>6} {head[5]:>6}  {head[6]:<8} {head[7]}")
        say("-" * 118)
    tally: dict[str, int] = {}
    for pts, gid, verdict, note, level in rows:
        tally[verdict.tag] = tally.get(verdict.tag, 0) + 1
        posted = "" if verdict.posted is None else str(verdict.posted)
        floor = "" if verdict.effective is None else str(verdict.effective)
        margin = "" if verdict.posted is None or verdict.effective is None else str(verdict.posted - verdict.effective)
        if csv:
            say(",".join([str(pts), gid, verdict.tag, posted, floor, margin, level, note.replace(",", ";")]))
        else:
            say(f"{pts:>6}  {gid:<14} {verdict.tag:<24} {posted:>6} {floor:>6} {margin:>6}  {level:<8} {note}")
    if not csv:
        say("")
        say(f"{len(rows)} step records: " + ", ".join(f"{k} {v}" for k, v in sorted(tally.items())))
        say("")
        for line in CAUTIONS:
            say(line)
    return 0


def main(argv: list[str]) -> int:
    if not argv:
        sys.stderr.write(__doc__ or "")
        return 2
    if argv[0] == "--all":
        return table("--csv" in argv)
    return report(argv[0])


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
