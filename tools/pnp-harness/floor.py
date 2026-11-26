#!/usr/bin/env python3
"""Screen a FIND step against the STAR-COVER SIZE FLOOR before dispatching an agent.

Why this exists. A FIND step asks for a small monotone circuit for a given function. When
that function is the edge (or point-line incidence) function of a graph G, and G is C4-FREE,
every biclique below the function is a star, so the cheapest circuit is a star cover, and a
cover by centres T costs

    one AND per centre          |T|
  + (deg t - 1) internal ORs    |E| - |T|
  + (|T| - 1) top ORs           |T| - 1
  ------------------------------------------
                                |E| + |T| - 1

Minimising over covers puts the cheapest star cover at |E| + tau - 1, with tau the minimum
vertex cover (for bipartite G, Koenig makes tau the maximum matching). A step whose posted
gate bound is BELOW that number is almost certainly FALSE and must not be dispatched; a step
AT it is constructible and is the best kind of target; a step ABOVE it is genuinely open.

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


def negation_shape(stmt: str) -> str:
    """ "", `exists`, `forall` or `other`: what, if anything, the statement negates.

    Decided by which marker comes FIRST after the leading `not (`, so a `have ...;` preamble
    and any nesting further in are both harmless.
    """
    if NEG_RE.search(stmt) is None:
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
    return graph_relation(stmt) or pair_list_relation(stmt) or modular_relation(stmt)


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
    "CAUTIONS, all three of which must be read before this number is used.",
    "  1. The star-cover cost needs the graph C4-FREE: only then is every biclique below the",
    "     function a star. This tool prints the C4 pair count and withholds the floor without it.",
    "  2. This is NOT a licence to cite PEqualNP.MetaComplexity.L204, whose hypotheses are",
    "     girth >= 7 and degree->=3 vertices at least 7 apart. The floor is a number to put in a",
    "     hypothesis, not a theorem to cite.",
    "  3. The floor binds a MONOTONE model only. With a NOT gate available it is EVIDENCE, not a",
    "     bound. And star-cover optimality itself rests on the star normal form theorem, which is",
    "     our own merged reduction R_meta_5691_3 whose hypotheses are not yet proved. So every",
    "     verdict below is strong structural evidence and NEVER a proof.",
)


@dataclass
class Verdict:
    tag: str
    detail: str
    effective: int | None
    posted: int | None


def verdict_of(
    counted: Counted,
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
        if model.kind == "unknown":
            why = "the cost model is not recognised, so the posted number may not count gates at all"
        elif counted.c4_pairs:
            why = "graph is not C4-free"
        else:
            why = f"tau {counted.tau_how}"
        return Verdict("NO FLOOR APPLIES", why, None, bound[0] if bound else None)
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
                f"a star cover of {eff} gates is at most the posted {posted}, so such a circuit DOES"
                " exist and the negation is likely FALSE - and the cover is the explicit counterexample"
            )
        if not model.monotone:
            detail += " [model admits NOT, so this is evidence only]"
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
            tag, detail = "AT FLOOR", "exactly constructible by a star cover - the best kind of target"
    else:
        tag, detail = "ABOVE FLOOR", f"{posted - eff} gate(s) of room; genuinely open, dispatch"
    if not model.monotone:
        detail += " [model admits NOT, so this is evidence only]"
    return Verdict(tag, detail, eff, posted)


def analyse(gid: str) -> tuple[Verdict, Counted | None, SideConditions, CostModel, Meta, str] | None:
    path = steps_dir() / f"{gid}.json"
    if not path.is_file():
        return None
    with open(path) as fh:
        rec = json.load(fh)
    info = meta_of(rec)
    gap = rec.get("gap")
    stmt = str(gap.get("statement", "")) if isinstance(gap, dict) else ""
    rel = relation(stmt)
    model = model_of(stmt)
    bound = posted_bound(stmt)
    negated = negation_shape(stmt)
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
    shape = negation_shape(stmt)
    if shape == "exists":
        say("  SHAPE: NEGATED existential (no circuit this small computes f) - the floor's meaning INVERTS")
    elif shape:
        say(f"  SHAPE: negation of a {shape} claim - the floor does NOT translate into it")
    if counted is None:
        say("  RELATION: none decoded - no DNF of `x i && x j`, no two-bit number list, no modular form")
        say(f"  VERDICT: {verdict.tag} - {verdict.detail}")
        return 0

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
    bound = posted_bound(stmt)
    say(f"  POSTED: {bound[1] if bound else 'nothing found'}")
    say(f"  VERDICT: {verdict.tag} - {verdict.detail}")
    say("")
    for line in CAUTIONS:
        say(line)
    return 0


RANK: Final = {
    "STAR COVER REFUTES IT": 0,
    "FLOOR SUPPORTS THE NEGATION": 1,
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
        if counted is not None and counted.c4_pairs:
            notes.append(f"not C4-free ({counted.c4_pairs} pairs)")
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
