#!/usr/bin/env python3
"""Decode a step's bracketed number lists as GRAPHS and independent sets.

Why this exists. A whole family of steps posts its specification as two lists of
plain natural numbers and nothing else - no title, no sketch. L-meta-7893 is the
example: fifteen numbers that must come out TRUE and fifteen that must come out
FALSE, over a ten-input `IsAO2` circuit. Read as prose that is opaque, and
`screen.py` can only shrug at it ("no edge list in title or statement").

Read as BIT SETS it is immediate. Each number is a subset of the inputs. If every
member of one list has exactly two bits, that list is an EDGE LIST, and the other
list is usually the maximal independent sets of the same graph - which means the
function being lower-bounded is the project's own

    graphFun K A x = decide (exists a in A, x a) || decide (exists u v, K.Adj u v
                                                            and x u and x v)

from Defs/NestedCoverCircuit.lean with `A` empty: "x contains an edge of K". Its
minterms ARE the edges and its maximal zeros ARE the maximal independent sets, so
the two posted lists are the canonical critical-complexity test set that pins the
function. On L-meta-7893 this turned fifteen opaque numbers into "the Petersen
graph" in one call, and then into a SIZE FLOOR, because the same file gives the
nested cover circuit's size as

    |A| + |E| + |T| - 1

with `T` a minimum vertex cover. For Petersen that is 0 + 15 + 6 - 1 = 20 against
a posted budget of 18, so the step's contradiction is a COUNT with slack 2 - the
same shape as the reduction that landed on L-meta-7698.

TWO CAVEATS, both learned the hard way today.

* The formula needs the graph C4-FREE (then every biclique is a star, so the
  cheapest cover is by stars and costs |E| + |T| - 1). This tool reports
  C4-freeness and refuses to print the floor without it.
* It does NOT licence citing `PEqualNP.MetaComplexity.L204`. That theorem wants
  girth >= 7 AND degree->=3 vertices at least 7 apart. Petersen has girth 5 with
  adjacent degree-3 vertices, so L204 does not apply even though the formula is
  right. Claiming otherwise is an overstatement this harness has already made
  once. The floor is a number to put in a hypothesis, not a theorem to cite.

Nothing here is a verdict on a step. It is a decoding, and like `screen.py` it
says what it measured, never what to do.

usage: pointsets.py <step-id>
"""

from __future__ import annotations

import itertools
import json
import pathlib
import re
import sys
from typing import Final

S: Final = pathlib.Path(__file__).absolute().parent

#: Lean's natural-number type, built with `chr` so this source file stays ASCII:
#: ruff's RUF001/RUF003 reject the character itself as confusable with a capital
#: N, and this directory takes no per-file ignore for that.
NAT: Final = chr(0x2115)
LE: Final = chr(0x2264)
WEDGE: Final = chr(0x2227)

#: A bracketed list of Lean natural literals, e.g. `[(3 : N), (6 : N)]`. The
#: statements post them with the type ascription on every element, so a plain
#: `\d+` scan over the whole statement would also pick up the arity and the size
#: bounds; requiring the brackets keeps it to real lists.
LIST_RE: Final = re.compile(rf"\[\s*\((\d+)\s*:\s*{NAT}\)(?:\s*,\s*\((\d+)\s*:\s*{NAT}\))*\s*\]")
NUM_RE: Final = re.compile(rf"\((\d+)\s*:\s*{NAT}\)")
ARITY_RE: Final = re.compile(rf"IsAO2\s*\(\s*(\d+)\s*:\s*{NAT}\)")
BUDGET_RE: Final = re.compile(
    rf"\((\d+)\s*:\s*{NAT}\)\s*{LE}\s*\w+\.size\s*{WEDGE}\s*\w+\.size\s*{LE}\s*\((\d+)\s*:\s*{NAT}\)"
)

Edge = tuple[int, int]


def say(line: str) -> None:
    """One report line. `sys.stdout.write`, not `print`: the harness bans T201."""
    sys.stdout.write(line + "\n")


def bits(n: int, width: int) -> frozenset[int]:
    return frozenset(i for i in range(width) if n >> i & 1)


def pair(c: tuple[int, ...]) -> Edge:
    return (min(c), max(c))


def arity(stmt: str) -> int:
    """The input count, from the first `IsAO2 (n : N)` in the statement."""
    m = ARITY_RE.search(stmt)
    return int(m.group(1)) if m else 0


class Graph:
    def __init__(self, edges: set[Edge], n: int) -> None:
        self.n = n
        self.edges = {(min(u, v), max(u, v)) for u, v in edges}
        self.adj: dict[int, set[int]] = {v: set() for v in range(n)}
        for u, v in self.edges:
            self.adj[u].add(v)
            self.adj[v].add(u)

    @property
    def degrees(self) -> list[int]:
        return sorted(len(self.adj[v]) for v in range(self.n))

    def triangles(self) -> int:
        return sum(
            1
            for c in itertools.combinations(range(self.n), 3)
            if all(pair(q) in self.edges for q in itertools.combinations(c, 2))
        )

    def c4_pairs(self) -> int:
        """Vertex pairs with two or more common neighbours: zero iff C4-free.

        Counting PAIRS, not cycles, on purpose. `screen.py` summed
        C(|common|, 2) over pairs and so double-counted every 4-cycle, once per
        diagonal; the only thing any caller needs is whether it is zero, and a
        pair count cannot be doubled.
        """
        return sum(1 for u, v in itertools.combinations(range(self.n), 2) if len(self.adj[u] & self.adj[v]) >= 2)

    def independent(self, s: frozenset[int]) -> bool:
        return all(pair(q) not in self.edges for q in itertools.combinations(sorted(s), 2))

    def maximal_independent(self, s: frozenset[int]) -> bool:
        return self.independent(s) and all(not self.independent(s | {v}) for v in range(self.n) if v not in s)

    def all_maximal_independent(self) -> set[frozenset[int]]:
        return {
            frozenset(c)
            for k in range(1, self.n + 1)
            for c in itertools.combinations(range(self.n), k)
            if self.maximal_independent(frozenset(c))
        }

    def min_covers(self) -> tuple[int, list[frozenset[int]]]:
        def is_cover(t: frozenset[int]) -> bool:
            return all(u in t or v in t for u, v in self.edges)

        for k in range(self.n + 1):
            found = [frozenset(c) for c in itertools.combinations(range(self.n), k) if is_cover(frozenset(c))]
            if found:
                return k, found
        return self.n, []

    def cover_is_matching(self, t: frozenset[int]) -> bool:
        """The subgraph a cover induces has max degree <= 1, so it is acyclic.

        That is the hypothesis NestedCoverCircuit's theorem 1.4 needs ("no cycle
        of K lies in a minimum cover") before the size formula describes a
        circuit that actually computes graphFun.
        """
        induced = [e for e in self.edges if e[0] in t and e[1] in t]
        return max((sum(1 for e in induced if v in e) for v in t), default=0) <= 1

    def name(self) -> str | None:
        """The graph, when the degree sequence and girth pin it to a known one."""
        d = self.degrees
        regular = bool(d) and d[0] == d[-1]
        if regular and d[0] == 3 and self.n == 10 and not self.triangles() and not self.c4_pairs():
            return "the PETERSEN graph (the unique (3,5)-cage: 3-regular, girth 5, 10 vertices)"
        if regular and d[0] == 3 and self.n == 6 and not self.triangles():
            return "K(3,3)"
        if regular and d[0] == self.n - 1:
            return f"the complete graph K{self.n}"
        return None


def report(gid: str) -> int:
    with open(S / "steps" / f"{gid}.json") as fh:
        stmt = str(json.load(fh)["gap"]["statement"])
    lists = [[int(x) for x in NUM_RE.findall(m.group(0))] for m in LIST_RE.finditer(stmt)]
    lists = [xs for xs in lists if len(xs) >= 2]
    if not lists:
        say(f"{gid}: no bracketed number lists in the statement")
        return 2

    n = arity(stmt)
    if n == 0:
        n = 1 + max(x.bit_length() for xs in lists for x in xs)
        say(f"{gid}: no IsAO2 arity found; using width {n} from the largest member")
    say(f"{gid}: {len(lists)} number list(s), {n} inputs")
    for i, xs in enumerate(lists):
        sizes = sorted({len(bits(x, n)) for x in xs})
        say(f"  list {i}: {len(xs)} members, bit-set sizes {sizes}")

    edge_lists = [xs for xs in lists if xs and all(len(bits(x, n)) == 2 for x in xs)]
    if not edge_lists:
        say("  no list is all-2-bit, so no edge list to build a graph from")
        return 2

    xs = max(edge_lists, key=len)
    g = Graph({(min(bits(x, n)), max(bits(x, n))) for x in xs}, n)
    say(f"\n  EDGE LIST: {len(g.edges)} edges on {n} vertices, degrees {g.degrees}")
    say(
        f"  triangles {g.triangles()} | vertex pairs with >=2 common nbrs {g.c4_pairs()} (C4-free: {g.c4_pairs() == 0})"
    )
    named = g.name()
    if named:
        say(f"  THIS IS {named}")

    k, covers = g.min_covers()
    allmax = g.all_maximal_independent()
    say(
        f"  minimum vertex cover |T| = {k} ({len(covers)} of them); "
        f"independence number {n - k}; {len(allmax)} maximal independent sets"
    )
    say(
        "  every minimum cover induces a matching (no cycle in a min cover): "
        f"{all(g.cover_is_matching(t) for t in covers)}"
    )

    for i, ys in enumerate(lists):
        if ys is xs:
            continue
        sets = {bits(y, n) for y in ys}
        say(
            f"  list {i} vs this graph: all independent {all(g.independent(s) for s in sets)}"
            f" | all MAXIMAL independent {all(g.maximal_independent(s) for s in sets)}"
            f" | is the COMPLETE set of maximal independent sets {sets == allmax}"
        )
        if sets == allmax:
            say(
                "    -> so this list is the function's MAXIMAL ZEROS and the edge list its"
                "\n       MINTERMS: the target is `graphFun K` with an empty vertex set"
                "\n       (Defs/NestedCoverCircuit.lean) on that graph."
            )

    if g.c4_pairs():
        say("\n  graph is NOT C4-free, so the |E| + |T| - 1 star-cover floor does not apply")
        return 0

    floor = len(g.edges) + k - 1
    say(f"\n  NESTED-COVER SIZE |A| + |E| + |T| - 1 = 0 + {len(g.edges)} + {k} - 1 = {floor}")
    say(
        "  The graph is C4-free, so every biclique is a star and that is the star-cover cost."
        "\n  State it as a HYPOTHESIS. It is NOT PEqualNP.MetaComplexity.L204, whose girth >= 7"
        "\n  and hub-separation hypotheses this graph fails."
    )
    budget = BUDGET_RE.search(stmt)
    if budget:
        lo, hi = int(budget.group(1)), int(budget.group(2))
        verdict = (
            f"budget is BELOW the floor, slack {floor - hi} - the contradiction is a count"
            if hi < floor
            else "budget REACHES the floor, so the count alone cannot close it"
        )
        say(f"  POSTED BUDGET {lo} <= size <= {hi} against floor {floor}: {verdict}")
    return 0


def main(argv: list[str]) -> int:
    if not argv:
        sys.stderr.write(__doc__ or "")
        return 2
    return report(argv[0])


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
