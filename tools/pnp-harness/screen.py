#!/usr/bin/env python3
"""Screen an edge-function gate-count step BEFORE spending an agent on it.

Steps of the form "<graph>: its edge function needs at least N AND/OR/NOT gates
of fan-in at most two" and their "False:" twins keep arriving. The twin asks for
a circuit of N-1 gates, which looks like a cheap witness hunt - and is not. Two
agents spent about an hour each on L-meta-10413 and L-meta-10679 before the
first of them produced the argument that settles BOTH in a second of arithmetic.

THE ARGUMENT, for a MONOTONE fan-in-two circuit computing the edge function of a
graph with m edges:

  * Each AND gate covers Supp1(L) x Supp1(R), which must be a biclique inside E.
    If the graph is C4-FREE, every biclique has a side of size one, so every AND
    covers a STAR; the number of ANDs is then at least the biclique cover number,
    which for a C4-free graph is the MINIMUM VERTEX COVER k.
  * Every gate in the output's OR-cone has Supp1 empty (it is <= f), while every
    leaf-OR feeding an AND has Supp1 non-empty. So no gate is shared between the
    top OR tree and the leaf ORs. Two leaf-ORs can share a wire of |Supp1| >= 2
    only through a C4, which by assumption does not exist. Hence
    #OR >= (m - t) + (t - 1) = m - 1, independent of how the stars are chosen.
  * Total >= k + m - 1.

So on a C4-free graph the floor is m + k - 1, which is exactly the cost of the
star cover - the cover is optimal, and nothing monotone beats it. A "False:" twin
asking for m + k - 2 can then only be true if a NOT gate beats the monotone
floor. Measured on both graphs above: every negation pattern tried cost MORE.

TWO GAPS IN THAT ARGUMENT, both found by the L-meta-10679 agent after this tool
was already committed. Neither is a reason to stop using it; both are reasons not
to call its verdict a proof.

  1. THE ARGUMENT ASSUMES EVERY AND GATE IS <= f. That is what makes
     Supp1(L) x Supp1(R) a biclique inside E. A general monotone circuit may put
     an AND gate ABOVE f: f factors CNF-style as g AND h with g, h >= f, and then
     the product need not lie in E at all. So the floor is airtight for an
     OR-of-stars circuit and NOT for every monotone circuit. On the 10679 graph
     that route was inspected - f is the AND over maximal independent sets I of
     the OR of the vertices outside I, and three of those clauses alone already
     cost 11 gates even sharing a prefix - so it is strictly worse there. By
     inspection, not by proof.
  2. IT SAYS NOTHING ABOUT NOT GATES, which is what these steps actually allow.

What stands in for a proof on point 2 is a calibrated experiment, also from that
agent: on every small C4-free graph where complete exact synthesis over the full
AND/OR/NOT basis is decidable, the full basis needs exactly m + k - 1 - eight
cases for eight (K_1,3; P_4; K_3; P_5; C_5; C_6; triangle with a pendant at each
corner; triangle with two pendants on one corner). NOT bought nothing in any of
them. The last two are the closest analogues of the 9-vertex graphs this family
keeps posting, which are a single triangle with trees hanging off it.
Runtimes from the same experiment calibrate why the big instances never return:
C_6 at 7 gates over 6 inputs took 60 s and C_7 at 9 gates over 7 inputs did not
finish in 480 s, so 14 gates over 9 inputs is orders of magnitude out of reach.
A 14-gate run that does not return is therefore EXPECTED and must never be read
as UNSAT.

So: this tool tells you a step is very probably false and that a witness hunt is
not worth an agent, which is the decision actually being made. It does not settle
the step. Where the graph HAS a four-cycle the argument says nothing: a 2x2
biclique covers four edges for three gates and a shared leaf-OR can beat a
disjoint cover, so those are the steps worth searching. Conversely, when every
biclique is a star - checkable directly, and all 68 of 10679's were - the shared
leaf-OR route is structurally unavailable.

usage: screen.py <step-id>            read the edge list from the saved lease answer
       screen.py --edges "0-4 1-5"    screen an edge list directly
"""

from __future__ import annotations

import itertools
import json
import pathlib
import re
import sys
from typing import Final

S: Final = pathlib.Path(__file__).absolute().parent


def parse_edges(text: str) -> list[tuple[int, int]]:
    """Pull "0-4 1-5 0-6" out of a title or an explicit list."""
    out: list[tuple[int, int]] = []
    for a, b in re.findall(r"(\d+)-(\d+)", text):
        e = (int(a), int(b))
        if e[0] != e[1] and e not in out and (e[1], e[0]) not in out:
            out.append(e)
    return out


def four_cycles(n: int, edges: list[tuple[int, int]]) -> int:
    adj: dict[int, set[int]] = {v: set() for v in range(n)}
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    total = 0
    for u, v in itertools.combinations(range(n), 2):
        c = len(adj[u] & adj[v])
        if c >= 2:
            total += c * (c - 1) // 2
    return total


def min_vertex_cover(n: int, edges: list[tuple[int, int]]) -> list[int]:
    for r in range(n + 1):
        for cand in itertools.combinations(range(n), r):
            s = set(cand)
            if all(a in s or b in s for a, b in edges):
                return list(cand)
    return list(range(n))


def budget_from_title(title: str) -> tuple[int, str] | None:
    """The gate count and WHICH CLAIM it belongs to.

    "needs at LEAST N gates" is a lower bound; its negated twin asks for N - 1.
    "with at MOST N gates computes ..." is an EXISTENCE claim in its own right,
    and then N is the budget itself, not N - 1. Conflating the two was a second
    bug: L-meta-9751 is an at-most row, and reading it as an at-least row put the
    budget one gate off and named the wrong artifact.
    """
    m = re.search(r"at\s+(least|most)\s+(\d+)\s+(?:AND|gates)", title, re.IGNORECASE)
    if m is None:
        return None
    return int(m.group(2)), m.group(1).lower()


def edges_from_statement(statement: str) -> list[tuple[int, int]]:
    """Read the edge list out of `(x i && x j) || ...`.

    Some titles say only "the listed graph", with the edges in the statement.
    """
    out: list[tuple[int, int]] = []
    for a, b in re.findall(r"x\s+(\d+)\s*&&\s*x\s+(\d+)", statement):
        e = (int(a), int(b))
        if e[0] != e[1] and e not in out and (e[1], e[0]) not in out:
            out.append(e)
    return out


def report(title: str, edges: list[tuple[int, int]], claim: tuple[int, str] | None) -> int:
    n = 1 + max(max(a, b) for a, b in edges)
    m = len(edges)
    c4 = four_cycles(n, edges)
    cover = min_vertex_cover(n, edges)
    k = len(cover)
    floor = m + k - 1

    sys.stdout.write(f"{title}\n")
    sys.stdout.write(f"  vertices {n}, edges {m}, four-cycles {c4}\n")
    sys.stdout.write(f"  minimum vertex cover {k} {sorted(cover)}\n")
    if c4 == 0:
        sys.stdout.write(f"  C4-FREE, so every biclique is a star and the monotone floor is m + k - 1 = {floor}\n")
    else:
        sys.stdout.write(
            f"  has {c4} four-cycle(s): a 2x2 biclique covers four edges for three gates, so the\n"
            f"  m + k - 1 = {floor} count is only an UPPER bound and a search is worth running\n"
        )
    if claim is None:
        sys.stdout.write("  no gate count found in the title; pass the budget yourself\n")
        return 0
    budget, kind = claim

    # WHICH CLAIM DO WE HOLD? Got this wrong twice, so it is spelled out.
    # 1. A negated twin says so in the title, and asks for budget - 1.
    # 2. An "at MOST N gates computes" row is an EXISTENCE claim: budget N, and
    #    if the cover already fits, writing the cover down IS the proof.
    # 3. An "at LEAST N gates" row is a lower bound and is not an artifact.
    low = title.lower()
    twin = "false:" in low or "it is false that" in low

    if not twin and kind == "most":
        sys.stdout.write(
            f"  WE HOLD AN EXISTENCE CLAIM: some circuit of <= {budget} gates computes it, so a\n"
            "  single exhibited circuit IS the proof\n"
        )
        if c4 == 0 and floor <= budget:
            sys.stdout.write(
                f"  VERDICT: WINNABLE WITHOUT A SEARCH. The star cover costs m + k - 1 = {floor},\n"
                f"  which already fits in {budget}. Build that circuit, verify it on every input,\n"
                "  and write the Lean file - p10413/mklean.py turns a verified circuit JSON into\n"
                "  the finished proof. Do this NOW; it is contested.\n"
            )
            return 0
        if c4 == 0:
            sys.stdout.write(
                f"  VERDICT: no monotone circuit of {budget} gates exists, since the floor is\n"
                f"  {floor}. The claim can only hold if a NOT gate beats the monotone floor, which\n"
                "  has not happened on any graph measured here. Probably FALSE: release\n"
                "  statement_seems_false rather than spending an agent.\n"
            )
            return 1
        sys.stdout.write(
            f"  VERDICT: a four-cycle is present so the floor does not bind - the cover bound\n"
            f"  {floor} is only an upper bound. A witness hunt is worth running.\n"
        )
        return 0

    if twin:
        want = budget - 1
        sys.stdout.write(
            f"  WE HOLD THE NEGATED TWIN: it asks us to EXHIBIT a circuit of <= {want} gates\n"
            f"  (the positive row claims at least {budget})\n"
        )
        if c4 == 0 and want < floor:
            sys.stdout.write(
                f"  VERDICT: no monotone circuit of {want} gates exists, since the floor is {floor}.\n"
                "  The step can only hold if a NOT gate beats the monotone floor, which has not\n"
                "  happened on any graph measured here. DO NOT spend an agent on a witness hunt;\n"
                "  release statement_seems_false.\n"
            )
            return 1
        sys.stdout.write("  VERDICT: the floor does not rule it out - a witness hunt is worth running.\n")
        return 0

    sys.stdout.write(
        f"  WE HOLD THE POSITIVE ROW: it claims at least {budget} gates are needed, which is a\n"
        "  LOWER BOUND over every circuit, NOT a witness we can exhibit\n"
    )
    if c4 == 0 and floor < budget:
        sys.stdout.write(
            f"  VERDICT: a monotone circuit of {floor} gates exists (the star cover), which is\n"
            f"  BELOW the claimed {budget}, so the claim is FALSE. Release statement_seems_false,\n"
            "  and keep the cover circuit: the negated twin is provable by exhibiting it.\n"
        )
        return 1
    sys.stdout.write(
        f"  VERDICT: the monotone floor is {floor}, so the claim is consistent and probably TRUE -\n"
        "  but proving it needs a lower bound over all circuits, NOT gates included, which is a\n"
        "  formalized counting argument rather than an artifact. Not winnable here: release\n"
        "  missing_lemma. Do not spend an agent on it.\n"
    )
    return 2


def main(argv: list[str]) -> int:
    if not argv:
        sys.stderr.write(__doc__ or "")
        return 2
    if argv[0] == "--edges":
        return report("(explicit edge list)", parse_edges(argv[1]), None)
    p = S / "steps" / f"{argv[0]}.json"
    if not p.exists():
        sys.stdout.write(f"{argv[0]}: no saved lease answer at {p}\n")
        return 2
    gap = json.load(open(p))["gap"]
    title = str(gap.get("title") or "")
    edges = parse_edges(title)
    if not edges:
        # A title saying "the listed graph" keeps its edges in the statement.
        edges = edges_from_statement(str(gap.get("statement") or ""))
        if edges:
            sys.stdout.write("  (edge list read from the statement, not the title)\n")
    if not edges:
        sys.stdout.write(f"{argv[0]}: no edge list in title or statement\n  {title}\n")
        return 2
    return report(f"{argv[0]}: {title}", edges, budget_from_title(title))


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
