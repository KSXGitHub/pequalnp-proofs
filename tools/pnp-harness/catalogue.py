#!/usr/bin/env python3
"""Rank every step statement we have ever been handed against what we can PROVE.

Why this exists. The desk hands out statements one lease at a time and we had
been judging each on arrival, which meant the only steps we ever compared were
the two or three in hand. steps/ now holds 164 of them - the whole session's
draws, recovered when the two state directories were merged - and `--proof-of`
claims a step even while another agent holds it. So the catalogue is a list of
CLAIMABLE work, and the question worth asking is not "is this draw good?" but
"which of the 164 does today's machinery already fit?".

It ranks by MARKER OVERLAP with assets we have in hand, not by points, because
a 1747-point step gated on an open research lemma is worth less than a 200-point
step whose vocabulary we have already formalised.

The markers are deliberately shallow - substring hits on the Lean text. This is
a SHORTLIST, never a verdict: every sign error this session came from trusting a
mechanical read of a statement instead of reading it, so the output is ordered
reading material and the last column is always `read it yourself`.
"""

from __future__ import annotations

import json
import pathlib
import sys
from typing import Final

S: Final = pathlib.Path(__file__).absolute().parent

#: What we can prove right now, each with the statement vocabulary it touches.
#: Sources: L_meta_zzrepair.lean (patchOne, edge_has_clean_and, clean_and_star,
#: repairMany_of_normalForm - all CHECK_OK, self-contained, import PEqualNP.Defs
#: only, zero double quotes so they paste into a submission as they stand) and
#: L_meta_zzchain.lean (repairMany implies the universal cover bound).
ASSETS: Final[dict[str, tuple[str, ...]]] = {
    "one-slot surgery (patchOne, STRONGER than the merged L_meta_8305.reduce)": (
        "replaceByConst",
        "eraseRedirect",
        "patch",
    ),
    "star profile of a clean AND under C4-freeness (clean_and_star/cross)": (
        "NoFourCycle",
        "starEdges",
        "cleanOn",
    ),
    "every edge is true at some clean AND (edge_has_clean_and)": (
        "IsDirtyAnd",
        "junk",
        "BelowF",
    ),
    "cover counting (|E| + tau - 1), given cleanliness": (
        "IsVertexCover",
        "edgeFinset",
        "Ustar",
        "centreless",
    ),
    "verified 58-line Res(xor) PHP(4,3) refutation + emitter": (
        "ProofComplexity",
        "ResXor",
        "weaken",
        "PHP",
    ),
    "ReplayCol witness replay (3-line FIND proofs)": (
        "HasCircuitSize",
        "circuitFun",
    ),
}

#: Shapes that have cost us time and should be visible at a glance.
FLAGS: Final[dict[str, str]] = {
    "Represents": "PARTIAL ROW SPEC - the cover floor does not apply at all",
    "RepSizeAtMost": "PARTIAL ROW SPEC - the cover floor does not apply at all",
    "oneEach": "PARTIAL ROW SPEC - the cover floor does not apply at all",
    "IsLeastAO": "minimality hypothesis - TopForm family, counting not surgery",
    "TopForm": "minimality hypothesis - TopForm family, counting not surgery",
}


def rows() -> list[dict[str, object]]:
    out: list[dict[str, object]] = []
    for p in sorted((S / "steps").glob("*.json")):
        try:
            rec = json.load(open(p))
        except (OSError, json.JSONDecodeError):
            continue
        gap = rec.get("gap")
        if not isinstance(gap, dict):
            continue
        #: POINTS LIVE IN `lease.terms.points`, NOT IN `gap`. This tool sorted by
        #: `gap.weight` for its whole first day, and weight is a DIFFERENT quantity:
        #: L-meta-9747 is weight 55 and 1498 POINTS, so it looked like one of the
        #: cheapest rows we held when it was the most valuable by a wide margin.
        #: Every ranking produced before this was mis-calibrated. `lease.terms`
        #: also carries the authoritative `reductions_open` and `kind`/`level` as
        #: issued, which beat the `gap` copies when they disagree.
        lease = rec.get("lease")
        terms = lease.get("terms") if isinstance(lease, dict) else None
        terms = terms if isinstance(terms, dict) else {}
        pts = terms.get("points")
        red_open = terms.get("reductions_open")
        stmt = str(gap.get("statement", ""))
        title = str(gap.get("title", ""))
        hits: list[str] = []
        for asset, marks in ASSETS.items():
            n = sum(1 for m in marks if m in stmt)
            if n:
                hits.append(f"{n}x {asset}")
        out.append(
            {
                "id": str(gap.get("id", p.stem)),
                "points": pts if isinstance(pts, int) else 0,
                "weight": gap.get("weight") if isinstance(gap.get("weight"), int) else 0,
                "level": str(terms.get("level") or gap.get("level") or "?"),
                "kind": str(terms.get("kind") or gap.get("kind") or "?"),
                "reductions": bool(red_open) if red_open is not None else bool(gap.get("reductions")),
                "live": gap.get("reductions_live"),
                "cut": title.strip().lower().startswith("a step toward"),
                "title": title,
                "hits": hits,
                "flags": sorted({v for k, v in FLAGS.items() if k in stmt}),
                "bytes": len(stmt),
            }
        )
    return out


def main(argv: list[str]) -> int:
    data = rows()
    want_open = "--reductions-open" in argv
    if want_open:
        data = [r for r in data if r["reductions"] and r["live"] != 3]
    data.sort(key=lambda r: (-int(r["points"] or 0), -len(r["hits"]), str(r["id"])))
    sys.stdout.write(f"{len(data)} steps on file; ordered by POINTS, then by how much of our machinery fits\n\n")
    for r in data[:40]:
        slots = "OPEN" if (r["reductions"] and r["live"] != 3) else ("full" if r["reductions"] else "no")
        sys.stdout.write(
            f"{r['id']:16} {r['points'] or 0:>6}pt {r['level']:<7} {r['kind']:<7}"
            f" red:{slots:<4} {'CUT' if r['cut'] else '   '}  {r['title'][:84]}\n"
        )
        for h in r["hits"]:
            sys.stdout.write(f"{'':18}+ {h}\n")
        for f in r["flags"]:
            sys.stdout.write(f"{'':18}! {f}\n")
    sys.stdout.write("\nSHORTLIST ONLY. Read each statement before judging it - every sign error\n")
    sys.stdout.write("this session came from trusting a mechanical read instead of the text.\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
