#!/usr/bin/env python3
"""Emit the Lean file for EVERY promise row the counting screen refutes.

The upstream pull request carries three disproofs because three were all we had
when it was opened. Nine rows of this family have now been refuted by the same
lemma, and each is six lines of Lean with the path witness supplied by
promise.py. Hand-typing six more proof terms, each with four `by decide` goals
and two `Exists.intro` indices, is exactly the kind of transcription where a
wrong index produces a file that fails to compile - or worse, one that compiles
while proving something about the wrong mask. So the file is generated from the
same code that computes the verdict.

The budget and shape are read from the step's own statement, never typed: that
mistake was made once already, reading budgets off row titles (20464 and 20940
are posted at 5 and 8, while their titles suggest 6 and 7).
"""

from __future__ import annotations

import json
import pathlib
import re
import sys
from typing import Final, NamedTuple

HARNESS: Final = pathlib.Path("/home/user/pequalnp-proofs/tools/pnp-harness")
sys.path.insert(0, str(HARNESS))

import promise as P  # noqa: E402


class Row(NamedTuple):
    step: str
    points: int
    mask: int
    n: int
    m: int
    budget: int
    bound: int
    wit: tuple[int, int, int, int]
    false_col: int
    false_row: int


def rows() -> list[Row]:
    out: list[Row] = []
    for p in sorted((HARNESS / "steps").glob("L-*.json")):
        try:
            rec = json.load(open(p))
        except (OSError, json.JSONDecodeError):
            continue
        gap = rec.get("gap") or {}
        stmt = str(gap.get("statement", ""))
        hit = P.ROW_RE.search(stmt)
        if not hit:
            continue
        _, n_s, _, m_s, mask_s, budget_s = hit.groups()
        if not (n_s and m_s):
            continue
        mask, n, m, budget = int(mask_s), int(n_s), int(m_s), int(budget_s)
        bound, _lhs, _rhs, wit = P.bound(mask, n, m)
        if wit is None or budget >= bound:
            continue  # not refuted by counting, or needs the weaker lemma
        a = P.matrix(mask, n, m)
        u, x, v, w = wit
        # The two side conditions of RepPath.path, as explicit indices.
        fc = next(q for q in range(m) if not a[u][q])
        fr = next(q for q in range(n) if not a[q][v])
        terms = (rec.get("lease") or {}).get("terms") or {}
        out.append(
            Row(
                str(gap.get("id")),
                int(terms.get("points") or 0),
                mask,
                n,
                m,
                budget,
                bound,
                wit,
                fc,
                fr,
            )
        )
    out.sort(key=lambda r: -r.points)
    return out


def picture(r: Row) -> str:
    a = P.matrix(r.mask, r.n, r.m)
    return ", ".join(
        "`" + "".join("1" if a[u][v] else "." for v in range(r.m)) + "`" for u in range(r.n)
    )


def emit(rs: list[Row]) -> str:
    head = [
        "| row | shape | mask | posted budget | forced reads | true floor |",
        "|---|---|---|---|---|---|",
    ]
    for r in rs:
        lhs = len(P.forced_left(P.matrix(r.mask, r.n, r.m), r.n, r.m))
        rhs = len(P.forced_right(P.matrix(r.mask, r.n, r.m), r.n, r.m))
        head.append(
            f"| {r.step} | {r.n} x {r.m} | {r.mask} | {r.budget} | {lhs} + {rhs} | {r.bound} |"
        )
    body: list[str] = []
    for i, r in enumerate(rs):
        nm = f"A{r.mask}_{r.n}x{r.m}"
        u, x, v, w = r.wit
        body.append(
            f"/-- The {r.n} by {r.m} mask of {r.step}: rows {picture(r)}. -/\n"
            f"def {nm} : Fin {r.n} → Fin {r.m} → Bool :=\n"
            f"  fun u v => ({r.mask} : ℕ).testBit ({r.m} * u.val + v.val)\n"
        )
        body.append(
            f"/-- {r.step} posted {r.budget}; the forced reads total {r.bound}. -/\n"
            f"theorem {nm}_not_{r.budget} : ¬ RepSizeAtMost {nm} {r.budget} := by\n"
            "  intro h\n"
            "  have key :=\n"
            f"    PEqualNP.MetaComplexity.RepPath.path {r.n} {r.m} {r.budget} {nm} {u} {x} {v} {w}\n"
            "      (by decide) (by decide) (by decide) (by decide)\n"
            f"      (Exists.intro {r.false_col} (by decide)) (Exists.intro {r.false_row} (by decide)) h\n"
            "  revert key\n"
            "  decide\n"
        )
        if i != len(rs) - 1:
            body.append("")
    return "\n".join(head) + "\n@@BODY@@\n" + "\n".join(body)


def main() -> int:
    rs = rows()
    sys.stdout.write(f"{len(rs)} refuted rows, {sum(r.points for r in rs)} points\n")
    for r in rs:
        sys.stdout.write(
            f"  {r.step:16} {r.points:>4}pt  mask {r.mask:<8} {r.n}x{r.m}"
            f"  posted {r.budget}  floor {r.bound}  wit {r.wit}\n"
        )
    table, body = emit(rs).split("@@BODY@@")
    doc = f"""import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.RepPath

/-!
# {len(rs)} posted promise rows are false, and the template that makes them is one unit short

This file proves {len(rs)} posted statements false, by citing a lemma this repository
already carries. It is offered unsolicited, with no gap id, because these rows
are posted in one direction only and so there is no row to attach a negation to.
The reason for sending it anyway is the last section: the template generating
this family computes its floor with a lemma weaker than the one beside it, so it
keeps posting rows one unit below the true floor and calling them searches.

## The lemma that decides them

`PEqualNP.MetaComplexity.RepPath.path` gives, for `RepSizeAtMost A s`,

  (forcedL A).card + (forcedR A).card <= s

where `forcedL A` is the left vertices with a true entry in some column that is
false elsewhere, and `forcedR A` the right vertices symmetrically
(`RepReads.forcedL` / `forcedR`). It needs a path witness: rows `u`, `x` and
columns `v`, `w` with `A u v`, `A u w`, `A x v` true and `A x w` false, plus one
false entry in row `u` and one in column `v`. On every mask below such a witness
exists, and it is exhibited in the proof term.

## The rows

{table.strip()}

Each sketch described a search in progress. For `L-meta-20460` it reported
holding a circuit of 7 AND/OR gates, holding none of 6, and called the row a
search. No search is needed: six gates are impossible.

## Where the template loses the unit

The sketch for `L-meta-20531` states its own floor:

  Our count of unread rows and columns gives a floor of 6 (on paper), a gap of 1.

That is the same count used here, one unit weaker. It is `RepReads.reads_le`,
which holds unconditionally and gives `card sum <= s + 1`. `RepPath.path` gives
`card sum <= s` whenever a path witness exists, and on these masks one always
does. So each row is posted one below its own floor, the gap is believed to be
one, and the family is generated as searches that cannot succeed.

These {len(rs)} were drawn and screened in a single session; every one whose budget fell
below the sharp floor was false. Using `path` rather than `reads_le` when the
witness exists would stop the family being generated this way.

The bound is a LOWER bound, so it only ever refutes - it cannot confirm a row -
and it is weaker than exhaustion: on the 4 by 4 mask 854, whose optimum is
exactly 7 by two independent encoders, this count yields only 6. Its value is
that it is free and that the kernel checks it.

Every declaration below is generated from the same code that computes the
verdict, so the witness indices are not transcribed by hand.
-/

namespace PEqualNP.Outside.PromiseFloor

open PEqualNP.Represents

{body.strip()}

end PEqualNP.Outside.PromiseFloor
"""
    out = pathlib.Path("/home/user/pequalnp-proofs/lean/PEqualNP/Outside/L_promise_floor.lean")
    out.write_text(doc)
    bad = doc.count(chr(34))
    sys.stdout.write(f"\nwrote {out}\n  double quotes: {bad} (must be 0)\n")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
