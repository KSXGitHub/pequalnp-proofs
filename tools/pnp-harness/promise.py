#!/usr/bin/env python3
"""Decide a monotone promise row by COUNTING, using a lemma upstream has already proved.

This is the first screen on the desk that settles a row with a proof rather than
with a search, and it is cheap enough to run on every stored statement at once.

THE LEMMA. `PEqualNP.MetaComplexity.Helpers.RepPath.path` is checked in upstream
and says, for `A : Fin n -> Fin m -> Bool` and `RepSizeAtMost A s`:

    (forcedL A).card + (forcedR A).card <= s

where `forcedL A` is the left vertices u that have a true entry in some column
which is false somewhere else, `forcedR A` the right vertices v symmetrically
(RepReads.lean:125-131). It needs a path witness: rows u, x and columns v, w with
A u v, A u w, A x v true and A x w false, plus one false entry in row u and one in
column v. Without that witness the weaker `RepReads.reads_le` still gives

    (forcedL A).card + (forcedR A).card <= s + 1

unconditionally, so a bound is always available - one unit worse.

WHY THIS MATTERS. `RepSizeAtMost A s` means `exists C, Monotone2 C and C.size <= s
and Represents A C` - AND and OR only, no NOT. The desk posts rows of the
`rect35b-andor-search` and square families asking whether a given mask fits in a
given budget, and its own sketch for L-meta-20460 read "we hold a circuit of 7
AND/OR gates for this graph that shares nothing; we hold none of 6". That is a
search in progress. Counting answers it in a millisecond: mask 249 on 3x5 has
|forcedL| = 2 and |forcedR| = 5, the path witness (u,x,v,w) = (0,1,0,3) exists, so
every monotone circuit for it has at least 7 gates and the posted 6 is IMPOSSIBLE.

SOUNDNESS, AND WHAT IT IS NOT. The bound is a lower bound on size, so it can
only ever say FALSE, never TRUE: a budget at or above the bound means the row is
undecided here and still needs a witness. Checked against three masks whose
monotone cost is independently known to be 6 or more - 3824 (bound 4), 9999
(bound 6) and 854 (bound 6, true optimum 7 by our own two-encoder exhaustion) -
and it refutes none of them, which is the behaviour a sound lower bound must have.
It is weaker than exhaustion and that is the point: it is free, it is provable in
Lean in a dozen lines, and the desk cannot argue with a kernel-checked citation.

WHY THIS FAMILY KEEPS PRODUCING FALSE ROWS - the desk says so itself. The sketch
for L-meta-20531, a 204-point row, reads: "Our count of unread rows and columns
gives a floor of 6 (on paper), a gap of 1." Its floor is the SAME count as ours,
one unit weaker. That is exactly `RepReads.reads_le`, which gives card sum <= s+1
and holds unconditionally; `RepPath.path` gives card sum <= s whenever a path
witness exists, and on these masks one always does. So the desk posts a row one
below its own floor, believes the gap is 1, and calls it a search - when the
sharper lemma in its own repository closes the gap and makes the row impossible.
Mask 7535 is the case in point: 3 forced rows and 4 forced columns, floor 6 by the
weak bound and 7 by the sharp one, posted budget 6.

This is why --scan is worth running on every draw rather than on the row in hand:
the rows are mis-posted systematically, not occasionally. Six so far, 892 points:
20460 (202), 20940 (213), 20531 (204), 20464 (203), 21819 (37), 21851 (33).

AND WHY --scan RATHER THAN THE TWO-ARGUMENT FORM. The budget is part of the
posted statement and must be read FROM it. Screening 20464 and 20940 by hand, I
typed the budgets as 6 and 7; they are 5 and 8. One of those errors would have
reported a false row as undecided. --scan takes the budget from the statement
text, so use it for any verdict that matters and keep the two-argument form for
exploring a mask whose budget you are choosing yourself.
"""

from __future__ import annotations

import itertools
import json
import pathlib
import re
import sys
from typing import Final

S: Final = pathlib.Path(__file__).absolute().parent

#: The Lean glyph for the naturals, built with chr so this file stays pure ASCII.
#: The project keeps non-ASCII out of its sources, and a bare literal here also
#: trips ruff's ambiguous-character rule (RUF001).
NAT: Final = chr(0x2115)

#: `RepSizeAtMost (fun (u : Fin n) (v : Fin m) => (M : Nat).testBit (m * u.val + v.val)) s`.
#: The row text varies in spacing and in whether the binders carry types, so the
#: pieces are matched separately rather than with one brittle pattern.
ROW_RE: Final = re.compile(
    r"RepSizeAtMost\s*\(fun\s*\(?\s*(\w+)\s*:?\s*(?:Fin\s*(\d+))?\s*\)?\s*"
    r"\(?\s*(\w+)\s*:?\s*(?:Fin\s*(\d+))?\s*\)?\s*=>\s*\(?\s*(\d+)\s*"
    rf"(?::\s*{NAT})?\s*\)?"
    r"\s*\.testBit[^)]*\)\s*\)\s*(\d+)"
)

#: THE SHARED-BINDER FORM, which ROW_RE does not reach. Upstream writes square
#: rows as `fun u v : Fin 8 => ...` - one annotation for both binders - and
#: ROW_RE only matches the per-binder form `(u : Fin 4) (v : Fin 6)`. Every
#: shared-binder row was therefore skipped in silence and reported as not a
#: promise row at all, which is how the 8 by 8 row L-meta-20378 and the 5 by 5
#: rows went unscreened. A test for this form is what found it.
SHARED_RE: Final = re.compile(
    r"RepSizeAtMost\s*\(fun\s+\w+\s+\w+\s*:\s*Fin\s*(\d+)\s*=>\s*\(?\s*(\d+)\s*"
    rf"(?::\s*{NAT})?\s*\)?\s*\.testBit\s*\(\s*(\d+)\s*\*[^)]*\)\s*\)\s*(\d+)"
)


def parse_row(stmt: str) -> tuple[int, int, int, int] | None:
    """(mask, n, m, budget) from a RepSizeAtMost statement, in either binder form."""
    hit = ROW_RE.search(stmt)
    if hit:
        _u, n_s, _v, m_s, mask_s, budget_s = hit.groups()
        if n_s and m_s:
            return int(mask_s), int(n_s), int(m_s), int(budget_s)
    sh = SHARED_RE.search(stmt)
    if sh:
        side_s, mask_s, stride_s, budget_s = sh.groups()
        # Both binders share the type, so the shape is side x side; the stride in
        # the testBit index must agree with it, and a disagreement means the
        # statement is not the shape this tool understands.
        if int(stride_s) != int(side_s):
            return None
        return int(mask_s), int(side_s), int(side_s), int(budget_s)
    return None


def matrix(mask: int, n: int, m: int) -> list[list[bool]]:
    return [[bool((mask >> (m * u + v)) & 1) for v in range(m)] for u in range(n)]


def forced_left(a: list[list[bool]], n: int, m: int) -> list[int]:
    return [u for u in range(n) if any(a[u][v] and any(not a[x][v] for x in range(n)) for v in range(m))]


def forced_right(a: list[list[bool]], n: int, m: int) -> list[int]:
    return [v for v in range(m) if any(a[u][v] and any(not a[u][w] for w in range(m)) for u in range(n))]


def path_witness(a: list[list[bool]], n: int, m: int) -> tuple[int, int, int, int] | None:
    """Rows u, x and columns v, w meeting every hypothesis of RepPath.path."""
    for u, x in itertools.permutations(range(n), 2):
        for v, w in itertools.permutations(range(m), 2):
            if a[u][v] and a[u][w] and a[x][v] and not a[x][w]:
                if any(not a[u][q] for q in range(m)) and any(not a[q][v] for q in range(n)):
                    return (u, x, v, w)
    return None


def bound(mask: int, n: int, m: int) -> tuple[int, list[int], list[int], tuple[int, int, int, int] | None]:
    """The least size the counting lemmas allow, with the evidence behind it."""
    a = matrix(mask, n, m)
    lhs, rhs = forced_left(a, n, m), forced_right(a, n, m)
    wit = path_witness(a, n, m)
    total = len(lhs) + len(rhs)
    return (total if wit is not None else total - 1), lhs, rhs, wit


def describe(mask: int, n: int, m: int, budget: int, out: object = sys.stdout) -> bool:
    """Print the verdict. Returns True when the row is PROVABLY false."""
    w = out.write  # type: ignore[attr-defined]
    least, lhs, rhs, wit = bound(mask, n, m)
    a = matrix(mask, n, m)
    w(f"mask {mask} on {n}x{m}, posted budget {budget}\n")
    for u in range(n):
        w("      " + "".join("1" if a[u][v] else "." for v in range(m)) + "\n")
    w(f"  forcedL {lhs} (card {len(lhs)})   forcedR {rhs} (card {len(rhs)})\n")
    if wit is not None:
        w(f"  RepPath.path applies with (u,x,v,w) = {wit}, so size >= {least}\n")
    else:
        w(f"  no path witness; RepReads.reads_le alone, so size >= {least}\n")
    if budget < least:
        w(
            f"  VERDICT: FALSE, and PROVED - no monotone circuit of {budget} gates exists because\n"
            f"  every one has at least {least}. Release statement_seems_false. If the row is a REFUTE\n"
            "  row, this is a win: cite the lemma and submit, do not search.\n"
        )
        return True
    w(
        f"  VERDICT: undecided here - the budget {budget} is at or above the counting bound {least}.\n"
        "  Counting is a LOWER bound and can never show a row true; this one still needs a witness.\n"
    )
    return False


def scan() -> int:
    """Run the screen over every statement the desk has ever handed us."""
    hits = 0
    for p in sorted((S / "steps").glob("*.json")):
        try:
            rec = json.load(open(p))
        except (OSError, json.JSONDecodeError):
            continue
        gap = rec.get("gap")
        if not isinstance(gap, dict):
            continue
        stmt = str(gap.get("statement", ""))
        parsed = parse_row(stmt)
        if parsed is None:
            continue
        mask_i, n_i, m_i, budget_i = parsed
        lease = rec.get("lease")
        terms = lease.get("terms") if isinstance(lease, dict) else {}
        terms = terms if isinstance(terms, dict) else {}
        negated = "¬" in stmt.split("RepSizeAtMost")[0][-8:]
        sys.stdout.write(
            f"\n=== {gap.get('id')}  {terms.get('points', 0)}pt  kind={terms.get('kind')}"
            f"  {'NEGATED STATEMENT' if negated else 'positive statement'} ===\n"
        )
        if describe(mask_i, n_i, m_i, budget_i):
            hits += 1
            if negated or terms.get("kind") == "refute":
                sys.stdout.write("  *** THIS ROW IS WINNABLE: it asks for the negation we can prove ***\n")
    sys.stdout.write(f"\n{hits} stored row(s) are provably false by counting.\n")
    return 0


def verdict_of(step_id: str) -> int:
    """Print ONE word for one step: FALSE, UNDECIDED or NOTAROW.

    --scan prints a block per row and callers were grepping it with a fixed
    -A window. That silently broke on taller matrices: a 4 by 6 row pushes its
    VERDICT line one further than a 3 by 5 row, so `grep -A7` found the verdict
    for 3-row masks and NOTHING for 4-row masks - and a missing verdict read as
    `undecided`, which is how two rows that were provably false were nearly kept
    as if they might be winnable. A caller should ask about one row and get one
    word, with no window to get wrong.
    """
    p = S / "steps" / f"{step_id}.json"
    if not p.is_file():
        sys.stdout.write("NOTAROW\n")
        return 2
    try:
        stmt = str((json.load(open(p)).get("gap") or {}).get("statement", ""))
    except (OSError, json.JSONDecodeError):
        sys.stdout.write("NOTAROW\n")
        return 2
    parsed = parse_row(stmt)
    if parsed is None:
        sys.stdout.write("NOTAROW\n")
        return 2
    mask_i, n_i, m_i, budget_i = parsed
    least, _lhs, _rhs, _wit = bound(mask_i, n_i, m_i)
    # `bound` already folds in whether a path witness exists: with one it returns
    # the sharp sum, without one the weaker reads_le value. So one comparison is
    # correct in both cases and there is no second branch to get out of step.
    sys.stdout.write("FALSE\n" if budget_i < least else "UNDECIDED\n")
    return 0


def main(argv: list[str]) -> int:
    if argv and argv[0] == "--verdict":
        if len(argv) < 2:
            sys.stderr.write("usage: promise.py --verdict <step-id>\n")
            return 2
        return verdict_of(argv[1])
    if argv and argv[0] == "--scan":
        return scan()
    if len(argv) < 4:
        sys.stderr.write("usage: promise.py <mask> <n> <m> <budget> | promise.py --scan\n")
        return 2
    describe(int(argv[0]), int(argv[1]), int(argv[2]), int(argv[3]))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
