#!/usr/bin/env python3
"""Decide in ~2 seconds whether a drawn step is worth working.

Written after an audit: ~1.0M worker tokens went on four steps of weight 50-93
and produced ZERO submissions, while both ACCEPTED proofs came from cheap routes
- a parent already merged in the repo (L-meta-3935, weight 5) and a reduction.
The bottleneck was never speed of work, it was choice of work.

usage: triage.py <step-id> [...]
Prints a verdict per step: TAKE (with the route), or SKIP (with the reason).
"""

from __future__ import annotations

import json
import pathlib
import re
import sys

S = pathlib.Path(__file__).resolve().parent
REPO = pathlib.Path("/home/user/pequalnp-proofs")
OUTSIDE = REPO / "lean" / "PEqualNP" / "Outside"

#: Steps at or above this weight sat on the program's open frontier every time.
FRONTIER_WEIGHT = 40
#: Phrases by which the desk itself says it expects no proof.
NO_PROOF = ("no proof is expected", "propose a cut")


def merged(step_id: str) -> bool:
    """Whether that step's proof file is already in the repo (so reusable)."""
    name = step_id.replace("-", "_").replace("L_meta", "L_meta")
    return (OUTSIDE / f"{name}.lean").exists()


def named_kin(sketch: str) -> list[str]:
    """Every L-meta/R-meta id the sketch points at: parents and siblings."""
    return sorted(set(re.findall(r"[LR]-meta-\d+(?:-\d+)?", sketch)))


def triage(step_id: str) -> tuple[bool, int, list[str]]:
    """(take, score, reasons). Higher score = work it sooner."""
    path = S / "steps" / f"{step_id}.json"
    if not path.exists():
        return False, -99, ["no cached step file; draw it first"]
    g = json.load(open(path))["gap"]
    sketch = (g.get("sketch") or "") + " " + (g.get("context") or "")
    stmt = g.get("statement") or g.get("goal") or ""
    weight = g.get("weight") or 0
    why: list[str] = []
    score = 0

    # The single best predictor we have: a proof of a relative already in-repo.
    kin = [k for k in named_kin(sketch) if k != step_id]
    have = [k for k in kin if merged(k)]
    if have:
        score += 60
        why.append(f"TEMPLATE IN REPO: {', '.join(have)} - copy, rename the namespace, adapt")
    elif kin:
        why.append(f"names kin {', '.join(kin)} but none is in the repo")

    # Weight, calibrated against this session's outcomes.
    if weight <= 10:
        score += 30
        why.append(f"weight {weight} is in the band our accepted proof came from")
    elif weight < FRONTIER_WEIGHT:
        score += 10
        why.append(f"weight {weight} is moderate")
    else:
        score -= 40
        why.append(f"weight {weight} >= {FRONTIER_WEIGHT}: every such step was frontier")

    # The desk telling us it expects no proof is decisive.
    low = sketch.lower()
    if any(p in low for p in NO_PROOF):
        score -= 50
        why.append("the desk itself expects no proof here, only a cut")

    # Shape. An existential with small arity can often be closed by `decide`.
    if stmt.lstrip().startswith("∃"):
        score += 15
        why.append("constructive (exhibit an object) - cheaper than a lower bound")
    if "exact negation of another step" in low:
        score += 15
        why.append("refutation step: one explicit counterexample settles it")
    ar = [int(n) for n in re.findall(r"Fin \((\d+)", stmt)]
    if ar:
        a = max(ar)
        if a <= 10:
            score += 15
            why.append(f"arity {a}: 2^{a} is inside `decide`")
        elif a >= 20:
            score -= 15
            why.append(f"arity {a}: too big to decide")
    if len(stmt) > 2000:
        score -= 10
        why.append(f"statement is {len(stmt)} chars: many conjuncts to discharge")

    return score > 0, score, why


def main(argv: list[str]) -> int:
    if not argv:
        sys.stderr.write(__doc__ or "")
        return 2
    for step_id in argv:
        take, score, why = triage(step_id)
        sys.stdout.write(f"{'TAKE' if take else 'SKIP'}  {step_id}  score={score}\n")
        for w in why:
            sys.stdout.write(f"        - {w}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
