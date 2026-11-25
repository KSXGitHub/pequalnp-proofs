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

#: Steps at or above this weight sat on the program's open frontier every time -
#: meaning we will not PROVE them. That is no longer disqualifying, because a
#: REDUCTION is a creditable outcome for a step we cannot prove, and hard steps
#: are far less contested than easy ones. See the scoring note below.
FRONTIER_WEIGHT = 40
#: Phrases by which the desk itself says it expects no proof.
NO_PROOF = ("no proof is expected", "propose a cut")


def merged(step_id: str) -> bool:
    """Whether a proof of that step is in the repo, EITHER as its own file or as a
    merged reduction of it.

    The first version only looked for L_meta_<n>.lean and so missed reductions
    entirely: L-meta-2373 names L-meta-2371 as kin, and R_meta_2371_418.lean is
    merged and is a perfectly good template, but the check reported "none is in
    the repo".
    """
    name = step_id.replace("-", "_")
    if (OUTSIDE / f"{name}.lean").exists():
        return True
    return bool(reductions_of(step_id))


def reductions_of(step_id: str) -> list[str]:
    """Merged reductions of this step, as file names.

    The desk allows AT MOST THREE reductions per step, so this decides whether the
    reduction route - the user's stated priority - is even open. All four Petersen
    family steps (651, 2371, 2373, 2375) already carry three each, which closed
    that route for the whole family; finding that out costs one directory listing
    and was worth knowing before spending anything.
    """
    m = re.fullmatch(r"L-([a-z0-9]+)-(\d+)", step_id)
    if not m:
        return []
    stem = f"R_{m.group(1)}_{m.group(2)}_"
    return sorted(f.name for f in OUTSIDE.glob(f"{stem}*.lean"))


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
    low = sketch.lower()
    why: list[str] = []
    score = 0

    # The single best predictor we have: a proof of a relative already in-repo.
    # Is the reduction route open at all? This is checked first because it is the
    # user's stated priority and because it is a hard gate, not a preference.
    slots = reductions_of(step_id)
    if len(slots) >= 3:
        score -= 25
        why.append(
            f"REDUCTION SLOTS FULL: {len(slots)} already merged ({', '.join(slots)}) - "
            "the cap is three, so only a proof or a refutation is left here"
        )
    else:
        score += 20
        why.append(f"reduction slots open ({len(slots)}/3 used) - the preferred artifact")

    kin = [k for k in named_kin(sketch) if k != step_id]
    have = [k for k in kin if merged(k)]
    if have:
        score += 60
        why.append(f"TEMPLATE IN REPO: {', '.join(have)} - copy, rename the namespace, adapt")
    elif kin:
        why.append(f"names kin {', '.join(kin)} but none is in the repo")

    # A negated twin is the best thing on the desk: a counterexample is sent as an
    # ordinary proof against it, it is cheap to settle either way, and we may already
    # hold the counterexample from having refuted the positive step.
    if "exact negation of another step" in low:
        score += 50
        why.append("NEGATED TWIN: a counterexample is submitted here as an ordinary proof")

    # Weight. This no longer penalises hard steps the way it did, because the
    # outcome for a step we cannot prove is now a REDUCTION rather than a release.
    # Of two ACCEPTED submissions, the one that MERGED was a reduction; the proof
    # lost because the step was weight 5 with seven in-repo templates, so another
    # agent produced a near-identical file and theirs cleared the checker first.
    # Easy for us is easy for everyone, and the merge slot goes to one of them.
    if weight <= 10:
        score += 20
        why.append(
            f"weight {weight}: provable, but easy steps are the MOST contested - "
            "only worth it if closable inside the five-minute exclusive window"
        )
    elif weight < FRONTIER_WEIGHT:
        score += 20
        why.append(f"weight {weight}: moderate, and not crowded")
    else:
        score += 10
        why.append(
            f"weight {weight} >= {FRONTIER_WEIGHT}: unlikely to be provable, so aim at a "
            "REDUCTION - 2 to 4 hypotheses, little competition, credited when they land"
        )

    # The desk telling us it expects no proof is decisive.
    if any(p in low for p in NO_PROOF):
        score += 25
        why.append(
            "the desk asks for a CUT here, which is exactly a reduction - "
            "it is telling us the intended artifact, not warning us off"
        )

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
