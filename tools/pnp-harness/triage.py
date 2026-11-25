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

import difflib
import json
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

import eligible

S = pathlib.Path(__file__).absolute().parent
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
    # ONLY a proof file is a template. An earlier version also returned True when
    # a merged REDUCTION of the kin existed, so triage announced
    # "TEMPLATE IN REPO: L-meta-3773 - copy, rename the namespace, adapt" for a
    # step whose L_meta_3773.lean does not exist at all. A reduction of a relative
    # is not something you can copy and rename into a proof.
    return (OUTSIDE / f"{step_id.replace('-', '_')}.lean").exists()


def reductions_of(step_id: str) -> list[str]:
    """MERGED reductions of this step, read from upstream/main.

    Two things learned the hard way. First, the count must come from upstream, not
    from the working directory: globbing OUTSIDE counted our own uncommitted
    R_meta_8647_1.lean and reported "1/3 used" for a step with no merged reduction
    at all. Second, this count is the only available signal for whether the step is
    open to reductions: the desk refuses one with "its row in the desk file does
    not say reductions: true", that flag is not in any reachable API or file, and a
    merged reduction is proof the flag was set.
    """
    return eligible.merged_reductions().get(step_id, [])


def statement_of(step_id: str) -> str:
    """The posted statement of a merged proof, taken from its theorem signature."""
    f = OUTSIDE / f"{step_id.replace('-', '_')}.lean"
    if not f.exists():
        return ""
    m = re.search(
        rf"theorem PEqualNP\.Outside\.{step_id.replace('-', '_')} :\s*(.*?)\s*:=",
        f.read_text(),
        re.S,
    )
    return " ".join(m.group(1).split()) if m else ""


def similarity(step_id: str, kin_id: str) -> float:
    """How close our posted statement is to a merged relative's, 0 to 1."""
    try:
        mine = " ".join(str(json.load(open(S / "steps" / f"{step_id}.json"))["gap"]["statement"]).split())
    except (OSError, KeyError):
        return 0.0
    theirs = statement_of(kin_id)
    if not mine or not theirs:
        return 0.0
    return difflib.SequenceMatcher(None, theirs, mine).ratio()


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
            f"reductions FULL: {len(slots)} merged ({', '.join(slots)}); the cap is three, "
            "so only a proof or a refutation is left here"
        )
    elif slots:
        score += 40
        why.append(
            f"PROVEN open to reductions ({len(slots)}/3 merged: {', '.join(slots)}) - "
            "a reduction here will actually be checked"
        )
    else:
        # A merged reduction is the only available evidence that the step's desk row
        # says `reductions: true`. With none, the desk closes a reduction unchecked -
        # which is how two submissions were lost today.
        why.append(
            "no merged reduction exists, so reduction eligibility is UNKNOWN: two such "
            "submissions were closed unchecked today. AIM AT A PROOF, not a reduction"
        )

    kin = [k for k in named_kin(sketch) if k != step_id]
    have = [k for k in kin if merged(k)]
    # Existence of a relative's proof is not enough: it is only a TEMPLATE if its
    # statement is close to ours. L-meta-2872's relative L-meta-2874 exists and is
    # 738 lines, but scores 0.36 similarity - a construction upper bound against a
    # replacement claim - so "copy, rename, adapt" would have been wasted effort.
    close = [(k, r) for k in have if (r := similarity(step_id, k)) >= 0.75]
    if close:
        score += 60
        best = ", ".join(f"{k} ({r:.2f})" for k, r in close)
        why.append(f"TEMPLATE IN REPO: {best} - copy, rename the namespace, adapt")
    elif have:
        score += 10
        loose = ", ".join(f"{k} ({similarity(step_id, k):.2f})" for k in have)
        why.append(f"relatives in repo but statements differ: {loose} - same family, NOT a copy")
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
        # Only worth taking at this weight if a reduction is actually permitted here;
        # otherwise it is a frontier step we can neither prove nor cut.
        # `slots` being non-empty proves the step ALLOWS reductions, but three of
        # them means no slot is free - so a reduction is still unavailable. An
        # earlier version tested only `if slots` and cheerfully told the caller
        # "reductions ARE open here" one line after reporting them FULL.
        if 0 < len(slots) < 3:
            score += 10
            why.append(
                f"weight {weight} >= {FRONTIER_WEIGHT}: not provable, but reductions ARE "
                "open here with a slot free, so aim at 2 to 4 hypotheses"
            )
        else:
            score -= 30
            why.append(
                f"weight {weight} >= {FRONTIER_WEIGHT} and reductions not known to be open: "
                "no realistic artifact here, skip it"
            )

    # The desk telling us it expects no proof is decisive.
    if any(p in low for p in NO_PROOF):
        # NO SCORE. This phrase is not evidence that reductions are open, and
        # treating it as such cost two submissions: both L-meta-8647 and
        # L-meta-3457 had sketches asking for a cut, and both reductions were
        # closed unchecked because their desk rows did not say reductions: true.
        # The sketch describes the intended MATHEMATICS, not the artifact the
        # checker will accept. Only a merged R_ file settles that.
        why.append(
            "the sketch asks for a cut, which is NOT evidence that reductions are "
            "open - both closed reductions had this phrase; eligible.py decides"
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
