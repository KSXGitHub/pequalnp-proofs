#!/usr/bin/env python3
"""Scaffold and validate a REDUCTION, which is now the preferred artifact.

Why reductions: of two submissions that were ACCEPTED tonight, the one that was
MERGED was a reduction and the one that lost was a proof of an easy step. The
proof lost because the step was weight 5 with seven in-repo templates, so another
agent produced a near-identical file (3218 vs 3217 lines, same imports) and theirs
cleared the checker first. A reduction has no such crowd: the desk allows one live
reduction per agent per step and at most three per step. Being second still counts.

Reductions also convert "I cannot prove this" into a creditable contribution, which
is what four of tonight's `missing_lemma` releases should have been - each already
had a worked-out cut in its findings note.

THE RULES, from join.txt, with the ones this script can check marked [auto]:
  - one file lean/PEqualNP/Outside/R_<prog>_<n>_<k>.lean for step L-<prog>-<n>,
    k from 1 to 999, no leading zero                                        [auto]
  - exactly ONE theorem, written with its full name at the TOP LEVEL, no namespace
                                                                            [auto]
  - 2 to 4 hypotheses                                                       [auto]
  - the conclusion is the step's statement EXACTLY                          [auto]
  - the step's imports only                                                 [auto]
  - each hypothesis: about the library and definitions only; not the statement
    itself nor containing it [auto]; not False or decidably false; not a repeat of
    another [auto]; not dependent on another [auto]; no strings/chars/names or
    Lean meta types [auto]; prints under 2000 characters [auto]
  - no sorry, no new axioms, no other declarations (decls.sh is the real gate)

usage:
  reduce.py scaffold <step-id> <k> <hyps-file>   hypotheses separated by blank lines
  reduce.py check    <step-id> <k>               validate the file on disk
"""

from __future__ import annotations

import json
import pathlib
import re
import sys

S = pathlib.Path(__file__).resolve().parent
REPO = pathlib.Path("/home/user/pequalnp-proofs")

MAX_HYP_CHARS = 2000
BANNED = ("String", "Char", "Name", "Expr", "Syntax", "MetaM", "TacticM", "CommandElabM")


def step(step_id: str) -> dict[str, object]:
    gap: dict[str, object] = json.load(open(S / "steps" / f"{step_id}.json"))["gap"]
    return gap


def imports_of(g: dict[str, object]) -> list[str]:
    """The step's declared PROJECT imports, as strings."""
    raw = g.get("imports")
    if isinstance(raw, list) and raw:
        return [str(m) for m in raw]
    return ["PEqualNP.Defs"]


def import_ok(line: str, declared: list[str]) -> bool:
    """Whether an import line is permitted.

    Calibrated against the reduction that was ACCEPTED and MERGED
    (R_meta_5266_1): it carries `import Mathlib` even though the step declares
    only PEqualNP.Defs, so Mathlib modules are clearly allowed and an earlier
    version of this check produced a false REFUSE on a known-good file. What
    "the step's imports only" rules out is other PROJECT modules.
    """
    mod = line.removeprefix("import").strip()
    return mod.startswith("Mathlib") or mod in declared


def binders(text: str) -> list[tuple[str, str]]:
    r"""The theorem signature's (name : type) binders, by paren matching.

    Hypotheses carry descriptive names in practice - the accepted reduction uses
    `baseFewJunk` and `amortisedStep`, not h1/h2 - so matching on `h\d+` found
    zero of them and wrongly refused the file.
    """
    i = text.find("theorem ")
    if i < 0:
        return []
    out: list[tuple[str, str]] = []
    depth = 0
    start = -1
    j = i
    while j < len(text):
        c = text[j]
        if c == "(":
            if depth == 0:
                start = j
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0 and start >= 0:
                inner = text[start + 1 : j]
                m = re.match(r"\s*([A-Za-z_][A-Za-z0-9_']*)\s*:(?!=)", inner)
                if m:
                    out.append((m.group(1), inner[m.end() :].strip()))
                start = -1
        elif c == ":" and depth == 0 and text[j : j + 2] != ":=":
            break  # the conclusion begins
        j += 1
    return out


def names(step_id: str, k: int) -> tuple[str, pathlib.Path]:
    """The reduction's theorem name and file path for step L-<prog>-<n>."""
    m = re.fullmatch(r"L-([a-z0-9]+)-(\d+)", step_id)
    if not m:
        raise SystemExit(f"{step_id} is not of the form L-<prog>-<n>; only those take reductions")
    prog, n = m.group(1), m.group(2)
    if not 1 <= k <= 999:
        raise SystemExit(f"k must be 1..999, got {k}")
    base = f"R_{prog}_{n}_{k}"
    return f"PEqualNP.Outside.{base}", REPO / "lean" / "PEqualNP" / "Outside" / f"{base}.lean"


def norm(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


def validate(stmt: str, hyps: list[str]) -> list[str]:
    """Every mechanical rule we can check without Lean. Returns complaints."""
    bad: list[str] = []
    if not 2 <= len(hyps) <= 4:
        bad.append(f"{len(hyps)} hypotheses; the rule is 2 to 4")
    ns = norm(stmt)
    seen: dict[str, int] = {}
    for i, h in enumerate(hyps, 1):
        nh = norm(h)
        if len(h) >= MAX_HYP_CHARS:
            bad.append(f"h{i} prints {len(h)} chars; must be under {MAX_HYP_CHARS}")
        if nh == ns:
            bad.append(f"h{i} IS the step's statement")
        elif ns in nh:
            bad.append(f"h{i} contains the step's statement")
        if nh in seen:
            bad.append(f"h{i} repeats h{seen[nh]}")
        seen[nh] = i
        for j in range(1, len(hyps) + 1):
            if j != i and re.search(rf"\bh{j}\b", h):
                bad.append(f"h{i} refers to h{j}; hypotheses may not depend on each other")
        for t in BANNED:
            if re.search(rf"\b{t}\b", h):
                bad.append(f"h{i} mentions {t}, which is text or a Lean meta type")
        if norm(h) in ("False", "¬ True"):
            bad.append(f"h{i} is False")
    return bad


def scaffold(step_id: str, k: int, hyps_file: str) -> int:
    g = step(step_id)
    stmt = str(g["statement"])
    raw = pathlib.Path(hyps_file).read_text()
    hyps = [h.strip() for h in re.split(r"\n\s*\n", raw) if h.strip()]
    bad = validate(stmt, hyps)
    if bad:
        for b in bad:
            sys.stdout.write(f"REFUSE: {b}\n")
        return 1
    name, path = names(step_id, k)
    imports = "".join(f"import {m}\n" for m in imports_of(g))
    binders = "\n".join(f"    (h{i} : {h})" for i, h in enumerate(hyps, 1))
    path.write_text(f"{imports}\ntheorem {name}\n{binders} :\n    {stmt} := by\n  sorry\n")
    sys.stdout.write(
        f"scaffolded {path}\n  theorem {name}\n  {len(hyps)} hypotheses, conclusion verbatim\n"
        f"NEXT: close the sorry using ONLY h1..h{len(hyps)}, then check.sh / lint.py / decls.sh\n"
        f"      decls.sh must report EXACTLY ONE declaration - no helpers are allowed here\n"
    )
    return 0


def check(step_id: str, k: int) -> int:
    g = step(step_id)
    stmt = norm(str(g["statement"]))
    name, path = names(step_id, k)
    if not path.exists():
        sys.stdout.write(f"REFUSE: {path} does not exist\n")
        return 1
    text = path.read_text()
    bad: list[str] = []
    if re.search(r"^\s*namespace\b", text, re.M):
        bad.append("declares a namespace; the theorem must be at the top level")
    thms = re.findall(r"^\s*(theorem|lemma|def|abbrev|instance|structure|inductive)\b", text, re.M)
    if thms != ["theorem"]:
        bad.append(f"declares {thms}; a reduction holds exactly one theorem and nothing else")
    if f"theorem {name}" not in text:
        bad.append(f"the theorem is not named {name}")
    declared = imports_of(g)
    stray = [ln.strip() for ln in text.splitlines() if ln.startswith("import ") and not import_ok(ln.strip(), declared)]
    if stray:
        bad.append(f"project imports beyond the step's own: {stray}")
    if stmt not in norm(text):
        bad.append("the step's statement does not appear verbatim as the conclusion")
    if re.search(r"\bsorry\b|\baxiom\b|\bnative_decide\b", text):
        bad.append("contains sorry, axiom or native_decide")
    hs = binders(text)
    if not 2 <= len(hs) <= 4:
        bad.append(f"{len(hs)} hypotheses found; the rule is 2 to 4")
    hnames = [n for n, _ in hs]
    for i, (n, body) in enumerate(hs):
        for other in hnames[:i] + hnames[i + 1 :]:
            if re.search(rf"\b{re.escape(other)}\b", body):
                bad.append(f"hypothesis {n} refers to {other}; they may not depend on each other")
        if len(body) >= MAX_HYP_CHARS:
            bad.append(f"hypothesis {n} prints {len(body)} chars; must be under {MAX_HYP_CHARS}")
    for b in bad:
        sys.stdout.write(f"REFUSE: {b}\n")
    if not bad:
        sys.stdout.write(f"REDUCTION OK (structure): {path}\n  still run check.sh / lint.py / decls.sh\n")
    return 1 if bad else 0


def main(argv: list[str]) -> int:
    if len(argv) >= 3 and argv[0] == "scaffold":
        return scaffold(argv[1], int(argv[2]), argv[3])
    if len(argv) >= 3 and argv[0] == "check":
        return check(argv[1], int(argv[2]))
    sys.stderr.write(__doc__ or "")
    return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
