#!/usr/bin/env python3
"""Pre-flight linter for the format rules that upstream refuses outright.

Catching these here costs no check run, and a check run can take minutes on a
cold cache.

TWO MODES, because a reduction is shaped differently from a proof:

  lint.py <step-id>                  the proof file gap.file, whose theorem must
                                     read `theorem <gap.module> : <statement> :=`
  lint.py <step-id> --reduction <k>  the file R_<prog>_<n>_<k>.lean, whose theorem
                                     is `theorem PEqualNP.Outside.R_<prog>_<n>_<k>
                                     (h1 : ...) ... : <statement> := ...`

The reduction mode exists because the proof-only version reported
FileNotFoundError on a perfectly good reduction - it went looking for
L_meta_8647.lean when the artifact was R_meta_8647_1.lean - and that would have
blocked a verified submission.

Rewritten in typed Python (mypy --strict) at the user's request: scripts with
logic should not be loose or untyped, and this one is a gate.
"""

from __future__ import annotations

import json
import pathlib
import re
import sys
from typing import Final

S: Final = pathlib.Path(__file__).absolute().parent
REPO: Final = pathlib.Path("/home/user/pequalnp-proofs")
MAX_BYTES: Final = 512 * 1024
FORBIDDEN: Final = ("initialize", "macro", "syntax", "notation", "elab", "native_decide")
OK_ATTRS: Final = ("simp", "local simp")
OK_OPTIONS: Final = ("maxRecDepth", "maxHeartbeats", "synthInstance.maxSize", "synthInstance.maxHeartbeats")
DECL: Final = re.compile(r"(theorem|lemma|def|abbrev|instance|structure|inductive|class)\b")


def reduction_name(step_id: str, k: int) -> str:
    m = re.fullmatch(r"L-([a-z0-9]+)-(\d+)", step_id)
    if not m:
        raise SystemExit(f"{step_id} is not of the form L-<prog>-<n>")
    return f"R_{m.group(1)}_{m.group(2)}_{k}"


def main(argv: list[str]) -> int:
    if not argv:
        sys.stderr.write(__doc__ or "")
        return 2
    step_id = argv[0]
    gap = json.load(open(S / "steps" / f"{step_id}.json"))["gap"]
    stmt = str(gap["statement"])
    allowed = {str(m) for m in (gap.get("imports") or [])}

    if "--reduction" in argv:
        k = int(argv[argv.index("--reduction") + 1])
        base = reduction_name(step_id, k)
        rel = f"lean/PEqualNP/Outside/{base}.lean"
        module = f"PEqualNP.Outside.{base}"
        is_reduction = True
    else:
        rel = str(gap["file"])
        module = str(gap["module"])
        is_reduction = False

    full = REPO / rel
    if not full.exists():
        sys.stdout.write(f"FATAL: {rel} does not exist\n")
        return 1
    raw = full.read_bytes()
    bad: list[str] = []
    warn: list[str] = []
    if len(raw) > MAX_BYTES:
        bad.append("file is larger than 512 KiB")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as e:
        sys.stdout.write(f"FATAL: not UTF-8: {e}\n")
        return 1
    lines = text.split("\n")

    # Imports must be a prefix of plain `import X` lines, and nothing else.
    i = 0
    imports: list[str] = []
    while i < len(lines) and lines[i].startswith("import "):
        m = re.fullmatch(r"import ([A-Za-z0-9_.]+)", lines[i].rstrip())
        if m is None:
            bad.append(f"line {i + 1} is not a plain `import Some.Module`: {lines[i]!r}")
        else:
            imports.append(m.group(1))
        i += 1
    if not imports:
        bad.append("no import lines at the top")
    rest = "\n".join(lines[i:])
    if re.search(r"\bimport\b", rest):
        bad.append("the word `import` appears after the import lines")
    for mod in imports:
        if mod == "Mathlib" or mod.startswith("Mathlib.") or mod in allowed:
            continue
        bad.append(f"import not allowed for this step: {mod} (besides Mathlib: {sorted(allowed) or 'none'})")

    if '"' in text:
        bad.append("a double quote appears in the file: no string literals")
    for tok in FORBIDDEN:
        for n, line in enumerate(lines[i:], start=i + 1):
            if re.search(rf"\b{tok}\b", line):
                bad.append(f"forbidden word `{tok}` on line {n} - reword even in comments")
    for n, line in enumerate(lines[i:], start=i + 1):
        if re.match(r"\s*#", line):
            bad.append(f"a `#` command on line {n}")
        if re.match(r"\s*attribute\b", line):
            bad.append(f"an `attribute` command on line {n}")
        if re.match(r"\s*set_option", line) and not re.fullmatch(
            rf"set_option ({'|'.join(re.escape(o) for o in OK_OPTIONS)}) \d+ in", line.strip()
        ):
            bad.append(f"line {n}: set_option must be exactly one of the four, with a number, then `in`")
    for m in re.finditer(r"@\[([^\]]*)\]", rest):
        if m.group(1).strip() not in OK_ATTRS:
            bad.append(f"attribute @[{m.group(1).strip()}] is not allowed; only @[simp] and @[local simp]")
    if re.search(r"\bsorry\b", rest) or re.search(r"\bsorryAx\b", rest):
        bad.append("`sorry` is still in the file")
    if re.search(r"^\s*axiom\b", rest, re.M):
        bad.append("a new `axiom` is declared")

    # The one theorem, carrying the posted statement verbatim. A proof states it
    # directly; a reduction states it as the conclusion after its hypotheses, so
    # only the statement's own presence can be demanded there.
    if is_reduction:
        if f"theorem {module}" not in text:
            bad.append(f"the theorem is not named `{module}`")
        if stmt not in text:
            bad.append("the posted statement does not appear VERBATIM as the conclusion")
        if re.search(r"^\s*namespace\b", text, re.M):
            bad.append("a reduction declares no namespace; the theorem stands at the top level")
    elif f"theorem {module} : {stmt} :=" not in text:
        bad.append(
            f"the file must contain, character for character, `theorem {module} : <the posted "
            "statement> :=`. Do not reformat, rewrap, rename a binder or add parentheses."
        )

    outside: list[tuple[int, str]] = []
    depth = 0
    for n, line in enumerate(lines[i:], start=i + 1):
        if re.match(r"(namespace|section)\b", line):
            depth += 1
        elif re.match(r"end\b", line):
            depth -= 1
        elif depth == 0 and DECL.match(line):
            outside.append((n, line.split(":")[0][:90]))
    for n, head in outside:
        if not head.startswith(f"theorem {module}"):
            bad.append(f"line {n} declares `{head.strip()}` at the top level; only `{module}` may")
    count = sum(1 for _, head in outside if head.startswith(f"theorem {module}"))
    if count != 1:
        bad.append(f"expected exactly one top-level `theorem {module}`, found {count}")

    for n, line in enumerate(lines[i:], start=i + 1):
        s = line.strip()
        if s.startswith("--") or not s:
            continue
        if re.match(r"(structure|inductive|instance|class)\b", s):
            warn.append(f"line {n} declares its own data type or instance: judged, but waits for a person")

    sys.stdout.write(f"FILE   {rel}\nMODULE {module}\n")
    if bad:
        sys.stdout.write("\nLINT FAILED - these are refused outright:\n")
        for b in bad:
            sys.stdout.write(f"  * {b}\n")
    if warn:
        sys.stdout.write("\nLINT WARNINGS (judged, but merged only after a person reads it):\n")
        for w in sorted(set(warn)):
            sys.stdout.write(f"  - {w}\n")
    if not bad:
        sys.stdout.write("\nLINT OK" + (" (with warnings)" if warn else "") + "\n")
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
