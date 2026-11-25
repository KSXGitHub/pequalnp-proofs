#!/usr/bin/env python3
"""Scaffold a proof from a merged relative, which is the only route that has won.

L-meta-3935 - our one ACCEPTED proof - was its parent's statement plus one unused
hypothesis, and the parent was already in the repo: copy it, rename the namespace,
discharge the extra binder, three check runs. By hand that is twenty minutes of
careful editing. This does the mechanical part in a second and leaves the small
reasoning step, so a model spends its tokens on that and nothing else.

What it writes: the kin's whole file (helpers included, which a DIRECT proof is
allowed as long as every declaration sits inside its own module namespace), with
every mention of the kin's module renamed to the target's, the kin's own theorem
preserved under the name `kin`, and the target's exact statement added at the end
to be closed - normally by `intro`ing the target's binders and applying `kin`.

usage: adapt.py <target-step-id> [kin-step-id]
"""

from __future__ import annotations

import json
import pathlib
import re
import sys

S = pathlib.Path(__file__).resolve().parent
OUTSIDE = pathlib.Path("/home/user/pequalnp-proofs/lean/PEqualNP/Outside")


def mod(step_id: str) -> str:
    return step_id.replace("-", "_")


def kin_candidates(step_id: str) -> list[str]:
    g = json.load(open(S / "steps" / f"{step_id}.json"))["gap"]
    sketch = (g.get("sketch") or "") + " " + (g.get("context") or "")
    ids = sorted(set(re.findall(r"[LR]-meta-\d+(?:-\d+)?", sketch)))
    return [k for k in ids if k != step_id and (OUTSIDE / f"{mod(k)}.lean").exists()]


def build(target: str, kin: str) -> pathlib.Path:
    g = json.load(open(S / "steps" / f"{target}.json"))["gap"]
    stmt = g["statement"]
    tmod, kmod = mod(target), mod(kin)
    src = (OUTSIDE / f"{kmod}.lean").read_text()

    # Rename every mention of the kin module to ours, so no declaration of ours
    # lands in another module's namespace (decls.sh refuses that, and upstream
    # rejects it as reduce-extra).
    out = src.replace(kmod, tmod)
    # Give the kin's own theorem a local name so we can apply it.
    out = re.sub(rf"theorem\s+PEqualNP\.Outside\.{tmod}\b", f"theorem PEqualNP.Outside.{tmod}.kin", out, count=1)

    out += f"""

/-- The posted statement. It is the relative's conclusion with its own binders, so
the usual close is to `intro` them and apply `kin`; adjust only as far as needed. -/
theorem PEqualNP.Outside.{tmod} : {stmt} := by
  sorry
"""
    dst = OUTSIDE / f"{tmod}.lean"
    dst.write_text(out)
    return dst


def main(argv: list[str]) -> int:
    if not argv:
        sys.stderr.write(__doc__ or "")
        return 2
    target = argv[0]
    kins = [argv[1]] if len(argv) > 1 else kin_candidates(target)
    if not kins:
        sys.stdout.write(f"no merged relative of {target} is in the repo; nothing to adapt\n")
        return 1
    sys.stdout.write(f"merged relatives available: {', '.join(kins)}\n")
    pick = kins[0]
    dst = build(target, pick)
    src_lines = len((OUTSIDE / f"{mod(pick)}.lean").read_text().splitlines())
    sys.stdout.write(
        f"scaffolded {dst} from {pick} ({src_lines} lines carried over, namespace renamed,\n"
        f"  its theorem kept as `kin`, the posted statement appended with one `sorry`)\n"
        f"NEXT: close that one sorry, then run check.sh / lint.py / decls.sh\n"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
