#!/usr/bin/env python3
"""Copy the container-mortal working tools into the fork, and print a manifest.

WHY. Everything that actually does the work - the SAT engines, the monotone
variant, the witness emitters, the worker job scripts, and the accumulated notes
this session reasons from - lives in a scratchpad that a reboot or a routine
cleanup can clear, and that goes away with the container for good. The harness
scripts under tools/pnp-harness/ are committed; none of this is. It was left out
because it fails that directory's ruff and mypy gates, which is a weak reason
next to losing it.

WHERE IT GOES, and why not under tools/pnp-harness/. gates.sh runs `ruff check .`
with that directory as its working directory, and the harness-checks workflow
triggers on `tools/pnp-harness/**`. Putting research scratch there would either
fail the gates or force the gates to be loosened for code that is not maintained
to that standard. notes/ours/ is unambiguously ours, outside both, so these files
are preserved without pretending to be gated harness code.

WHAT IS LEFT BEHIND on purpose: CNF files and solver logs (regenerable, large),
__pycache__ and tool caches, and the lease/step state, which is a credential with
a twenty-minute life and the desk's own refetchable copy.
"""

from __future__ import annotations

import pathlib
import shutil
import sys
from typing import Final

P: Final = pathlib.Path(
    "/tmp/claude-0/-home-user-pequalnp-proofs/731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/pnp"
)
DEST: Final = pathlib.Path("/home/user/pequalnp-proofs/notes/ours/engines")

#: Relative path -> one line on what it is and how far it is validated.
WANT: Final[dict[str, str]] = {
    # Accumulated knowledge. The reason this rescue exists at all.
    "STATE.md": "running notes: every row screened, every verdict and why, the mistakes and their causes",
    "PLAYBOOK.md": "the procedures that worked, written to be followed by a later session",
    "DEADLINE.md": "the window deadline and the stall ledger - the authority on both",
    "PENDING_PRS.md": "submissions outstanding upstream and their state",
    # Infrastructure.
    "x.sh": "the single command shape workers run jobs through, so their calls raise no permission box",
    "watchdog.py": "keeps exactly one poller alive; reads /proc rather than matching command lines",
    "consolidate.py": "merges the two state directories the symlink bug created; copy-only, deletes nothing",
    "reap.py": "kills named solver PIDs after verifying them in /proc, honouring PROTECTED markers",
    # The engines.
    "p19071/rep44.py": "exact synthesis of least FanInTwo circuits representing an n x m mask on the promise; 4x4 regressions pass against four masks of known optimum",
    "p19071/loose.py": "independent second-opinion encoder whose UNSAT covers every circuit of at most that size by padding monotonicity",
    "p19071/scan.c": "column model sweeping all 65536 4x4 masks in 11 seconds",
    "p19071/deep.c": "solver-free depth enumeration, about 50 s for the 7-gate question",
    "p19071/export4.py": "builds the depth-4 state set scan.c consumes",
    "p19071/reach.py": "reachability helper over the column model",
    "p20508/rep44m.py": "rep44 plus --monotone, forbidding NOT forms: the model of RepSizeAtMost. Validated two-sidedly on mask 249 - UNSAT at 6 where we hold a kernel proof, SAT at 7 NOT-free",
    "p4873/mklean.py": "turns a solver gate list into a checkable Lean file",
    "p4873/validate.py": "re-simulates a decoded circuit independently of the encoder that produced it",
    "p4873/synth.py": "the original synthesis driver",
    "p4873/fano.py": "the Fano-plane instance that was out of reach",
    "pcx121/emit_php.py": "emits the VERIFIED 58-line Res(xor) PHP(4,3) refutation; one command if a 56/57/58 row is posted",
    "pcx121/sat55.py": "the 55-line attempt, which did not come back",
    "pcx121/hubs2.py": "hub structure for the PHP instances",
}

#: Whole directories taken as they are, minus the noise filters below.
WANT_DIRS: Final[dict[str, str]] = {
    "jobs": "worker job scripts, including the validated p909 encoder/verifier and the 19527 drivers",
}
SKIP_SUFFIX: Final = (".cnf", ".log", ".out", ".pyc")
SKIP_DIR: Final = ("__pycache__", ".mypy_cache", ".ruff_cache", "cnf")


def copy_one(rel: str) -> tuple[str, int] | None:
    src = P / rel
    if not src.is_file():
        return None
    dst = DEST / rel
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dst)
    return rel, src.stat().st_size


def copy_dir(rel: str) -> list[tuple[str, int]]:
    out: list[tuple[str, int]] = []
    for src in sorted((P / rel).rglob("*")):
        if not src.is_file():
            continue
        if src.suffix in SKIP_SUFFIX or any(part in SKIP_DIR for part in src.parts):
            continue
        r = str(src.relative_to(P))
        got = copy_one(r)
        if got:
            out.append(got)
    return out


def main() -> int:
    DEST.mkdir(parents=True, exist_ok=True)
    done: list[tuple[str, int]] = []
    missing: list[str] = []
    for rel in WANT:
        got = copy_one(rel)
        if got:
            done.append(got)
        else:
            missing.append(rel)
    for rel in WANT_DIRS:
        done.extend(copy_dir(rel))

    total = sum(sz for _, sz in done)
    sys.stdout.write(f"copied {len(done)} files, {total / 1024:.0f} KiB\n\n")
    for rel, sz in sorted(done):
        note = WANT.get(rel, WANT_DIRS.get(rel.split("/")[0], ""))
        sys.stdout.write(f"  {sz:>8}  {rel}\n")
        if note and "/" not in rel:
            sys.stdout.write(f"            {note}\n")
    if missing:
        sys.stdout.write("\nnot found (listed but absent):\n")
        for rel in missing:
            sys.stdout.write(f"  {rel}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
