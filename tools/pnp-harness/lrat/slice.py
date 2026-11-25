#!/usr/bin/env python3
"""Cut one middle segment out of a genrow.py multi-segment row file into a standalone Lean file.

A middle segment's theorem is `checkSeg_sound c_B{k} W c_S{k} c_B{k+1} (by decide +kernel)`, which
mentions neither the formula `F` nor any other segment, so the declarations
`c_B{k}w*, c_B{k}, c_B{k+1}w*, c_B{k+1}, c_S{k}*` plus the header are a complete file.  Measuring
it alone separates the per-segment cost of `decide +kernel` from the cost that accumulates over a
whole file.

Usage: slice.py in.lean out.lean K NAMESPACE
"""

from __future__ import annotations

import re
import sys

# A top-level declaration starts at column 0 with `def`, `noncomputable def` or `theorem`.
DECL = re.compile(r"^(?:noncomputable\s+)?(?:def|theorem)\s+([A-Za-z_][A-Za-z0-9_]*)")


def split_decls(text: str) -> tuple[list[str], dict[str, str], list[str]]:
    """Return (header lines, name -> declaration text, declaration order)."""
    lines = text.splitlines(keepends=True)
    header: list[str] = []
    decls: dict[str, str] = {}
    order: list[str] = []
    cur: str | None = None
    buf: list[str] = []
    for line in lines:
        m = DECL.match(line)
        if m is not None:
            if cur is not None:
                decls[cur] = "".join(buf)
            cur = m.group(1)
            order.append(cur)
            buf = [line]
        elif cur is None:
            header.append(line)
        else:
            buf.append(line)
    if cur is not None:
        decls[cur] = "".join(buf)
    return header, decls, order


def main() -> int:
    src, dst, k_s, ns = sys.argv[1:5]
    k = int(k_s)
    with open(src) as fh:
        header, decls, order = split_decls(fh.read())
    want_prefixes = (f"c_B{k}w", f"c_B{k + 1}w", f"c_S{k}")
    want_exact = (f"c_B{k}", f"c_B{k + 1}")
    keep = [nm for nm in order if nm in want_exact or any(nm == p or nm.startswith(p + "_") for p in want_prefixes)]
    if f"c_B{k}" not in keep or f"c_S{k}" not in keep:
        print(f"slice.py: segment {k} is not a middle segment of {src}", file=sys.stderr)
        return 1
    body = "".join(decls[nm] for nm in keep)
    thm = (
        f"theorem seg{k} : ∀ a, EntriesSat a c_B{k} → EntriesSat a c_B{k + 1} :=\n"
        f"  checkSeg_sound c_B{k} 17 c_S{k} c_B{k + 1} (by decide +kernel)\n"
    )
    head = "".join(line for line in header if not line.startswith("end "))
    with open(dst, "w") as o:
        o.write(head)
        o.write(body)
        o.write("\n" + thm + f"\nend {ns}\n")
    print(f"kept {len(keep)} declarations for segment {k}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
