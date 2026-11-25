#!/usr/bin/env python3
"""Write the skeleton file for a step: its declared imports and the exact statement.

IMPORT ONLY WHAT THE STEP DECLARES. This file used to emit `import Mathlib` on top
of the step's own `gap.imports`, and that one line cost a factor of SEVENTY-ONE on
every single check:

    import Mathlib + PEqualNP.Defs ... 112266 ms
    import PEqualNP.Defs only      ...   1575 ms

That matters more than it looks. The desk gives a step to ONE agent first and lets a
second join after five minutes without a proof, a third after ten, with the first
accepted proof merged and credited. At 112 s a check, a five-minute exclusive window
buys two attempts; at 1.6 s it buys well over a hundred. Two steps were lost to other
participants while this was costing two minutes a build.

It is also what the accepted proofs do: L_meta_3935 and L_meta_1667, both merged, use
no `import Mathlib` at all - only narrow modules such as Mathlib.Data.Finset.Card.
join.txt says so in as many words: "Import only what you use."

If a proof turns out to need a Mathlib lemma that `gap.imports` does not reach, add
that ONE module (`import Mathlib.Data.Finset.Card`), never all of Mathlib.

usage: skeleton.py <step-id> [--force]
"""

import json
import os
import sys

S = os.path.dirname(os.path.abspath(__file__))
REPO = "/home/user/pequalnp-proofs"

g = json.load(open(os.path.join(S, "steps", sys.argv[1] + ".json")))["gap"]
full = os.path.join(REPO, g["file"])
os.makedirs(os.path.dirname(full), exist_ok=True)
if os.path.exists(full) and "--force" not in sys.argv:
    print("exists, not overwriting:", g["file"])
    sys.exit(0)

declared = list(g.get("imports") or [])
if not declared:
    # Nothing declared is unexpected; the project definitions are the minimum.
    declared = ["PEqualNP.Defs"]
imports = "".join("import %s\n" % m for m in declared)
open(full, "w").write("%s\ntheorem %s : %s := by\n  sorry\n" % (imports, g["module"], g["statement"]))
print("skeleton written:", g["file"], "| imports:", ", ".join(declared))
