#!/usr/bin/env python3
import json, os, sys
S = os.path.dirname(os.path.abspath(__file__)); REPO = "/home/user/pequalnp-proofs"
g = json.load(open(os.path.join(S, "steps", sys.argv[1] + ".json")))["gap"]
full = os.path.join(REPO, g["file"])
os.makedirs(os.path.dirname(full), exist_ok=True)
if os.path.exists(full) and "--force" not in sys.argv:
    print("exists, not overwriting:", g["file"]); sys.exit(0)
imports = "".join("import %s\n" % m for m in (g.get("imports") or []))
open(full, "w").write("import Mathlib\n%s\ntheorem %s : %s := by\n  sorry\n" % (imports, g["module"], g["statement"]))
print("skeleton written:", g["file"])
