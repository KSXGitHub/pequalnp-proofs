#!/usr/bin/env python3
# Write a scratch file proving the NEGATION of a posted statement, verbatim from the desk JSON.
import json, os, sys
S = os.path.dirname(os.path.abspath(__file__)); REPO = "/home/user/pequalnp-proofs"
gid = sys.argv[1]; proof = open(sys.argv[2]).read()
g = json.load(open(os.path.join(S, "steps", gid + ".json")))["gap"]
imports = "".join("import %s\n" % m for m in (g.get("imports") or []))
name = "zz_refute_" + gid.replace("-", "_")
body = ("import Mathlib\n%s\nset_option maxHeartbeats 1000000 in\ntheorem %s : ¬ (%s) := by\n%s"
        % (imports, name, g["statement"], proof))
p = os.path.join(REPO, "lean/PEqualNP/Outside/%s.lean" % name)
open(p, "w").write(body)
print("lean/PEqualNP/Outside/%s.lean" % name)
