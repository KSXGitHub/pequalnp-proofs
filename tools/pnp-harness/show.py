#!/usr/bin/env python3
import json, os, sys, textwrap
S = os.path.dirname(os.path.abspath(__file__))
d = json.load(open(os.path.join(S, "steps", sys.argv[1] + ".json")))
g = d["gap"]
print("ID      ", g["id"], "|", g.get("title", ""))
print("FILE    ", g["file"])
print("MODULE  ", g["module"])
print("IMPORTS ", g.get("imports"))
print("HARD    ", g.get("hard"), "| REDUCTIONS:", g.get("reductions"))
print("LEASE   ", d["lease"]["id"], "expires", d["lease"]["expires_at"])
print("UNLOCKS ", g.get("unlocks") or "")
for k in ("context", "sketch", "refutation", "shard_spec"):
    if g.get(k):
        v = g[k] if isinstance(g[k], str) else json.dumps(g[k], indent=1)
        print("\n== %s ==\n%s" % (k.upper(), v))
if g.get("dead"):
    print("\n== ALREADY FAILED ==")
    for x in g["dead"]: print(" -", x if isinstance(x, str) else json.dumps(x))
print("\n== STATEMENT (verbatim) ==")
print(g["statement"])
