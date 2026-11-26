#!/usr/bin/env python3
"""Two-level (lemma/hub) refutation builder that EMITS a certificate.

The opt.py pass minimises TREE cost, so it cannot discover sharing.  Here a set
of lemmas is picked (every clause the axioms-only pass derives in at most tau
inferred lines), the pass derives the empty clause with those lemmas as FREE
LEAVES, and each lemma that got used is derived once from the axioms.  The lines
are the union of the top cone and the lemma cones -- shared, counted once.

Order: lemma-cone lines by their axioms-only cost, then the rest by their
with-lemmas cost.  Both costs strictly increase from premises to conclusion, so
premises always stand LATER in the newest-first list, as `res` demands.

usage: hubs2.py [--kind K] [--m M] [--l L] [--w W] [--reps R] [--out FILE]
"""
from __future__ import annotations
import argparse, json, pathlib, random, sys, time
import numpy as np
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "pcx131"))
from opt import Space, cone, dijkstra

ap = argparse.ArgumentParser()
ap.add_argument("--kind", default="php")
ap.add_argument("--m", type=int, default=4)
ap.add_argument("--l", type=int, default=3)
ap.add_argument("--w", type=int, default=4)
ap.add_argument("--reps", type=int, default=6)
ap.add_argument("--seed", type=int, default=121)
ap.add_argument("--secs", type=float, default=1500.0)
ap.add_argument("--target", type=int, default=0)
ap.add_argument("--out", default="hubs2.json")
args = ap.parse_args()

t0 = time.time()
sp = Space(args.kind, args.m, args.l, args.w)
rng = random.Random(args.seed)
axmask = np.zeros(sp.npool, dtype=bool); axmask[sp.axioms] = True
axset = set(int(x) for x in sp.axioms)
print(f"pool {sp.npool} clauses of width <= {args.w}", flush=True)
r1 = dijkstra(sp, axmask, rng, False, None, axmask)
assert r1 is not None
cost0, pa0, pb0, piv0 = r1
print(f"  axioms-only tree cost of the empty clause: {cost0[sp.empty]:.0f}", flush=True)

def assemble(top, used, pa2, pb2, piv2, cost2):
    inhub: set[int] = set()
    for h in used:
        inhub |= set(cone(sp, h, pa0, pb0))
    lines = set(top) | inhub
    just = {}
    for c in lines:
        if c in inhub:
            if pa0[c] >= 0 and pb0[c] >= 0:
                just[c] = (int(pa0[c]), int(pb0[c]), int(piv0[c]))
        else:
            if pa2[c] >= 0 and pb2[c] >= 0:
                just[c] = (int(pa2[c]), int(pb2[c]), int(piv2[c]))
    hub_b = sorted(inhub, key=lambda c: (float(cost0[c]), c))
    top_b = sorted(lines - inhub, key=lambda c: (float(cost2[c]), c))
    oldest = hub_b + top_b
    newest = list(reversed(oldest))
    pos = {c: i for i, c in enumerate(newest)}
    out = []
    for i, c in enumerate(newest):
        cl = sp.dec(int(sp.pool[c]))
        eqs = sorted([[[list(v)], s] for (v, s) in cl])
        if c in just:
            a, b, v = just[c]
            assert pos[a] > i and pos[b] > i, "premise not in the tail"
            out.append({"i": i, "rule": "res", "form": [list(sp.vars[v])],
                        "C": pos[b], "D": pos[a], "eqs": eqs})
        else:
            assert int(sp.pool[c]) in [sp.enc(a) for a in sp.axioms_c] or c in axset
            out.append({"i": i, "rule": "ax", "eqs": eqs})
    return {"formula": args.kind, "m": args.m, "n": args.l,
            "length": len(newest),
            "note": "lines newest first, as IsLinDerivation requires",
            "lines": out}

best = None
taus = [1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 20, 24, 30]
while time.time() - t0 < args.secs:
    for tau in taus:
        if time.time() - t0 > args.secs:
            break
        Lmask = (cost0 > 0) & (cost0 <= tau)
        seeds = axmask | Lmask
        for rep in range(args.reps):
            r2 = dijkstra(sp, seeds, rng, False, None, seeds)
            if r2 is None:
                continue
            cost2, pa2, pb2, piv2 = r2
            top = cone(sp, sp.empty, pa2, pb2)
            used = [c for c in top if Lmask[c]]
            cert = assemble(top, used, pa2, pb2, piv2, cost2)
            tot = cert["length"]
            if best is None or tot < best:
                best = tot
                pathlib.Path(args.out).write_text(json.dumps(cert, indent=1))
                print(f"  tau {tau} rep {rep}: {tot} lines "
                      f"(hubs {len(used)}) [{time.time()-t0:.0f}s]", flush=True)
                if args.target and tot <= args.target:
                    sys.exit(0)
print(f"best: {best} lines [{time.time()-t0:.0f}s] -> {args.out}")
