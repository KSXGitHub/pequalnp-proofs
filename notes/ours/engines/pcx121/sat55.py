#!/usr/bin/env python3
"""Exact SAT search for a short Res(+) refutation of PHP m n over a clause pool.

Every heuristic I have plateaus at 58 lines, so this asks the question directly:
is there a refutation of at most B lines all of whose lines lie in a pool P?

A refutation is a set S of pool clauses with the empty clause in S, every member
an axiom or the resolvent of two members, acyclically.  Acyclicity is imposed by
fixing a total order on P in advance and allowing a step only when both premises
come EARLIER (closer to the axioms) than the conclusion; the order used is the
min TREE cost of deriving a clause from the axioms, which is checked against a
known refutation first, so the encoding provably contains at least that one.

    keep_c                                  c is a line
    keep_empty
    keep_c -> (c is an axiom) or OR_s y_s   every kept line is justified
    y_s -> keep_a, y_s -> keep_b            a step needs its premises
    sum keep_c <= B                         the length bound

UNSAT here means "no refutation of that length inside this pool and this order",
which is NOT a lower bound on refutation length -- it is reported as such.

usage: sat55.py [--m M] [--l L] [--w W] [--bound B] [--init C.json] [--out F]
"""

from __future__ import annotations

import argparse
import itertools
import json
import pathlib
import sys
import time

import numpy as np

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "pcx131"))

from pysat.card import EncType, ITotalizer  # type: ignore[import-untyped]
from pysat.formula import IDPool  # type: ignore[import-untyped]
from pysat.solvers import Cadical153  # type: ignore[import-untyped]

import dtree  # noqa: E402
from opt import Space, dijkstra  # noqa: E402
import random  # noqa: E402


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--kind", default="php")
    ap.add_argument("--m", type=int, default=4)
    ap.add_argument("--l", type=int, default=3)
    ap.add_argument("--w", type=int, default=4)
    ap.add_argument("--trees", type=int, default=0)
    ap.add_argument("--bound", type=int, default=50)
    ap.add_argument("--start", type=int, default=58)
    ap.add_argument("--init", action="append", default=[])
    ap.add_argument("--seed", type=int, default=121)
    ap.add_argument("--out", default="sat_cert.json")
    args = ap.parse_args()

    t0 = time.time()
    rng = random.Random(args.seed)
    sp0 = dtree.Space(args.kind, args.m, args.l)
    nv = sp0.nv
    poolset: set[int] = {0}
    for k in range(args.w + 1):
        for sub in itertools.combinations(range(nv), k):
            for signs in itertools.product((0, 1), repeat=k):
                c = 0
                for vv, sg in zip(sub, signs):
                    c |= 1 << (2 * vv + sg)
                poolset.add(c)
    if args.trees:
        tp: dict[int, set[tuple[int, int, int]]] = {}
        nat = list(range(nv))
        for t in range(args.trees):
            o = nat[:]
            if t:
                rng.shuffle(o)
            dtree.tree(sp0, o, rng, 0.0 if t == 0 else 0.4, tp)
        poolset |= set(tp)
    seeds: list[list[int]] = []
    for q in args.init:
        d0 = json.loads(pathlib.Path(q).read_text())
        cs = []
        for ln in d0["lines"]:
            e = 0
            for f in ln["eqs"]:
                v = tuple(f[0][0])
                e |= 1 << (2 * sp0.vi[v] + (0 if f[1] else 1))
            cs.append(e)
        poolset |= set(cs)
        seeds.append(cs)
    sp = Space(args.kind, args.m, args.l, 99, pool_override=sorted(poolset))
    n = sp.npool
    print(f"pool {n} clauses [{time.time() - t0:.0f}s]", flush=True)

    axmask = np.zeros(n, dtype=bool)
    axmask[sp.axioms] = True
    res = dijkstra(sp, axmask, rng, False, None, axmask)
    assert res is not None
    cost0 = res[0]
    key = sorted(range(n), key=lambda c: (float(cost0[c]), int(sp.pool[c])))
    rank = [0] * n
    for p, c in enumerate(key):
        rank[c] = p

    # the order must admit the seed refutation, or UNSAT would mean nothing
    for cs, q in zip(seeds, args.init):
        d0 = json.loads(pathlib.Path(q).read_text())
        bad = 0
        for ln in d0["lines"]:
            if ln["rule"] != "res":
                continue
            c = sp.ix[cs[int(ln["i"])]]
            a = sp.ix[cs[int(ln["D"])]]
            b = sp.ix[cs[int(ln["C"])]]
            if not (rank[a] < rank[c] and rank[b] < rank[c]):
                bad += 1
        print(f"  seed {q}: {bad} of its steps violate the order"
              f" ({'ORDER OK' if bad == 0 else 'ORDER TOO TIGHT'})", flush=True)

    # steps, vectorised: for each pivot v, every (a with v positive, b with v negative)
    pos = [np.flatnonzero(((sp.pool >> (2 * v)) & 1) == 1) for v in range(nv)]
    neg = [np.flatnonzero(((sp.pool >> (2 * v + 1)) & 1) == 1) for v in range(nv)]
    rankarr = np.array(rank, dtype=np.int64)
    steps: list[tuple[int, int, int, int]] = []
    for v in range(nv):
        pb, nb = 1 << (2 * v), 1 << (2 * v + 1)
        bs = neg[v]
        bcl = sp.pool[bs] & ~nb
        brank = rankarr[bs]
        for ai in pos[v]:
            acl = int(sp.pool[ai]) & ~pb
            rr = acl | bcl
            ri = sp.idx[rr]
            ok = ri >= 0
            ok &= rankarr[ai] < rankarr[np.where(ok, ri, 0)]
            ok &= brank < rankarr[np.where(ok, ri, 0)]
            for t in np.flatnonzero(ok):
                steps.append((int(ri[t]), int(ai), int(bs[t]), v))
    print(f"  {len(steps)} order-consistent steps [{time.time() - t0:.0f}s]",
          flush=True)

    pool_id = IDPool()
    keep = [int(pool_id.id(("k", c))) for c in range(n)]
    yvar: list[int] = []
    by_res: dict[int, list[int]] = {}
    cnf: list[list[int]] = []
    for si, (c, a, b, v) in enumerate(steps):
        y = int(pool_id.id(("y", si)))
        yvar.append(y)
        cnf.append([-y, keep[a]])
        cnf.append([-y, keep[b]])
        cnf.append([-y, keep[c]])
        by_res.setdefault(c, []).append(y)
    for c in range(n):
        if axmask[c]:
            continue
        cnf.append([-keep[c]] + by_res.get(c, []))
    cnf.append([keep[sp.empty]])
    print(f"  base CNF: {pool_id.top} vars, {len(cnf)} clauses "
          f"[{time.time() - t0:.0f}s]", flush=True)

    # one totalizer, then tighten the bound by assumption: the standard
    # SAT-UNSAT descent, so each solve starts warm from the last one
    tot = ITotalizer(lits=keep, ubound=args.start, top_id=pool_id.top)
    s_ = Cadical153(bootstrap_with=cnf)
    for cl in tot.cnf.clauses:
        s_.add_clause(list(cl))
    # phase hints from the seed refutation: start the search at a known solution
    if seeds:
        want = set()
        for cs in seeds:
            for e in cs:
                want.add(int(sp.ix[e]))
        ph = [keep[c] if c in want else -keep[c] for c in range(n)]
        s_.set_phases(literals=ph)
    model = None
    best = None
    B = args.start
    while B >= args.bound:
        ok = s_.solve(assumptions=[-tot.rhs[B]])
        print(f"  bound {B}: {'SAT' if ok else 'UNSAT'} "
              f"[{time.time() - t0:.0f}s]", flush=True)
        if not ok:
            if best is None:
                print("  (UNSAT inside THIS pool and THIS order only -- not a "
                      "lower bound on refutation length)")
                return
            break
        model = {x for x in s_.get_model() if x > 0}
        best = B
        kept_now = sum(1 for c in range(n) if keep[c] in model)
        print(f"    model keeps {kept_now} clauses", flush=True)
        B = min(B - 1, kept_now - 1)
    assert model is not None

    kept = [c for c in range(n) if keep[c] in model]
    chosen: dict[int, tuple[int, int, int]] = {}
    for si, (c, a, b, v) in enumerate(steps):
        if c in chosen or not (keep[c] in model):
            continue
        if int(pool_id.id(("y", si))) in model and keep[a] in model and keep[b] in model:
            chosen[c] = (a, b, v)
    # keep only what the empty clause needs
    seen: set[int] = set()
    stack = [sp.empty]
    while stack:
        c = stack.pop()
        if c in seen:
            continue
        seen.add(c)
        if c in chosen:
            a, b, _v = chosen[c]
            stack += [a, b]
    oldest = sorted(seen, key=lambda c: rank[c])
    newest = list(reversed(oldest))
    posn = {c: i for i, c in enumerate(newest)}
    lines = []
    for i, c in enumerate(newest):
        eqs = sorted([[[list(v)], sg] for (v, sg) in sp.dec(int(sp.pool[c]))])
        if c in chosen:
            a, b, v = chosen[c]
            assert posn[a] > i and posn[b] > i
            lines.append({"i": i, "rule": "res", "form": [list(sp.vars[v])],
                          "C": posn[b], "D": posn[a], "eqs": eqs})
        else:
            lines.append({"i": i, "rule": "ax", "eqs": eqs})
    cert = {"formula": args.kind, "m": args.m, "n": args.l,
            "length": len(newest),
            "note": "lines newest first, as IsLinDerivation requires",
            "lines": lines}
    pathlib.Path(args.out).write_text(json.dumps(cert, indent=1))
    print(f"  wrote {args.out}: {len(newest)} lines "
          f"(model kept {len(kept)})")


if __name__ == "__main__":
    main()
