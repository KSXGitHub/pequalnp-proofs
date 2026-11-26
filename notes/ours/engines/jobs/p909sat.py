# L-meta-909. Does an AndCountCircuit on Fin 10 with <= 6 AND gates, every variable bare in
# at most two gates, exist that is false on every maximal independent set of the Petersen graph
# and true on every one-vertex extension of one?
#
# Self-contained (run under python3 -I): rebuilds the graph from the posted edge list.
#
# usage: x.sh p909sat SIZE READ MODE [SOLVER] [TAG]
#   MODE   loose = no symmetry breaking (hunt for a witness)
#          tight = sound symmetry breaking (for reaching UNSAT); see S1/S2/S3 below.
#                  tight is complete only together with the separate runs for every smaller
#                  size, because S1/S2 delete a gate rather than keep a padded one.
import itertools, json, sys, time, os

OUT = "/tmp/claude-0/-home-user-pequalnp-proofs/731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/p909"
EDGES = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
         (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
N = 10


def adj(a, b):                                    # SimpleGraph.fromRel of the posted list
    return a != b and ((a, b) in EDGES or (b, a) in EDGES)


MIS = []
for r in range(N + 1):
    for S in itertools.combinations(range(N), r):
        U = set(S)
        if all(not adj(a, c) for a in U for c in U) and \
           all(w in U or any(adj(a, w) for a in U) for w in range(N)):
            MIS.append(frozenset(U))
assert len(MIS) == 15

# eval is monotone in U, so requiring truth on the minimal required-true points implies it on
# all 100.  outVars is forced empty: every vertex lies in some maximal independent set, where
# eval must be false, so no vertex can sit in outVars.
ALLT = sorted(set(tuple(sorted(I | {w})) for I in MIS for w in range(N) if w not in I))
TRUE_PTS = [u for u in ALLT if not any(set(o) != set(u) and set(o) <= set(u) for o in ALLT)]
FALSE_PTS = sorted(set(tuple(sorted(I)) for I in MIS))
assert len(ALLT) == 100 and len(TRUE_PTS) == 70 and len(FALSE_PTS) == 15

SIZE = int(sys.argv[1]); READ = int(sys.argv[2]); MODE = sys.argv[3]
SOLVER = sys.argv[4] if len(sys.argv) > 4 else "cd195"
TAG = sys.argv[5] if len(sys.argv) > 5 else f"{SIZE}_{READ}_{MODE}"

from pysat.formula import IDPool, CNF
from pysat.card import CardEnc, EncType

p = IDPool(); cnf = CNF()
V = lambda *k: p.id(k)
add = lambda *c: cnf.append(list(c))
lv = lambda i, v: V('lv', i, v); rv = lambda i, v: V('rv', i, v)
lg = lambda i, j: V('lg', i, j); rg = lambda i, j: V('rg', i, j)
og = lambda i: V('og', i)
G = lambda u, i: V('G', u, i); LS = lambda u, i: V('LS', u, i); RS = lambda u, i: V('RS', u, i)

# clause (c): for each v, #{ i : v in leftVars i or v in rightVars i } <= READ
for v in range(N):
    ds = []
    for i in range(SIZE):
        d = V('d', i, v); ds.append(d)
        add(-lv(i, v), d); add(-rv(i, v), d); add(-d, lv(i, v), rv(i, v))
    cnf.extend(CardEnc.atmost(lits=ds, bound=READ, vpool=p,
                              encoding=EncType.seqcounter).clauses)

# sideTrue / gateValFuel / eval, point by point.  WellFormed is built in: a side of gate i may
# only name gates j < i, which is exactly what sideTrue would read anyway.
for u in FALSE_PTS + TRUE_PTS:
    U = set(u)
    for i in range(SIZE):
        add(-G(u, i), LS(u, i)); add(-G(u, i), RS(u, i)); add(G(u, i), -LS(u, i), -RS(u, i))
        for (Sv, vs, gs, tag) in ((LS, lv, lg, 'al'), (RS, rv, rg, 'ar')):
            lits = [vs(i, v) for v in sorted(U)]
            for j in range(i):
                a = V(tag, u, i, j); lits.append(a)
                add(-a, gs(i, j)); add(-a, G(u, j)); add(a, -gs(i, j), -G(u, j))
            add(-Sv(u, i), *lits)
            for l in lits:
                add(-l, Sv(u, i))

for u in FALSE_PTS:                               # eval U = false
    for i in range(SIZE):
        add(-og(i), -G(u, i))
for u in TRUE_PTS:                                # eval U = true
    lits = []
    for i in range(SIZE):
        b = V('b', u, i); lits.append(b); add(-b, og(i)); add(-b, G(u, i))
    add(*lits)

if MODE == "tight":
    for i in range(SIZE):
        # S1: every gate is reachable from the output.  An unreachable gate can be deleted,
        #     giving a circuit of smaller size, which the smaller runs cover.
        add(og(i), *[lg(k, i) for k in range(i + 1, SIZE)],
                   *[rg(k, i) for k in range(i + 1, SIZE)])
        # S2: no side is identically false.  Such a gate is constant false; delete it.
        add(*[lv(i, v) for v in range(N)], *[lg(i, j) for j in range(i)])
        add(*[rv(i, v) for v in range(N)], *[rg(i, j) for j in range(i)])
        # S3: the two sides of a gate may be exchanged with no effect on the gate value, on
        #     WellFormed or on clause (c); fix left <=lex right.
        xs = [lv(i, v) for v in range(N)] + [lg(i, j) for j in range(i)]
        ys = [rv(i, v) for v in range(N)] + [rg(i, j) for j in range(i)]
        eq = None
        for t in range(len(xs)):
            if eq is None:
                add(-xs[t], ys[t])
            else:
                add(-eq, -xs[t], ys[t])
            ne = V('lexeq', i, t)
            add(-ne, -xs[t], ys[t]); add(-ne, xs[t], -ys[t])
            if eq is not None:
                add(-ne, eq)
            eq = ne

print(f"SIZE={SIZE} READ={READ} {MODE} solver={SOLVER} pts={len(FALSE_PTS)+len(TRUE_PTS)} "
      f"vars={p.top} clauses={len(cnf.clauses)}", flush=True)

import pysat.solvers as PS
MK = {"cd195": PS.Cadical195, "cd153": PS.Cadical153, "g4": PS.Glucose4,
      "mcm": PS.MapleCM, "mpl": PS.Maplesat, "lgl": PS.Lingeling, "m22": PS.Minisat22}
S = MK[SOLVER](bootstrap_with=cnf)

t0 = time.time(); budget = 200000; total = 0; res = None
while True:
    S.conf_budget(budget)
    res = S.solve_limited(expect_interrupt=False)
    total += budget
    if res is not None:
        break
    print(f"  ... no result after ~{total} conflicts, {time.time()-t0:.0f}s (STILL RUNNING, "
          f"not UNSAT)", flush=True)
    budget = min(budget * 2, 4000000)

el = time.time() - t0
print(f"RESULT SIZE={SIZE} READ={READ} {MODE}: {'SAT' if res else 'UNSAT'} "
      f"after {total} conflicts, {el:.1f}s", flush=True)
if res:
    m = set(l for l in S.get_model() if l > 0)
    sol = {"size": SIZE,
           "leftVars":  [[v for v in range(N) if lv(i, v) in m] for i in range(SIZE)],
           "leftGates": [[j for j in range(i) if lg(i, j) in m] for i in range(SIZE)],
           "rightVars": [[v for v in range(N) if rv(i, v) in m] for i in range(SIZE)],
           "rightGates":[[j for j in range(i) if rg(i, j) in m] for i in range(SIZE)],
           "outVars": [], "outGates": [i for i in range(SIZE) if og(i) in m]}
    print(json.dumps(sol), flush=True)
    with open(os.path.join(OUT, f"sol_{TAG}.json"), "w") as f:
        json.dump(sol, f)
S.delete()
