# L-meta-909, hunt + controls over the "star outputs plus literal buffers" design.
#
# Background facts this job rests on, each proved/checked elsewhere in this session:
#  * eval is monotone, so clause (d) reduces to: false on the 15 maximal independent sets,
#    true on the 70 minimal points T u {p} with T a size-3 maximal independent set.
#  * A gate false on every maximal independent set whose two side-functions are ORs of vertex
#    sets must have those two sets disjoint and completely joined, and Petersen has girth 5,
#    so one of them is a singleton: the gate is a star ({t}, S) with S inside N(t).
#  * A gate with leftVars = rightVars = X has value "X meets U", an OR of variables, at a cost
#    of one gate and ONE read per element of X; later sides may OR it in for free.  Call it a
#    buffer.  A buffer for a single vertex v is a free copy of the literal v.
#
# The design searched here: |C| star output gates ({t}, S_t) for t in C, plus one buffer gate
# per vertex of B.  Every occurrence of a vertex of B inside a side is served by its buffer and
# so is free; occurrences of other vertices are bare and cost a read in that gate.
#
# usage: x.sh p909star MAXGATES
import itertools, json, sys

EDGES = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
         (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
N = 10
adj = lambda a, b: a != b and ((a, b) in EDGES or (b, a) in EDGES)
NBR = [frozenset(w for w in range(N) if adj(v, w)) for v in range(N)]

MIS = []
for r in range(N + 1):
    for S in itertools.combinations(range(N), r):
        U = set(S)
        if all(not adj(a, c) for a in U for c in U) and \
           all(w in U or any(adj(a, w) for a in U) for w in range(N)):
            MIS.append(frozenset(U))
ALLT = sorted(set(tuple(sorted(I | {w})) for I in MIS for w in range(N) if w not in I))
PTS = [frozenset(u) for u in ALLT
       if not any(set(o) != set(u) and set(o) <= set(u) for o in ALLT)]
assert len(MIS) == 15 and len(PTS) == 70

MAXG = int(sys.argv[1]) if len(sys.argv) > 1 else 6

# (A) how few star output gates cover the 70 points, with NO read bound at all?  Each gate
#     ({t}, N(t)) covers the points containing an edge at t, so this is a hitting-set question
#     and its answer is a lower bound on the number of output gates in this design.
best = None
for k in range(1, 8):
    found = []
    for C in itertools.combinations(range(N), k):
        Cs = set(C)
        if all(any(t in P and (NBR[t] & P) for t in Cs) for P in PTS):
            found.append(C)
    if found:
        best = (k, found)
        break
print(f"(A) fewest star output gates ignoring reads: {best[0]}  "
      f"({len(best[1])} such centre sets, e.g. {best[1][0]})", flush=True)
iscover = [sorted(c) for c in best[1]
           if all(a in set(c) or b in set(c) for (a, b) in EDGES)]
print(f"    of those, {len(iscover)} are vertex covers", flush=True)

# (B) the design search: choose C (centres), S_t inside N(t), B (buffered vertices), and for
#     each occurrence decide bare-or-buffered.  A vertex of B has every occurrence free, so the
#     read count is 1 (its own buffer); a vertex outside B pays one read per gate it occurs in.
def reads_ok(C, S, B):
    for v in range(N):
        if v in B:
            r = 1                                   # its buffer gate only
        else:
            r = sum(1 for t in C if v == t or v in S[t])
        if r > 2:
            return False
    return True

def covers(C, S):
    return all(any(t in P and (S[t] & P) for t in C) for P in PTS)

sols = []
for nc in range(1, MAXG + 1):
    for C in itertools.combinations(range(N), nc):
        # S_t nonempty subset of N(t)
        for combo in itertools.product(*[[frozenset(s) for r in (1, 2, 3)
                                          for s in itertools.combinations(sorted(NBR[t]), r)]
                                         for t in C]):
            S = dict(zip(C, combo))
            if not covers(C, S):
                continue
            occ = set(C) | set().union(*combo)
            for nb in range(0, MAXG - nc + 1):
                for B in itertools.combinations(sorted(occ), nb):
                    if nc + nb > MAXG:
                        continue
                    if reads_ok(C, S, set(B)):
                        sols.append((nc + nb, sorted(C),
                                     [[t, sorted(S[t])] for t in C], sorted(B)))
                        break
                else:
                    continue
                break
    if sols:
        break
if not sols:
    print(f"(B) no circuit of this design shape with at most {MAXG} gates", flush=True)
else:
    sols.sort()
    print(f"(B) smallest in this design: {sols[0][0]} gates", flush=True)
    for s in sols[:5]:
        print("   ", s, flush=True)
    with open("/tmp/claude-0/-home-user-pequalnp-proofs/731ccd8c-0494-56c8-b77c-6e2443ae238b"
              "/scratchpad/p909/stardesign.json", "w") as f:
        json.dump({"gates": sols[0][0], "C": sols[0][1],
                   "S": sols[0][2], "B": sols[0][3]}, f)
