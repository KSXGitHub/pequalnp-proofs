# INDEPENDENT re-simulation for L-meta-909.  Shares no code with the SAT translation.
#
# A direct, line-by-line transcription of lean/PEqualNP/Defs/AndCountCircuit.lean:
#   sideTrue U B F i val = (exists v in B, v in U) or (exists j in F, j < i and val j)
#   gateValFuel C U 0     = fun _ => false
#   gateValFuel C U (d+1) = fun i => sideTrue U (leftVars i) (leftGates i) i (gateValFuel C U d)
#                                 && sideTrue U (rightVars i)(rightGates i) i (gateValFuel C U d)
#   gateVal C U = gateValFuel C U C.size
#   eval C U    = (exists v in outVars, v in U) or (exists j in outGates, gateVal C U j)
#   WellFormed C = forall i, (forall j in leftGates i, j < i) and (forall j in rightGates i, j<i)
# and clause (c) counts GATE INDICES i with v in leftVars i or v in rightVars i.
#
# It rebuilds the graph from the posted edge list and re-derives the independent+dominating
# sets by brute force over all 1024 subsets, so nothing is taken on trust from the search.
#
# usage: x.sh p909verify <solution.json> [expected-read-bound]
import itertools, json, sys

EDGES = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
         (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
N = 10


def Adj(a, b):                       # SimpleGraph.fromRel (fun a b => (a,b) in edgeList)
    return a != b and ((a, b) in EDGES or (b, a) in EDGES)


def sideTrue(U, B, F, i, val):
    return any(v in U for v in B) or any((j < i) and val[j] for j in F)


def gateValFuel(C, U, d):
    if d == 0:
        return [False] * C["size"]
    prev = gateValFuel(C, U, d - 1)
    return [sideTrue(U, C["leftVars"][i], C["leftGates"][i], i, prev) and
            sideTrue(U, C["rightVars"][i], C["rightGates"][i], i, prev)
            for i in range(C["size"])]


def ev(C, U):
    g = gateValFuel(C, U, C["size"])
    return (any(v in U for v in C["outVars"]) or
            any(g[j] for j in C["outGates"]))


C = json.load(open(sys.argv[1]))
BOUND = int(sys.argv[2]) if len(sys.argv) > 2 else 2
ok = True

wf = all(all(j < i for j in C["leftGates"][i]) and all(j < i for j in C["rightGates"][i])
         for i in range(C["size"]))
print(f"(a) WellFormed              : {wf}")
ok &= wf
print(f"(b) size <= 6               : {C['size'] <= 6}   (size = {C['size']})")
ok &= C["size"] <= 6

rc = [sum(1 for i in range(C["size"])
          if v in C["leftVars"][i] or v in C["rightVars"][i]) for v in range(N)]
print(f"(c) read counts per vertex  : {rc}   max {max(rc)} <= {BOUND}: {max(rc) <= BOUND}")
ok &= max(rc) <= BOUND

nf = nt = 0
bad = []
for r in range(N + 1):
    for S in itertools.combinations(range(N), r):
        U = set(S)
        if not all(not Adj(a, c) for a in U for c in U):
            continue
        if not all(w in U or any(Adj(a, w) for a in U) for w in range(N)):
            continue
        nf += 1
        if ev(C, U) is not False:
            bad.append(("eval should be false at", sorted(U)))
        for w in range(N):
            if w in U:
                continue
            nt += 1
            if ev(C, U | {w}) is not True:
                bad.append(("eval should be true at", sorted(U | {w})))
print(f"(d) independent+dominating I: {nf} of them, {nt} one-vertex extensions; "
      f"violations: {len(bad)}")
for b in bad[:10]:
    print("     ", b)
ok &= not bad
print("INDEPENDENT RE-SIMULATION:", "ALL FOUR CLAUSES HOLD" if ok else "FAILED")
