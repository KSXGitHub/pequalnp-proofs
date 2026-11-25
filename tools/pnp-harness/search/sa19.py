"""Hunt for a 19-gate AND/OR/NOT circuit for the Petersen edge function.

L-meta-651's sketch: "A circuit with 19 gates refutes it and is as welcome as a
proof. Known: a circuit with 20 gates exists", and their own attempt ran each of
five cases for ten minutes and decided none. Reduction slots are full across the
whole family (three merged each on 651, 2371, 2373, 2375), so a refutation is the
only route left in. The star bound is 15 + 6 - 1 = 20 and Petersen is C4-free, so
every two-level circuit costs at least 20; a 19-gate circuit must be genuinely
non-two-level.

BITMASK TRUTH TABLES. A first version held each wire as a list of 1024 bools and
managed only 155k iterations in 100 s - and at 20 gates, where a solution is KNOWN
to exist, it got no closer than 40 wrong rows. That calibration failure made any
19-gate negative result worthless, so the representation changed: each wire is one
1024-bit Python int, and a gate is a single & , | or ~. Cost is then one popcount
of the xor against the target.

FanInTwo allows and, or AND not with inputs.length <= 2, so NOT is in the basis.
The monotonicity row reduction therefore does NOT apply - a circuit containing NOT
need not be monotone even when the function it computes is - and all 1024 rows are
carried, which costs nothing once they are a single integer.

usage: sa19.py <gates> <seconds> <seed>
"""

import itertools
import json
import pathlib
import random
import sys
import time

D = pathlib.Path(__file__).resolve().parent
NI = 10
E = [
    (0, 1),
    (0, 4),
    (0, 5),
    (1, 2),
    (1, 6),
    (2, 3),
    (2, 7),
    (3, 4),
    (3, 8),
    (4, 9),
    (5, 7),
    (5, 8),
    (6, 8),
    (6, 9),
    (7, 9),
]
ROWS = list(itertools.product([False, True], repeat=NI))
R = len(ROWS)
FULL = (1 << R) - 1


def mask(bits: list[bool]) -> int:
    m = 0
    for i, b in enumerate(bits):
        if b:
            m |= 1 << i
    return m


COL = [mask([r[i] for r in ROWS]) for i in range(NI)]
TARGET = mask([any(r[a] and r[b] for a, b in E) for r in ROWS])

NG = int(sys.argv[1])
SECS = float(sys.argv[2])
SEED = int(sys.argv[3])
rnd = random.Random(SEED)
AND, OR, NOT = 0, 1, 2


def rand_gate(j: int) -> list[int]:
    hi = NI + j
    return [rnd.choice((AND, OR, NOT)), rnd.randrange(hi), rnd.randrange(hi)]


def out_mask(gs: list[list[int]]) -> int:
    w = COL + [0] * NG
    for i, (op, a, b) in enumerate(gs):
        if op == NOT:
            w[NI + i] = ~w[a] & FULL
        elif op == AND:
            w[NI + i] = w[a] & w[b]
        else:
            w[NI + i] = w[a] | w[b]
    return w[NI + NG - 1]


def cost(gs: list[list[int]]) -> int:
    return (out_mask(gs) ^ TARGET).bit_count()


cur = [rand_gate(j) for j in range(NG)]
cc = cost(cur)
best = cc
bestg = [g[:] for g in cur]
t0 = time.time()
it = 0
while time.time() - t0 < SECS and best > 0:
    it += 1
    T = max(0.02, 1.5 * (1 - (time.time() - t0) / SECS))
    j = rnd.randrange(NG)
    old = cur[j][:]
    k = rnd.randrange(3)
    if k == 0:
        cur[j][0] = rnd.choice((AND, OR, NOT))
    else:
        cur[j][k] = rnd.randrange(NI + j)
    nc = cost(cur)
    if nc <= cc or rnd.random() < 2.718 ** (-(nc - cc) / T):
        cc = nc
    else:
        cur[j] = old
    if cc < best:
        best = cc
        bestg = [g[:] for g in cur]

el = time.time() - t0
line = f"gates={NG} seed={SEED} best_wrong_rows={best} iters={it} seconds={el:.0f}"
print(line, flush=True)
(D / f"SA_{NG}_{SEED}.txt").write_text(line + "\n")
if best == 0:
    nm = {AND: "and", OR: "or", NOT: "not"}
    gates = [[nm[o], ([a] if o == NOT else [a, b])] for o, a, b in bestg]
    json.dump({"gates": gates, "output": NI + NG - 1}, open(D / f"circuit_{NG}.json", "w"))
    for j, (o, ins) in enumerate(gates):
        print(f"  gate {j:2d} wire {NI + j:2d}: {o:3s} {ins}")
    print(f"SOLVED -> circuit_{NG}.json", flush=True)
