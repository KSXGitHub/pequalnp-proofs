"""Independent check of a found circuit: plain evaluation, no bitmasks.

The annealer's own cost is computed with 1024-bit integer ops. This re-evaluates
the circuit row by row with ordinary booleans, so a bug in the mask arithmetic
cannot certify its own output.

usage: verify.py <gates>
"""

import itertools
import json
import pathlib
import sys

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
n = int(sys.argv[1])
c = json.load(open(D / f"circuit_{n}.json"))
gates = [(o, list(i)) for o, i in c["gates"]]
out = c["output"]


def ev(x: list[bool]) -> bool:
    w = list(x)
    for op, ins in gates:
        v = [w[i] if i < len(w) else False for i in ins]
        if op == "not":
            w.append(not v[0])
        elif op == "and":
            w.append(all(v))
        else:
            w.append(any(v))
    return w[out] if out < len(w) else False


bad = [x for x in itertools.product([False, True], repeat=NI) if ev(list(x)) != any(x[a] and x[b] for a, b in E)]
print(f"size={len(gates)} output=wire {out}")
print(f"rows checked={2**NI}  mismatches={len(bad)}")
ops = sorted({o for o, _ in gates})
print(f"ops used: {ops}")
for j, (o, ins) in enumerate(gates):
    assert o in ("and", "or", "not"), o
    assert len(ins) <= 2, (j, ins)  # FanInTwo
    assert all(i < NI + j for i in ins), (j, ins)  # reads back
print("structure OK: FanInTwo (ops in {and,or,not}, <=2 inputs), every gate reads back")
print("VERIFIED" if not bad else f"WRONG on {len(bad)} rows, e.g. {bad[0]}")
