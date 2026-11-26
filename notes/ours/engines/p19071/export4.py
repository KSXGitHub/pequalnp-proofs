#!/usr/bin/env python3
"""Export every reachable set of 4 added columns (depth-4 states) as raw uint16."""
import struct, sys
M = 0xFFFF
INPUTS = tuple([0xF << (4*u) for u in range(4)] + [0x1111 << v for v in range(4)])

def cands(avail):
    out = set()
    k = len(avail)
    for i in range(k):
        a = avail[i]
        out.add(~a & M)
        for j in range(i+1, k):
            b = avail[j]
            out.add(a & b); out.add(a | b)
    out.discard(0)
    return out - set(avail)

depth = int(sys.argv[1]); path = sys.argv[2]
level = {frozenset()}
for d in range(1, depth+1):
    nxt = set()
    for st in level:
        avail = INPUTS + tuple(sorted(st))
        for c in cands(avail):
            nxt.add(st | {c})
    level = nxt
    print(f"depth {d}: {len(level)} states", flush=True)
with open(path, "wb") as fh:
    for st in level:
        fh.write(struct.pack("<%dH" % depth, *sorted(st)))
print(f"wrote {len(level)} states of {depth} columns to {path}")
