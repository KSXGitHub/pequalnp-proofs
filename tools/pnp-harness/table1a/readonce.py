#!/usr/bin/env python3
"""Can a 9-gate circuit's table contain an induced four-vertex path?

table1a.py's read budget shows that a minimal circuit of 9 gates is exactly a
READ-ONCE AND/OR formula over the 10 one-hot wires (18 read slots; the 8
non-output gates and the 10 input wires each need one, so each is read exactly
once and nothing is shared).  This samples such formulas directly -- no solver --
evaluates them at the 25 points oneEach u v, and counts the induced P4s of the
table they produce (a 2-by-2 submatrix with exactly three ones).  If no sampled
read-once formula ever yields a table with an induced P4, then "A contains an
induced P4" rules out 9 gates, which with the read budget gives repSize A >= 10.

usage: python3 readonce.py <samples> [seed]
"""

from __future__ import annotations

import itertools
import random
import sys

from table1a import must_read_inputs

NL = 5
NR = 5
PTS = [(u, v) for u in range(NL) for v in range(NR)]
# Each wire's value over the 25 points, as a 25-bit set: wires 0..4 are the rows,
# 5..9 the columns.
GEN = [sum(1 << p for p, (u, v) in enumerate(PTS) if (w == u if w < NL else w - NL == v)) for w in range(NL + NR)]
FULL = (1 << len(PTS)) - 1


def random_read_once(rng: random.Random) -> tuple[int, str]:
    """A random read-once formula over the 10 wires: its 25-point set and its text."""
    pool = [(GEN[w], ("x" if w < NL else "y") + str(w % NL)) for w in range(NL + NR)]
    rng.shuffle(pool)
    while len(pool) > 1:
        i = rng.randrange(len(pool))
        a = pool.pop(i)
        j = rng.randrange(len(pool))
        b = pool.pop(j)
        if rng.random() < 0.5:
            pool.append((a[0] | b[0], f"({a[1]}+{b[1]})"))
        else:
            pool.append((a[0] & b[0], f"({a[1]}*{b[1]})"))
    return pool[0]


def p4_count(bits: int) -> int:
    def at(u: int, v: int) -> int:
        return (bits >> (NR * u + v)) & 1

    n = 0
    for u1, u2 in itertools.combinations(range(NL), 2):
        for v1, v2 in itertools.combinations(range(NR), 2):
            if at(u1, v1) + at(u1, v2) + at(u2, v1) + at(u2, v2) == 3:
                n += 1
    return n


def p4_list(bits: int) -> list[tuple[int, int, int, int]]:
    def at(u: int, v: int) -> int:
        return (bits >> (NR * u + v)) & 1

    out: list[tuple[int, int, int, int]] = []
    for u1, u2 in itertools.combinations(range(NL), 2):
        for v1, v2 in itertools.combinations(range(NR), 2):
            if at(u1, v1) + at(u1, v2) + at(u2, v1) + at(u2, v2) == 3:
                out.append((u1, u2, v1, v2))
    return out


def max_disjoint_p4(bits: int) -> int:
    """The largest set of induced P4s of the table sharing no vertex."""
    ps = p4_list(bits)
    best = 0
    for k in range(min(2, len(ps)), 0, -1):
        for sel in itertools.combinations(ps, k):
            left = [x for q in sel for x in q[:2]]
            right = [x for q in sel for x in q[2:]]
            if len(set(left)) == len(left) and len(set(right)) == len(right):
                best = k
                break
        if best:
            break
    return best


def main() -> int:
    samples = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    rng = random.Random(seed)
    tables: set[int] = set()
    with_p4: list[tuple[int, str]] = []
    const = 0
    for _ in range(samples):
        bits, text = random_read_once(rng)
        if bits in (0, FULL):
            const += 1
            continue
        if not all(must_read_inputs(bits)):
            continue  # then the read budget allows fewer than 9 gates, so 9 is not least
        tables.add(bits)
        if p4_count(bits) > 0:
            with_p4.append((bits, text))
    sys.stdout.write(
        f"{samples} random read-once formulas, {const} constant on the 25 points, "
        f"{len(tables)} distinct tables whose least size is EXACTLY 9\n"
    )
    if with_p4:
        sys.stdout.write(
            f"FOUND {len(with_p4)} read-once formulas whose table has an induced P4, "
            f"so an induced P4 does NOT rule out 9 gates:\n"
        )
        for bits, text in with_p4[:5]:
            sys.stdout.write(f"  mask {bits}  {text}\n")
    else:
        sys.stdout.write(
            "no sampled read-once formula has an induced P4 in its table: an induced "
            "P4 rules out 9 gates, so with the read budget repSize >= 10\n"
        )
    dist: dict[int, int] = {}
    ddist: dict[int, int] = {}
    rich: list[int] = []
    for bits in tables:
        n = p4_count(bits)
        dist[n] = dist.get(n, 0) + 1
        d = max_disjoint_p4(bits)
        ddist[d] = ddist.get(d, 0) + 1
        if d >= 2:
            rich.append(bits)
    sys.stdout.write(
        f"\ninduced-P4 count over the {len(tables)} distinct 9-gate tables: "
        f"max {max(dist)}, histogram {dict(sorted(dist.items()))}\n"
    )
    sys.stdout.write(f"largest set of VERTEX-DISJOINT induced P4s: histogram {dict(sorted(ddist.items()))}\n")
    if rich:
        sys.stdout.write(f"{len(rich)} of them hold two vertex-disjoint induced P4s, e.g. {rich[:5]}\n")
    else:
        sys.stdout.write(
            "NONE of them holds two vertex-disjoint induced P4s: two disjoint induced "
            "P4s rule out 9 gates, so with the read budget repSize >= 10\n"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
