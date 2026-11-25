#!/usr/bin/env python3
"""Does an induced four-vertex path force repSize above 9?

The read budget in table1a.py says a minimal circuit of size 9 is a READ-ONCE
formula: 18 read slots, 8 non-output gates and 10 input wires each read exactly
once.  So "repSize A = 9" means "A has a read-once AND/OR formula", and a bound
that rules size 9 out is a bound on read-once formulas.  This script tests the
desk's hint that an induced four-vertex path is such an obstruction, by sampling
masks, counting their induced P4s (a 2-by-2 submatrix with exactly three ones,
i.e. an induced path on two left and two right vertices) and asking the tool
whether 9 gates suffice.

usage: python3 p4check.py <count> [seed]
"""

from __future__ import annotations

import itertools
import random
import sys

from table1a import NL, NR, must_read_inputs, solve_size, table, zero_gate_witness


def p4_count(mask: int) -> int:
    a = table(mask)
    n = 0
    for u1, u2 in itertools.combinations(range(NL), 2):
        for v1, v2 in itertools.combinations(range(NR), 2):
            if a[u1][v1] + a[u1][v2] + a[u2][v1] + a[u2][v2] == 3:
                n += 1
    return n


def least_size(mask: int, cap: int) -> int | None:
    """The exact least size if it is at most `cap`, else None."""
    if zero_gate_witness(mask) is not None:
        return 0
    for ng in range(1, cap + 1):
        got, _ = solve_size(mask, ng, True, True, "cadical153")
        if got is not None:
            return ng
    return None


def main() -> int:
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    rng = random.Random(seed)
    buckets: dict[tuple[bool, object], int] = {}
    counterexamples: list[tuple[int, int, int]] = []
    seen: set[int] = set()
    while len(seen) < count:
        mask = rng.getrandbits(NL * NR)
        if mask in seen:
            continue
        if not all(must_read_inputs(mask)):
            continue  # the read budget then allows sizes below 9; keep the sample uniform
        seen.add(mask)
        p4 = p4_count(mask)
        m = least_size(mask, 9)
        sys.stderr.write(f"  mask {mask}: {p4} induced P4s, least size {m if m is not None else '>9'}\n")
        sys.stderr.flush()
        key: tuple[bool, object] = (p4 > 0, m if m is not None else ">9")
        buckets[key] = buckets.get(key, 0) + 1
        if p4 > 0 and m is not None:
            counterexamples.append((mask, p4, m))
    sys.stdout.write(f"{len(seen)} masks sampled with seed {seed}\n")
    sys.stdout.write("(has an induced P4, least size)  ->  how many\n")
    for key in sorted(buckets, key=str):
        sys.stdout.write(f"  {key}  ->  {buckets[key]}\n")
    if counterexamples:
        sys.stdout.write(f"\nCOUNTEREXAMPLES to 'an induced P4 forces size >= 10': {len(counterexamples)}\n")
        for mask, p4, m in counterexamples[:10]:
            sys.stdout.write(f"  mask {mask}: {p4} induced P4s, least size {m}\n")
    else:
        sys.stdout.write("\nno mask in the sample has an induced P4 and a circuit of 9 gates\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
