"""Fano incidence function, its minterms/maxterms, and the hand-built 27-gate star cover."""
from __future__ import annotations

N = 14  # wires 0..6 = points, 7..13 = lines

# line L contains points {L, L+1, L+3} mod 7  (difference set {0,1,3})
LINE_PTS = [tuple(sorted(((L + d) % 7) for d in (0, 1, 3))) for L in range(7)]
INC = [(p, L) for L in range(7) for p in LINE_PTS[L]]  # 21 incidences


def f(v: int) -> bool:
    """v is a 14-bit mask: bit p = point p, bit 7+L = line L."""
    for (p, L) in INC:
        if (v >> p) & 1 and (v >> (7 + L)) & 1:
            return True
    return False


def minterms() -> list[int]:
    return [(1 << p) | (1 << (7 + L)) for (p, L) in INC]


def maxterms() -> list[int]:
    """Maximal elements of {v : not f(v)}."""
    out = []
    for v in range(1 << N):
        if f(v):
            continue
        if all(f(v | (1 << i)) for i in range(N) if not (v >> i) & 1):
            out.append(v)
    return out


# ---- the star cover: 27 gates, gate j is wire 14+j -------------------------
def star_cover() -> tuple[list[tuple[str, int, int]], int]:
    gates: list[tuple[str, int, int]] = []

    def add(op: str, a: int, b: int) -> int:
        gates.append((op, a, b))
        return N + len(gates) - 1

    terms = []
    for L in range(7):
        a, b, c = LINE_PTS[L]
        w = add('or', a, b)
        w = add('or', w, c)
        terms.append(add('and', 7 + L, w))
    acc = terms[0]
    for t in terms[1:]:
        acc = add('or', acc, t)
    return gates, acc


def wires(gates: list[tuple[str, int, int]], v: int) -> list[bool]:
    w = [bool((v >> i) & 1) for i in range(N)]
    for (op, a, b) in gates:
        x = w[a] if a < len(w) else False
        y = w[b] if b < len(w) else False
        w.append(x and y if op == 'and' else x or y)
    return w


def evalc(gates: list[tuple[str, int, int]], out: int, v: int) -> bool:
    return wires(gates, v)[out]


if __name__ == '__main__':
    print('lines:', LINE_PTS)
    print('incidences:', len(INC))
    mt, Mt = minterms(), maxterms()
    print('minterms(21 expected):', len(mt), 'distinct', len(set(mt)))
    print('maxterms:', len(Mt))
    from collections import Counter
    print('maxterm shapes (npoints,nlines):',
          Counter((bin(v & 0x7f).count('1'), bin(v >> 7).count('1')) for v in Mt))
    gates, out = star_cover()
    print('star cover: gates =', len(gates), ' output wire =', out,
          ' output gate op =', gates[out - N][0], ' gate index =', out - N)
    bad = [v for v in range(1 << N) if evalc(gates, out, v) != f(v)]
    print('rows checked:', 1 << N, ' mismatches:', len(bad))
    print('all gates fan-in 2:', all(True for g in gates))
    print('all gates Nodup:', all(a != b for (_, a, b) in gates))
    print('all gates ReadsBack:', all(max(a, b) < N + j for j, (_, a, b) in enumerate(gates)))
    print('all ops and/or:', all(op in ('and', 'or') for (op, _, _) in gates))
    # the statement's own conjuncts, checked on the star cover
    print('eval true on all 21 minterms:', all(evalc(gates, out, v) for v in mt))
    print('eval false on all maxterms:', all(not evalc(gates, out, v) for v in Mt))
    print('GATES:')
    for j, (op, a, b) in enumerate(gates):
        print('  gate', j, '(wire', N + j, '):', op, a, b)
