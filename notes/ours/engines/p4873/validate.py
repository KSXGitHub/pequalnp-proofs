#!/usr/bin/env python3
"""Brute-force minimum Monotone2 size, over the FULL loose model, for small n.

This is the third, solver-free check of synth.py.  It searches the model exactly as
`PEqualNP.MetaComplexity.Monotone2` permits it:

  * op in {and, or};
  * inputs.length <= 2, so fan-in 0 (and [] = true, or [] = false), fan-in 1 (a copy)
    and two equal operands are all allowed;
  * a read of a wire that does not exist yet returns false, so an out-of-range operand is
    modelled by an extra pseudo-wire whose column is constant false;
  * the output wire may be any wire at all, not only the last gate.

The search is a breadth-first sweep over the SET of wire columns available, which is sound
because what a next gate can produce depends only on that set (wire indices matter only
through which columns are readable).  Each level adds one gate.  `min_size[f]` is then the
least number of gates of any loose-model circuit computing `f`, with no normal-form
assumption of any kind -- so it can be compared against synth.py's sweep.
"""

from __future__ import annotations

import argparse
import itertools
import sys
from typing import Dict, FrozenSet, List, Optional, Sequence, Set


def columns_for_inputs(n: int) -> List[int]:
    """Column of input i: bit k set iff input i is 1 on row k."""
    nrows = 1 << n
    cols: List[int] = []
    for i in range(n):
        c = 0
        for k in range(nrows):
            if (k >> i) & 1:
                c |= 1 << k
        cols.append(c)
    return cols


def brute_min_sizes(
    n: int, max_gates: int, verbose: bool = False, model: str = "mono"
) -> Dict[int, int]:
    nrows = 1 << n
    full = (1 << nrows) - 1
    const_false = 0
    const_true = full

    inputs = columns_for_inputs(n)
    start: FrozenSet[int] = frozenset(inputs)

    min_size: Dict[int, int] = {}
    for c in inputs:
        min_size[c] = 0  # computed by an input wire, no gates

    frontier: Set[FrozenSet[int]] = {start}
    for depth in range(1, max_gates + 1):
        nxt: Set[FrozenSet[int]] = set()
        for state in frontier:
            # an operand may be any available column, or the constant false of a
            # nonexistent wire
            operands = list(state) + [const_false]
            new_cols: Set[int] = set()
            # fan-in 0
            new_cols.add(const_true)  # and []
            new_cols.add(const_false)  # or  []
            # fan-in 1: a copy of the operand (and [a] = or [a] = a)
            for a in operands:
                new_cols.add(a)
            # fan-in 2, repetitions allowed
            for a, b in itertools.combinations_with_replacement(operands, 2):
                new_cols.add(a & b)
                new_cols.add(a | b)
            if model == "ao2":
                # NOT: fan-in 0 is the constant true, fan-in 1 or 2 negates the first wire
                for a in operands:
                    new_cols.add(full ^ a)
            for c in new_cols:
                if c not in min_size:
                    min_size[c] = depth
                nxt.add(state | {c})
        frontier = nxt
        if verbose:
            print(
                f"  depth {depth}: {len(frontier)} states, {len(min_size)} functions known",
                file=sys.stderr,
                flush=True,
            )
    return min_size


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--max-gates", type=int, required=True)
    ap.add_argument("--table", type=str, default="", help="report one function only")
    ap.add_argument("--verbose", action="store_true")
    ap.add_argument("--model", choices=("mono", "ao2"), default="mono")
    args = ap.parse_args(argv)

    ms = brute_min_sizes(args.n, args.max_gates, args.verbose, args.model)
    if args.table:
        t = int(args.table, 0)
        got = ms.get(t)
        print(
            f"n={args.n} table=0x{t:x} min_loose_Monotone2_size="
            + (str(got) if got is not None else f"> {args.max_gates}")
        )
        return 0
    by_size: Dict[int, int] = {}
    for _f, s in ms.items():
        by_size[s] = by_size.get(s, 0) + 1
    print(f"n={args.n} up to {args.max_gates} gates: functions reachable by size")
    for s in sorted(by_size):
        print(f"  size {s}: {by_size[s]} functions")
    print(f"  total {len(ms)}")
    # print the full table so another tool can diff it
    for f in sorted(ms):
        print(f"FUN 0x{f:0{1 << args.n // 4 or 1}x} {ms[f]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
