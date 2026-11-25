#!/usr/bin/env python3
"""Independent checker for a Table 1a circuit.  Shares no code with table1a.py.

A SAT model satisfies MY clauses, which is only as good as my transcription of
the Lean definitions.  So everything below is a fresh re-implementation, written
straight off the source, of

  lean/PEqualNP/Defs/CircuitLowerBounds.lean
      GateOp.eval and l = l.all id          -- `true` on the empty list
      GateOp.eval or  l = l.any id          -- `false` on the empty list
      Circuit.wires C x =
          C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
      Circuit.eval  C x = (C.wires x).getD C.output false
      Circuit.size  C   = C.gates.length
  lean/PEqualNP/Defs/MetaComplexityLgpMono.lean
      Monotone2 C = forall g in C.gates, g.op in {and, or} and g.inputs.length <= 2
  lean/PEqualNP/Defs/Represents.lean
      oneEach u v = List.ofFn (fun i : Fin n => decide (i = u))
                 ++ List.ofFn (fun j : Fin m => decide (j = v))
      Represents A C = forall u v, C.eval (oneEach u v) = A u v
      RepSizeAtMost A s = exists C, Monotone2 C and C.size <= s and Represents A C

The table is A u v = (<mask> : Nat).testBit (5 * u.val + v.val), decoded here from
the mask's binary digit string rather than by shifting, as a second opinion on the
bit order.

usage:
    python3 verify.py --mask 7874358 --circuit prefix_10.json --budget 10

Exit status 0 and the line VERIFY_OK mean: the circuit is Monotone2, has at most
`budget` gates, and agrees with A at all 25 points oneEach u v.
"""

from __future__ import annotations

import argparse
import itertools
import json
import pathlib
import sys
from typing import Any, Final

LEFT: Final = 5
RIGHT: Final = 5


def adjacency(mask: int) -> list[list[bool]]:
    """A u v = mask.testBit (5*u+v), read off the binary digits, lsb first."""
    if mask < 0:
        raise ValueError("mask must be a natural number")
    digits = format(mask, "b")[::-1]  # digits[k] is bit k
    bits = [d == "1" for d in digits] + [False] * (LEFT * RIGHT)
    return [[bits[LEFT * u + v] for v in range(RIGHT)] for u in range(LEFT)]


def one_each(u: int, v: int) -> list[bool]:
    """The 10-bit input with exactly left vertex u and right vertex v on."""
    out: list[bool] = []
    for i in range(LEFT):
        out.append(i == u)
    for j in range(RIGHT):
        out.append(j == v)
    return out


def gate_value(opname: str, read: list[bool]) -> bool:
    if opname == "and":
        for b in read:
            if not b:
                return False
        return True
    if opname == "or":
        for b in read:
            if b:
                return True
        return False
    raise ValueError(f"gate op {opname!r} is not AND or OR, so Monotone2 fails")


def evaluate(gates: list[dict[str, Any]], output: int, x: list[bool]) -> bool:
    wires = list(x)
    for g in gates:
        read: list[bool] = []
        for idx in g["inputs"]:
            i = int(idx)
            read.append(wires[i] if 0 <= i < len(wires) else False)
        wires.append(gate_value(str(g["op"]), read))
    return wires[output] if 0 <= output < len(wires) else False


def main() -> int:
    ap = argparse.ArgumentParser(description="independently check a Table 1a circuit")
    ap.add_argument("--mask", type=int, required=True)
    ap.add_argument("--circuit", type=str, required=True)
    ap.add_argument("--budget", type=int, required=True)
    args = ap.parse_args()

    raw: dict[str, Any] = json.loads(pathlib.Path(args.circuit).read_text())
    gates: list[dict[str, Any]] = [dict(g) for g in raw["gates"]]
    output = int(raw["output"])
    mask: int = args.mask
    budget: int = args.budget
    if "mask" in raw and int(raw["mask"]) != mask:
        sys.stdout.write(f"MASK MISMATCH: file says {raw['mask']}, asked for {mask}\n")
        return 1

    a = adjacency(mask)
    sys.stdout.write(f"mask {mask} -> A (rows = left vertex u, cols = right vertex v):\n")
    for u in range(LEFT):
        sys.stdout.write("   " + " ".join(str(int(a[u][v])) for v in range(RIGHT)) + "\n")

    sys.stdout.write("circuit under test (input wires 0..4 = left, 5..9 = right):\n")
    for j, g in enumerate(gates):
        sys.stdout.write(f"   wire {LEFT + RIGHT + j} = {g['op']}{tuple(g['inputs'])}\n")
    sys.stdout.write(f"   output wire = {output}\n")

    mono = True
    for g in gates:
        if str(g["op"]) not in ("and", "or") or len(list(g["inputs"])) > 2:
            mono = False
    size = len(gates)
    sys.stdout.write(f"Monotone2: {mono}\n")
    sys.stdout.write(f"size {size} <= budget {budget}: {size <= budget}\n")

    # Every gate must read wires that exist when it runs, or it silently reads false.
    forward = [(j, i) for j, g in enumerate(gates) for i in (int(k) for k in g["inputs"]) if i >= LEFT + RIGHT + j]
    if forward:
        sys.stdout.write(f"note: reads of not-yet-existing wires (read as false): {forward}\n")

    wrong: list[str] = []
    sys.stdout.write("the 25 constrained points oneEach u v:\n")
    for u in range(LEFT):
        row: list[str] = []
        for v in range(RIGHT):
            got = evaluate(gates, output, one_each(u, v))
            want = a[u][v]
            row.append(f"{int(got)}{'' if got == want else '<-WRONG'}")
            if got != want:
                wrong.append(f"oneEach {u} {v}: circuit {int(got)}, A {int(want)}")
        sys.stdout.write("   " + " ".join(f"{c:<8}" for c in row) + "\n")
    for w in wrong[:8]:
        sys.stdout.write(f"   {w}\n")
    sys.stdout.write(f"Represents: {not wrong}\n")

    # Informational: the definition constrains nothing off those 25 inputs.
    constrained = {tuple(one_each(u, v)) for u in range(LEFT) for v in range(RIGHT)}
    true_total = 0
    true_off = 0
    for bits in itertools.product([False, True], repeat=LEFT + RIGHT):
        if evaluate(gates, output, list(bits)):
            true_total += 1
            if bits not in constrained:
                true_off += 1
    sys.stdout.write(
        f"on all 1024 inputs the circuit is true {true_total} times, {true_off} of them "
        f"off the 25 constrained points (Represents asks nothing there)\n"
    )

    ok = mono and size <= budget and not wrong
    sys.stdout.write("VERIFY_OK\n" if ok else "VERIFY_FAIL\n")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
