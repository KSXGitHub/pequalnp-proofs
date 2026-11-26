#!/usr/bin/env python3
"""L-meta-19527 driver: does NOT buy a gate on the 5x5 promise graph mask 3187468?

Runs the (now n x m) engine $P/p19071/rep44.py through its own main(), so every
result here comes from exactly the code path that was validated on 4x4.

Batches (one short argument each, so the command shape stays fixed):

  regress   the three known 4x4 answers: mask 854 UNSAT at 6 and SAT at 7,
            masks 3824 and 9999 SAT at 6.  If these move, the generalisation is
            wrong and nothing it says about 5x5 means anything.
  control   MANDATORY POSITIVE CONTROL: the same code path must return SAT on
            mask 3187468 at 12 gates (loose), plus an independent hand-built
            12-gate monotone witness checked by rep44.simulate.
  hand      no solver at all: simulate the two hand-built circuits (12-gate
            monotone, 11-gate non-monotone) on all 25 promise rows.
  low7      exact sizes 1..7 on 5x5, tight (symmetry + distinct-cols).
  nine      exact sizes 8 and 9 on 5x5, tight.
  ten       the row itself: exact size 10, loose first (hunt a witness), then
            tight if loose does not return.
  tensat    exact size 10, loose, cadical --sat (witness hunt, tuned).
  tensat2   the same with --seed=12345 --walkreleff=1000, to diversify.
  tentight  exact size 10, tight, the full call cap (UNSAT attempt).
  eleven    exact size 11 on 5x5, loose (witness hunt) + the hand-built 11.
  twelve    exact size 12 on 5x5, loose (the positive control's size).

CALIBRATION LAW: hunt witnesses loose (--no-symmetry), prove UNSAT tight.
"""

from __future__ import annotations

import importlib.util
import io
import sys
import time
from contextlib import redirect_stdout
from dataclasses import dataclass
from pathlib import Path
from types import ModuleType
from typing import List, Optional, Sequence, Tuple

ENGINE = Path("/tmp/claude-0/-home-user-pequalnp-proofs/"
              "731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/pnp/p19071/rep44.py")
WORK = Path("/tmp/claude-0/-home-user-pequalnp-proofs/"
            "731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/p19527/cnf")

MASK = 3187468
N = 5
M = 5

# wall-clock guard for one batch: x.sh kills the job at 900 s by default
BATCH_BUDGET = 820.0
CALL_CAP = 600


def load_engine() -> ModuleType:
    spec = importlib.util.spec_from_file_location("rep44", ENGINE)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    # dataclasses resolves annotations through sys.modules, so register first
    sys.modules["rep44"] = mod
    spec.loader.exec_module(mod)
    return mod


@dataclass
class Outcome:
    label: str
    status: str          # SAT | UNSAT | TIMEOUT | ERROR
    seconds: float
    text: str


def run_case(eng: ModuleType, label: str, mask: int, n: int, m: int, gates: int,
             loose: bool, distinct: bool, timeout: int,
             solver_args: Sequence[str] = ()) -> Outcome:
    argv: List[str] = ["--mask", str(mask), "--n", str(n), "--m", str(m),
                       "--gates", str(gates), "--timeout", str(timeout),
                       "--work", str(WORK), "--tag", "_" + label]
    if loose:
        argv.append("--no-symmetry")
    if distinct:
        argv.append("--distinct-cols")
    for sa in solver_args:
        # "=" form: argparse refuses a value that begins with "--"
        argv.append("--solver-arg=" + sa)
    print(f"=== {label}: mask={mask} {n}x{m} gates={gates} "
          f"{'loose(--no-symmetry)' if loose else 'tight(symmetry)'}"
          f"{'+distinct-cols' if distinct else ''} "
          f"solver_args={list(solver_args)} timeout={timeout}s", flush=True)
    buf = io.StringIO()
    t0 = time.time()
    try:
        with redirect_stdout(buf):
            eng.main(argv)
    except SystemExit as exc:
        buf.write(f"\nSystemExit: {exc}\n")
    except Exception as exc:  # noqa: BLE001 - report, never swallow silently
        buf.write(f"\nEXCEPTION: {type(exc).__name__}: {exc}\n")
    dt = time.time() - t0
    text = buf.getvalue()
    print(text, flush=True)
    status = "ERROR"
    if "RESULT: UNSAT" in text:
        status = "UNSAT"
    elif "RESULT: SAT" in text:
        status = "SAT"
    elif "DID NOT RETURN" in text:
        status = "TIMEOUT"
    elif "DECODING BUG" in text:
        status = "DECODEBUG"
    print(f"--- {label}: {status} in {dt:.1f}s", flush=True)
    return Outcome(label, status, dt, text)


def hand_witness(eng: ModuleType) -> Tuple[bool, str]:
    """A 12-gate monotone circuit for mask 3187468, built by hand and checked by
    the engine's own Lean-faithful simulator.  Wires 0..4 = x0..x4 (left),
    5..9 = y0..y4 (right); gate j is wire 10 + j.

    Edges: (0,2) (0,3) (1,3) (1,4) (2,3) (3,0) (4,0) (4,1).
    Right-side cover: N(y0)={x3,x4}, N(y1)={x4}, N(y2)={x0},
    N(y3)={x0,x1,x2}, N(y4)={x1}."""
    G = eng.GateSpec
    gates = [
        G("or", [3, 4]),        # 10 = x3 | x4          (N(y0))
        G("and", [10, 5]),      # 11 = (x3|x4) & y0
        G("and", [4, 6]),       # 12 = x4 & y1
        G("and", [0, 7]),       # 13 = x0 & y2
        G("or", [0, 1]),        # 14 = x0 | x1
        G("or", [14, 2]),       # 15 = x0 | x1 | x2      (N(y3))
        G("and", [15, 8]),      # 16 = (x0|x1|x2) & y3
        G("and", [1, 9]),       # 17 = x1 & y4
        G("or", [11, 12]),      # 18
        G("or", [13, 16]),      # 19
        G("or", [17, 18]),      # 20
        G("or", [19, 20]),      # 21 = output
    ]
    _, rows = eng.mask_rows(MASK, N, M)
    out = 10 + len(gates) - 1
    bad = [(bits, want) for bits, want in rows
           if eng.simulate(gates, bits, out) != want]
    desc = (f"hand-built {len(gates)}-gate monotone circuit, output wire {out}\n"
            + "\n".join(f"  wire {10+j}: {g.op} {g.inputs}" for j, g in enumerate(gates))
            + "\nlean gates: " + eng.lean_gate_list(gates))
    if bad:
        return False, desc + f"\nMISMATCHED {len(bad)} rows: {bad[:4]}"
    return True, desc + f"\nchecked: agrees with the mask on all {len(rows)} oneEach rows"


def hand_witness11(eng: ModuleType) -> Tuple[bool, str]:
    """An 11-gate NON-monotone circuit for mask 3187468, built by hand: under the
    one-a-side promise exactly one x is set, so NOT(x3 | x4) = x0 | x1 | x2, and the
    wire x3|x4 is reused for the y0 biclique.  That is one gate under the 12-gate
    monotone biclique covers (the desk's monotone floor for this graph is 11)."""
    G = eng.GateSpec
    gates = [
        G("or", [3, 4]),        # 10 = x3 | x4
        G("not", [10]),         # 11 = x0 | x1 | x2    (promise only!)
        G("and", [11, 8]),      # 12 = (x0|x1|x2) & y3 -> edges (0,3) (1,3) (2,3)
        G("and", [10, 5]),      # 13 = (x3|x4) & y0    -> edges (3,0) (4,0)
        G("and", [0, 7]),       # 14 = x0 & y2         -> edge (0,2)
        G("and", [1, 9]),       # 15 = x1 & y4         -> edge (1,4)
        G("and", [4, 6]),       # 16 = x4 & y1         -> edge (4,1)
        G("or", [12, 13]),      # 17
        G("or", [14, 15]),      # 18
        G("or", [16, 17]),      # 19
        G("or", [18, 19]),      # 20 = output
    ]
    _, rows = eng.mask_rows(MASK, N, M)
    out = 10 + len(gates) - 1
    bad = [(bits, want) for bits, want in rows
           if eng.simulate(gates, bits, out) != want]
    desc = (f"hand-built {len(gates)}-gate NON-monotone circuit, output wire {out}\n"
            + "\n".join(f"  wire {10+j}: {g.op} {g.inputs}" for j, g in enumerate(gates))
            + "\nlean gates: " + eng.lean_gate_list(gates))
    if bad:
        return False, desc + f"\nMISMATCHED {len(bad)} rows: {bad[:4]}"
    return True, desc + f"\nchecked: agrees with the mask on all {len(rows)} oneEach rows"


def budget_timeout(deadline: float, want: int) -> int:
    left = int(deadline - time.time())
    return max(0, min(want, CALL_CAP, left))


def main(argv: Sequence[str]) -> int:
    if len(argv) != 1:
        print(__doc__)
        return 2
    batch = argv[0]
    eng = load_engine()
    WORK.mkdir(parents=True, exist_ok=True)
    deadline = time.time() + BATCH_BUDGET
    results: List[Outcome] = []

    if batch == "regress":
        # the three known 4x4 answers, with the settings the 4x4 work used (tight)
        specs: List[Tuple[str, int, int, bool]] = [
            ("r854s6", 854, 6, False),
            ("r854s7", 854, 7, False),
            ("r3824s6", 3824, 6, False),
            ("r9999s6", 9999, 6, False),
        ]
        for label, mask, gates, loose in specs:
            to = budget_timeout(deadline, 180)
            results.append(run_case(eng, label, mask, 4, 4, gates, loose, False, to))
        # any SAT case that failed to be found tight gets one loose retry
        expect = {"r854s6": "UNSAT", "r854s7": "SAT",
                  "r3824s6": "SAT", "r9999s6": "SAT"}
        for o in list(results):
            if o.status != expect[o.label] and expect[o.label] == "SAT":
                to = budget_timeout(deadline, 180)
                results.append(run_case(eng, o.label + "_loose",
                                        854 if "854" in o.label else
                                        (3824 if "3824" in o.label else 9999),
                                        4, 4, 7 if o.label == "r854s7" else 6,
                                        True, False, to))

    elif batch == "control":
        ok, desc = hand_witness(eng)
        print("=== independent hand-built witness check")
        print(desc, flush=True)
        print(f"--- hand witness: {'OK' if ok else 'BROKEN'}", flush=True)
        to = budget_timeout(deadline, CALL_CAP)
        results.append(run_case(eng, "c12_loose", MASK, N, M, 12, True, False, to))

    elif batch == "hand":
        # no solver at all: the mask decoding, then the two hand-built circuits
        _, rws = eng.mask_rows(MASK, N, M)
        print(f"=== mask {MASK} as a {N}x{M} matrix, entry (u,v) = testBit({M}*u+v)")
        edges: List[Tuple[int, int]] = []
        for u in range(N):
            line = ""
            for v in range(M):
                on = rws[M * u + v][1]
                line += "1" if on else "."
                if on:
                    edges.append((u, v))
            print("    " + line)
        print(f"    {len(edges)} edges: "
              + " ".join(f"({u},{v})" for u, v in edges), flush=True)
        for name, fn in (("12-gate monotone", hand_witness),
                         ("11-gate non-monotone", hand_witness11)):
            ok, desc = fn(eng)
            print(f"=== {name}")
            print(desc, flush=True)
            print(f"--- {name}: {'OK' if ok else 'BROKEN'}", flush=True)

    elif batch == "low7":
        for gates in range(1, 8):
            to = budget_timeout(deadline, 120)
            if to <= 0:
                print(f"=== s{gates}: skipped, batch budget exhausted", flush=True)
                break
            results.append(run_case(eng, f"s{gates}_tight", MASK, N, M, gates,
                                    False, True, to))

    elif batch == "nine":
        for gates in (8, 9):
            to = budget_timeout(deadline, 400)
            if to <= 0:
                print(f"=== s{gates}: skipped, batch budget exhausted", flush=True)
                break
            results.append(run_case(eng, f"s{gates}_tight", MASK, N, M, gates,
                                    False, True, to))

    elif batch == "ten":
        results.append(run_case(eng, "s10_loose", MASK, N, M, 10, True, False,
                                budget_timeout(deadline, 380)))
        if results[-1].status == "TIMEOUT":
            results.append(run_case(eng, "s10_tight", MASK, N, M, 10, False, True,
                                    budget_timeout(deadline, 400)))

    elif batch == "tensat":
        # last witness hunt at 10: loose, with cadical's satisfiable-instance
        # configuration.  Any SAT here is re-simulated on all 25 rows, so a
        # tuned search cannot produce a false positive.
        results.append(run_case(eng, "s10_loose_sat", MASK, N, M, 10, True, False,
                                budget_timeout(deadline, 430), ("--sat",)))

    elif batch == "tensat2":
        results.append(run_case(eng, "s10_loose_sat_w", MASK, N, M, 10, True, False,
                                budget_timeout(deadline, 430),
                                ("--sat", "--seed=12345", "--walkreleff=1000")))

    elif batch == "tentight":
        results.append(run_case(eng, "s10_tight", MASK, N, M, 10, False, True,
                                budget_timeout(deadline, CALL_CAP)))

    elif batch == "eleven":
        ok, desc = hand_witness11(eng)
        print("=== independent hand-built 11-gate non-monotone witness check")
        print(desc, flush=True)
        print(f"--- hand witness 11: {'OK' if ok else 'BROKEN'}", flush=True)
        results.append(run_case(eng, "s11_loose", MASK, N, M, 11, True, False,
                                budget_timeout(deadline, 240)))

    elif batch == "twelve":
        results.append(run_case(eng, "s12_loose", MASK, N, M, 12, True, False,
                                budget_timeout(deadline, CALL_CAP)))

    else:
        print(f"unknown batch {batch!r}")
        print(__doc__)
        return 2

    print("\n==== SUMMARY (" + batch + ") ====")
    for o in results:
        print(f"  {o.label:16s} {o.status:9s} {o.seconds:7.1f}s")
    total = sum(o.seconds for o in results)
    print(f"  solver wall time this batch: {total:.1f}s")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
