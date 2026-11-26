# Preserved working tools

Everything here ran in a container that a reboot or a routine cleanup can clear,
and that goes away for good when the session ends. The harness under
`tools/pnp-harness/` is committed; none of this was, because it fails that
directory's ruff and mypy gates - a weak reason next to losing it. So it is kept
here instead, outside both `gates.sh` (which runs `ruff check .` with
`tools/pnp-harness/` as its working directory) and the `harness-checks` workflow
(which triggers on `tools/pnp-harness/**`). These are research tools, preserved
for continuity; they are not maintained to the harness standard and this
directory does not pretend otherwise.

## How to use it again

Copy the tree back into a scratchpad and point the harness at it. Two tools read
their engine location from the environment, so nothing needs editing:

```bash
cp -r notes/ours/engines "$SCRATCH/pnp"
export PNP_ENGINE_DIR="$SCRATCH/pnp/p19071"   # masklookup.py
export PNP_MONO_DIR="$SCRATCH/pnp/p20508"     # promisehunt.py
chmod +x "$SCRATCH/pnp/x.sh"
```

`x.sh` expects jobs at `jobs/<name>.py` relative to itself, which is how the tree
is laid out here. The C programs need building: `cc -O2 -o scan p19071/scan.c`
and likewise for `deep.c`.

## Read these first

* `STATE.md` - the running notes. Every row screened, every verdict and the
  reason for it, and every mistake with its cause. This is the file that makes a
  later session useful rather than starting over, and it is the main reason this
  directory exists: context gets compacted, and this does not.
* `PLAYBOOK.md` - the procedures that worked, written to be followed.
* `DEADLINE.md` - the window deadline and the stall ledger. The authority on
  both; the figure in a heartbeat message is a copy and can drift.
* `PENDING_PRS.md` - what is outstanding upstream.

## The engines, and how far each is trusted

| file | what it does | validation |
|---|---|---|
| `p19071/rep44.py` | exact synthesis of least `FanInTwo` circuits representing an n x m mask on the one-a-side promise, as SAT | 4x4 regressions pass on four masks of independently known optimum: 854 (UNSAT at 6, SAT at 7), 3824 and 9999 (SAT at 6) |
| `p20508/rep44m.py` | the same plus `--monotone`, forbidding the NOT forms: the model of `RepSizeAtMost` | validated from BOTH sides on mask 249 - UNSAT at 6, where `notes/ours/L_promise_counting.lean` holds a kernel proof that 6 is impossible, and SAT at 7 with a NOT-free circuit re-simulated on all 15 rows, matching the desk's own claim |
| `p19071/loose.py` | independent second-opinion encoder | its UNSAT covers every circuit of at most that size by padding monotonicity; agreed with `rep44.py` on mask 854 |
| `p19071/scan.c` | column model over all 65536 4x4 masks | 11 seconds for the full sweep; produced `tools/pnp-harness/lrat/mask4x4_gt6.txt` |
| `p19071/deep.c` | solver-free depth enumeration | about 50 s for the 7-gate question |
| `p4873/validate.py` | re-simulates a decoded circuit independently of the encoder that produced it | this is the control that makes any SAT believable; use it |
| `p4873/mklean.py` | turns a solver gate list into a checkable Lean file | the witness route for a FIND row |
| `pcx121/emit_php.py` | emits the **verified** 58-line Res(xor) PHP(4,3) refutation | one command if a 56/57/58 row is ever posted |
| `pcx121/sat55.py` | the 55-line attempt | did not come back; not a negative result |

## Two laws that cost real time to learn

**Hunt loose, prove UNSAT tight.** Tight symmetry breaking makes UNSAT reachable
and makes SAT much harder to *find*: cadical missed a known 12-gate completion in
330 s with distinct/order constraints on, and found it in 16 s with them off.

**No UNSAT without a positive control.** The same code path must return SAT at
some size on the same instance before any UNSAT from it is believed. An UNSAT
from a broken encoding is indistinguishable from a real one, and a restricted
model can be *provably* incomplete and still return UNSAT at every size - that
happened on the Petersen pure-product search, where 6 and 7 both came back UNSAT
while a 7-gate circuit demonstrably exists.

## What was deliberately left out

CNF files and solver logs (regenerable and large), tool caches, and the lease and
step state - a lease id is a credential with a twenty-minute life and the desk
keeps the authoritative copy, refetchable with `desk.sh state`.
