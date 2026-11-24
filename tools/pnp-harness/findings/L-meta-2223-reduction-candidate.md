# L-meta-2223: reduced to one Nodup obligation

Fano plane, weight 60, open to reductions (one reduction was already live when we held it).
Released as `missing_lemma`. `PARTIAL_L_meta_2223.lean` elaborates with exit 0 and a single
`sorry`.

After `intro x1 x2 x3 C a b hC hab h1 h2`, the witness `D := C` closes everything except one
goal. Size at most 27 and the incidence-computing part come from `hC`; both line-degree at least
two parts come from `h1` and `h2`. What survives is that the gate-wire reads of `C`,

    (C.output :: C.gates.flatMap Gate.inputs).filter (14 <= .)

form a `Nodup` list. A circuit that reuses a gate wire breaks it, so the content is turning a
shared-wire circuit into a read-once one without losing line-degree at least two on either
marked set.

## Why the cheap routes are all closed

- There is no edgeless branch here: the edge `x1 a b` is a hypothesis.
- The empty circuit with an out-of-range output computes constant false, and incidence is not
  constant, so it fails its own obligation. (This is the move that worked on L-meta-4895; it does
  not transfer.)
- The 27-gate star formula computes incidence and has `Nodup` reads, but its line-degree is only
  one per marked set, an AND of a marked input with an OR of unmarked ones. Degree at least two
  needs an AND of two wires both containing the marked input, i.e. a redundant gate, which costs
  about one more gate: 28 against the cap of 27. So no witness is buildable from the star.

## What decides it

Either no 27-gate Fano circuit has line-degree at least two on both marked sets, making the step
vacuously true, or such a shared-read DAG circuit exists with no read-once equivalent, making it
false. We found no witness, so we do not claim it false. Sibling notes record that SAT search is
infeasible at this size.
