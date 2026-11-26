# Does one NOT gate save a gate? Measured, undecided - and a lemma worth more

The desk posts six rows of the form *"it is false that: at fan-in two, one NOT
gate saves nothing on edges ..."* (L-meta-14745, 10865, 10643, 10713, 10633,
10793). Each is refutable exactly when, for the function
`f(x) = OR over edges (a,b) of (x_a and x_b)` on all `2^n` inputs,

* `N` = the least size with AND, OR and **at most one NOT** gate, and
* `M` = the least size with AND and OR only

satisfy `N < M`. If `N = M` the row is true and no counterexample exists. The
desk's own sketch says a counterexample is "not expected if the positive
statement is true", so it believes `N = M`.

## The answer: not determined, and the rows are not worth pursuing

Three graphs were measured, tight sweeps upward from size 1 so that every size
below the frontier is a recorded UNSAT:

| graph | n | edges | lower bound | upper bound | verdict |
|---|---|---|---|---|---|
| G1 | 8 | 12 | 9 | 14 | `N` and `M` both undetermined |
| G2 | 7 | 10 | 9 | 12 | both undetermined |
| G3 | 7 | 14 | 9 | 15 | both undetermined |

The lower bounds are complete UNSAT runs at sizes 1 to 8 for **both** NOT
budgets. The upper bounds are hand circuits, each re-simulated on all `2^n`
inputs by a simulator written separately from the encoder. **Every size 9 run is
a did-not-return, not an UNSAT**, so nothing above 8 is refuted on any graph.

Two observations that are evidence without being proof:

* at every size where the solver returned a verdict, the monotone and the
  one-NOT searches returned the **same** verdict;
* every SAT the solver produced decoded to a circuit with **zero NOT gates even
  when one was permitted**.

That points towards `N = M`, which would make all six rows true and unrefutable.
Combined with the cost - the sizes that matter, 11 to 14, extrapolate to
10^4 to 10^5 solver-seconds each with this encoding, against 10^2 at size 8 -
the decision is to leave these rows alone. Not because they are hard in an
interesting way, but because the measurement says a counterexample probably does
not exist and the search cannot reach the sizes that would settle it.

## The padding lemma, which is the useful part

For this family a single **loose** exact-size UNSAT already gives the lower
bound, with no sweep over smaller sizes. Let a circuit of size `k` compute the
target, and let its last gate be `c = a op b`. If `op` is `and` or `or`, append
`d = c op a`:

```
op = or  :  d = (a or b) or a  = a or b  = c
op = and :  d = (a and b) and a = a and b = c
```

`d` carries `c`'s value on **every** input, whatever the row set, `d` is last and
is the output, `c` is read, and no gate is left unread - a circuit of size
`k + 1` in the same normal form. So SAT at `k` forces SAT at `k + 1`, and by
induction at every larger size. Contrapositive:

> **UNSAT at exactly the budget rules out every circuit of size at most the
> budget.**

Two conditions, both load-bearing:

1. **Distinct-columns symmetry breaking must be OFF.** Padding duplicates `c`'s
   column, so a constraint forbidding duplicate columns forbids the padded
   circuit and the induction fails. This is why tight sweeps still need to climb
   from size 1, and it turns "hunt loose" from a preference into a requirement
   for this argument.
2. **The last gate must not be a NOT.** For a monotone circuit that is
   automatic. For a one-NOT circuit computing a non-constant monotone `f` it
   still holds: if the last gate were `NOT a`, then `f` would be the complement
   of `a`, and `a` is computed monotonically, so `f` would be antitone as well as
   monotone and hence constant. It does **not** transfer to a partial-spec
   FanInTwo row, where the constrained set need not make the target monotone -
   there, sweep.

Verified rather than assumed: on 4x4 mask 3824 the engine returns SAT at sizes
5, 6, 7, 8 and 9 with no gap, which is upward closure in action; and on 3x5 mask
3309 the size-by-size sweep returns UNSAT at 1 through 6 exactly as padding
predicts from the single UNSAT at 7.

`tools/pnp-harness/promisehunt.py` now relies on this and skips the sweep, with
`--sweep` kept to re-confirm it. What padding does **not** replace is the
positive control: the same code path must still return SAT at some larger size on
the same instance, because an UNSAT from a broken encoding looks exactly like a
real one.

## If anyone wants the row decided after all

The blocker is the encoding, not the CPU. rep44's scheme uses one selector per
gate per wire-pair, which is about 2.09 million clauses at size 14 on 256 rows,
and solve times grow roughly 7 to 8 times per gate. A one-hot-index-per-input-slot
encoding - two slot selectors and two auxiliary value columns per gate per row
instead of one selector per wire pair - drops the clause count from about
`O(s n^2 2^n)` to about `O(s n 2^n)`, on the order of 10^5 clauses instead of
10^6 at these sizes. G2 is the right target: smallest interval, a verified
12-gate circuit already in hand, and only size 11 genuinely in doubt once the
UNSAT frontier moves two steps. With padding, the decisive experiment is then a
single pair of loose runs at one size: monotone UNSAT and one-NOT SAT at the same
size is a complete refutation.
