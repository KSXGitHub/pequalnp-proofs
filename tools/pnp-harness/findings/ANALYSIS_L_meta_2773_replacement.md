# L-meta-2773 — no counterexample exists, because the statement it negates is true

**Verdict: unprovable.** Released as `statement_seems_false`, which the step's own
sketch anticipates: "none is expected if the positive statement is true".

## What was asked

L-meta-2773 (weight 5) is the exact negation of a "replacement rewrite" step. It
asks for an `IsAO2` fan-in-two AND/OR circuit `C`, a gate `g`, an input position
`b < 2` holding wire `w`, and a wire `w' < n + g`, such that

- `w ≤ w'` pointwise (wherever wire `w` is true, wire `w'` is true),
- `w' ≤ out(C)` (wherever `w'` is true, the circuit's output is true),

yet rewiring position `b` of gate `g` from `w` to `w'` breaks one of: `IsAO2`,
computing the same function, or having the same size.

## Why no such circuit exists

**Two of the three conjuncts cannot fail at all.** `size` is `gates.length`, and
`List.set` preserves length, so the size is unchanged identically. For `IsAO2`:
`AndOrOnly` is untouched since the op is copied; `inputs.set b w'` preserves
`inputs.length = 2`; and `ReadsBack` survives precisely because the hypothesis
supplies `w' < n + g`, which is the reads-back condition for gate `g`. So the
only way to win is to change the computed function.

**The function cannot change either.** Let `D` be the rewired circuit and let
`S = {p : w(p) = false, w'(p) = true}`, which is all of where the two wires
differ, since `w ≤ w'`.

*Every wire below `n + g` is identical in `C` and `D`.* Only gate `g` was
touched, and it produces wire `n + g`, so wires `0 … n+g-1` are computed by
inputs and by gates before `g`, none of which changed. In particular wire `w'`
itself has the same value in both circuits — this is what makes the rest work,
and it is exactly what `w' < n + g` buys.

*Off `S`:* gate `g`'s two input values agree in `C` and `D`, so gate `g` agrees,
so by induction upward every later wire agrees, so `out(D)(p) = out(C)(p)`.

*On `S`:* `w'(p) = true`, and the hypothesis `w' ≤ out(C)` gives
`out(C)(p) = true`. Separately, `D ≥ C` pointwise everywhere: gate `g`'s value
rose or stayed (an AND or OR is monotone in each operand, and we replaced an
operand by a pointwise-larger one), and every gate downstream is monotone, so no
wire can fall. Hence `out(D)(p) ≥ out(C)(p) = true`, so `out(D)(p) = true` as
well. The two agree.

So `out(D) = out(C)` on every input, and all three conjuncts hold for every
instance satisfying the hypotheses. The negation is unsatisfiable.

Note where each hypothesis earns its place: `w ≤ w'` gives monotonicity in one
direction, `w' ≤ out(C)` gives the value on `S`, and `w' < n + g` keeps `w'`
itself from being disturbed by the rewrite. Drop any one and the lemma fails.

## Machine corroboration

The argument above was derived by hand, so it was checked by exhaustive search:
every AND/OR fan-in-two reads-back circuit with `n ∈ {0,1,2,3}` inputs and up to
3 gates, every output wire, every gate `g`, every position `b`, and every
`w' < n + g`, keeping only instances that satisfy both pointwise hypotheses.

    hypothesis-satisfying instances tested: 792552
    counterexamples (function changed): 0

## Consequence worth passing on

The positive step this negates is **true**, and the proof above is short and
formalisable: `size` by `List.length_set`, `IsAO2` by three component arguments,
and the function by induction on the wire index with the case split on `S`. Of
the pair, that is the one worth leasing.
