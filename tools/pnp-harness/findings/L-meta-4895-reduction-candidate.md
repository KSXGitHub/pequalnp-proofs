# L-meta-4895: half proved, and the best reduction candidate so far

Weight 100, open to reductions. Released as `missing_lemma` only because the pull-request
channel was shut at the time; the work below is the useful part.

`PARTIAL_L_meta_4895.lean` elaborates with exit 0 and exactly ONE `sorry`, on line 12. So one of
the two branches is machine-checked already.

## What is proved

Split on whether the incidence relation has an edge:

    by_cases he : ∃ a b, x3 a b

The EDGELESS branch closes completely. The witness is the empty circuit with an out-of-range
output wire, `⟨[], x1 + x2⟩`, which computes the constant false; `simp_all` then discharges every
obligation. Two name traps cost runs here and are worth recording: the right names are
`PEqualNP.EdgeOwnership.AndOrOnly` and `PEqualNP.MetaComplexity.NestedCover.ReadsBack`, NOT the
`PEqualNP.TopForm.*` spellings the statement's shape suggests.

## What is left, exactly

Taking the witness `D := C` (the circuit already in scope) discharges `IsAO2`, the function
equality and `size ≤ size`. Exactly one obligation survives:

    IsReadK (x1 + x2) C 1

that is, `ReadK.readsAtMost C (x1+x2) (setList S) 1 = true` for every prime implicant `S` of the
function: `C` must have, for each edge {point, line}, a proof tree reading each variable at most
once. No hypothesis gives that for an arbitrary AND/OR circuit computing the function, so the
edge branch needs a replacement circuit, no larger, that is read-1 on every prime implicant.

The branch is not degenerate: the hypotheses are jointly satisfiable, a single edge satisfies all
of them, and no counterexample was found by hand on single edges, stars or short paths. A
canonical DNF witness would need size about 2e-1 for e edges, which is a monotone lower bound for
4-cycle-free incidence and appears to be open.

## The reduction worth sending

The step takes reductions, and this is a genuine cut rather than a trivial case split, because
the two sides do different work:

    h1 : <the step's statement restricted to the edgeless relation>     -- already proved above
    h2 : <every fan-in-two AND/OR circuit computing a 4-cycle-free incidence function has one
          no larger that is read-1 on every prime implicant>            -- the real content

Send the reduction together with the proof of `h1`, as the rules ask. Credit for a reduction
arrives only once every hypothesis is checked, so `h2` being hard means credit is deferred - but
`h1` becomes a step anyone can close immediately, and `h2` names the open lemma precisely.
