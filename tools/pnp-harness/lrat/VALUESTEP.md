# Winning a VALUE row, mechanically

A value row asks for the exact optimum of a function, so unlike a lower-bound row it has a
determinate answer. Upstream carries 354 `V_<prog>_<n>__k<k>.lean` files in that shape, and this
pipeline reproduces one end to end: **witness, four-line upper bound, and an LRAT-certified lower
bound, in a single self-contained file with no hypotheses.** That is a COMPLETE PROOF, which is
worth saying out loud, because every artifact we had merged before this was an `R_` reduction that
assumed its hypotheses and left the row open.

## The ceiling, which decides whether a row is winnable at all

| route | reach | why it stops there |
|---|---|---|
| LRAT (`LinkN2` + `Checker`) | n = 4 with k <= 6; n = 8 with k <= 5 | the FILE cap. Upstream's largest k=6 file is 505,412 B against lint's 524,288 B, i.e. 96% full. Mask 4919 at n=4, k=7 renders 1,883,049 B - 3.6x the cap - and cadical's LRAT is already trimmed, so `--trim` saves nothing. Segmenting does not help: the cap is on the file, not the theorem. |
| inlined exhaustive search | k = 7..13 | upstream's own route above the LRAT ceiling: ~111 KB of verified search machinery (`availB`, `lower_base`, `lower_iso`, `lower_slice`, `lower_to_circuit4`) plus a ~22 KB per-mask search record, ~130 KB total, scaling to 403 KB at k=13. THE GENERATOR FOR THAT RECORD IS NOT IN THE REPO - we would have to write the search that produces it. |

So: n=4/k<=6 and n=8/k<=5 are winnable TODAY in minutes. Above that the witness stays cheap and the
lower bound does not.

## The chain

1. `tools/pnp-harness/lrat/gentab.py N S MASK out.cnf` - CNF from a truth-table mask, mirroring
   `enc2` clause for clause. Bound proved is `S+1`, since padding is allowed.
2. `cadical --lrat=true --no-binary out.cnf out.lrat` - the bundled
   `/root/.elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical` (2.1.2) emits LRAT directly.
   THE CERTIFICATE IS JUST THIS OUTPUT TRANSCRIBED; nothing upstream-private is involved.
3. `notes/data/lrat-link/genrow.py --not` - transcribes CNF + LRAT into the Lean key/certificate
   lists.
4. `decnot.py` - decodes a SAT model into a witness circuit, written from the LEAN semantics
   and independent of the CNF, so it is a genuine second opinion on the witness.
5. `assemble.py` - emits the finished file: `import PEqualNP.Defs`, the witness, the
   four-line `upper`, the `lower`, and the final conjunction.

## Validation, which is the part that earns trust

Run on upstream's own mask (n=4, table 3824, k=6) the witness line came out BYTE-IDENTICAL to
upstream's `def wit`, `not [5]` gate included, derived independently through `decnot.py`. `fn`,
`wit`, `upper`, `rows`, `F` and the `lower` term all matched; only the certificate cut differed
(upstream used two segments, our cadical run fitted one). Then a fresh mask upstream does not cover,
table 9999 at k=6, went through the same pipeline to CHECK_OK in 11 s.

## Traps, each one hit

- `genrow.py` emits bare top-level `set_option`s and a `/-!` docstring beginning `# `. lint rejects
  both. Move the options onto the theorem as `set_option <name> <digits> in` and rewrite the comment.
- `decls.sh` reports strays `PEqualNP.MetaComplexity.FanInTwo.eq_1` and `wit.eq_1`, from
  `simp [wit, FanInTwo]` inside `upper`. Upstream's own V_ files have the IDENTICAL profile, so this
  is accepted in practice for value rows - do not contort the proof to remove them.
- `c_K` is a KEY list, not a proof: `loadF` stores clause `i` under key `c_K[i] - 1` and `0` drops
  the clause. Clause ORDER is load-bearing (fOp, fSrcAlo, fSrcEq, fGate, fOutAlo, fOutEq, fOut,
  fPad, fPre, fPadRd, fOrd, fUsed, fNot, fNotNot, then fLex for `enc2`).
- Nothing about the packing needs proving: `check_sound` holds for ANY token list, so a bad key,
  unit or cut can only make the checker reject.

## `LinkN2` DOES cover NOT gates - an earlier note of ours was wrong

`LinkN.Model.op` is `0 AND, 1 OR, 2 TRUE (padding), 3 NOT`, `gfun` gives `!a` at 3, `Valid.not_eq`
forces a NOT gate's two sources equal, and `size_of_unsat2` concludes about `HasCircuitSize`, i.e.
`FanInTwo`. The "AND/OR only, no NOT" header we relied on belongs to
`Promise.lean`/`PromiseGen.lean`/`PromiseCube.lean`, which sit on `Link2` - a different file family.
Both readings are right about their own files.
THIS REOPENS THE FanInTwo REFUTATION ROUTE we had written off as having no technique, with one
caveat: `LinkN2.lower_of_unsat2` wants `hev` on EVERY input, so there is no ready NOT-plus-promise
wrapper. It is derivable in a few lines, because `LinkN.Valid n s g R M` is already relative to a row
predicate `R` and `LinkN.valid_ofCirc` takes an `R`-restricted `hev`; `Promise.promise_lower` is
exactly that construction over `Link2`. Copy its shape.

## Where the two scripts we wrote live

`decnot.py` and `assemble.py` are at
`/tmp/claude-0/-home-user-pequalnp-proofs/731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/pnp/pdry/`
and are deliberately NOT tracked: they are throwaway generators that do not meet this repo's ruff
configuration (ten findings, no automatic fixes, and T20 forbids the prints they are built around).
Everything needed to rewrite them is in the contract above, and the load-bearing transcriber,
`notes/data/lrat-link/genrow.py`, is already tracked upstream. If either script is ever worth
keeping, it needs a rewrite to this repo's lint rules, not a copy.
