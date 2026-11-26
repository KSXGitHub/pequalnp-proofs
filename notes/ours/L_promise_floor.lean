import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.RepPath

/-!
# Three posted promise rows are false, and the template that makes them is one unit short

This file proves three posted statements false, by citing a lemma this repository
already carries. It is offered unsolicited, with no gap id, because the rows it
settles are posted in one direction only and so there is no row to attach a
negation to. The reason for sending it anyway is the last section: the template
generating this whole family computes its floor with a lemma that is weaker than
the one beside it, so it keeps posting rows one unit below the true floor and
calling them searches.

## The lemma that decides them

`PEqualNP.MetaComplexity.RepPath.path` gives, for `RepSizeAtMost A s`,

  (forcedL A).card + (forcedR A).card <= s

where `forcedL A` is the left vertices with a true entry in some column that is
false elsewhere, and `forcedR A` the right vertices symmetrically
(`RepReads.forcedL` / `forcedR`). It needs a path witness: rows `u`, `x` and
columns `v`, `w` with `A u v`, `A u w`, `A x v` true and `A x w` false, plus one
false entry in row `u` and one in column `v`. On the masks below such a witness
always exists and is exhibited in the proof term.

## The three rows

| row | shape | mask | posted budget | forced reads | true floor |
|---|---|---|---|---|---|
| L-meta-20460 | 3 x 5 | 249 | 6 | 2 + 5 | 7 |
| L-meta-21851 | 4 x 6 | 292863 | 7 | 3 + 5 | 8 |
| L-meta-20531 | 3 x 5 | 7535 | 6 | 3 + 4 | 7 |

Each sketch described a search in progress. For L-meta-20460 it reported holding
a circuit of 7 AND/OR gates, holding none of 6, and called the row a search. No
search is needed: six gates are impossible.

## Where the template loses the unit

The sketch for L-meta-20531, a 204-point row, states its own floor:

  Our count of unread rows and columns gives a floor of 6 (on paper), a gap of 1.

That count is the same one used here, one unit weaker. It is `RepReads.reads_le`,
which holds unconditionally and gives `card sum <= s + 1`. `RepPath.path` gives
`card sum <= s` whenever a path witness exists, and on these masks one always
does. So the row is posted one below its own floor, the gap is believed to be
one, and the family is generated as searches that cannot succeed.

Eight rows of this family were drawn and screened in a single session; every one
whose budget fell below the sharp floor was false, and releasing them as
`statement_seems_false` returned them to the pool unchanged, so they were drawn
again by others. Using `path` rather than `reads_le` when the witness exists
would stop the family being generated this way.

The bound is a LOWER bound, so it only ever refutes - it cannot confirm a row -
and it is weaker than exhaustion: on the 4 by 4 mask 854, whose optimum is
exactly 7 by two independent encoders, this count yields only 6. Its value is
that it is free and that the kernel checks it.
-/

namespace PEqualNP.Outside.PromiseFloor

open PEqualNP.Represents

/-- The 3 by 5 mask of L-meta-20460: rows `1..11`, `111..`, `.....`. -/
def A249 : Fin 3 → Fin 5 → Bool := fun u v => (249 : ℕ).testBit (5 * u.val + v.val)

/-- The 4 by 6 mask of L-meta-21851: rows `111111`, `11111.`, `111...`, `1.....`. -/
def A292863 : Fin 4 → Fin 6 → Bool := fun u v => (292863 : ℕ).testBit (6 * u.val + v.val)

/-- The 3 by 5 mask of L-meta-20531: rows `1111.`, `11.1.`, `111..`. -/
def A7535 : Fin 3 → Fin 5 → Bool := fun u v => (7535 : ℕ).testBit (5 * u.val + v.val)

/-- Two left vertices and five right ones are forced, so seven gates at least,
against the posted six. -/
theorem A249_not_six : ¬ RepSizeAtMost A249 6 := by
  intro h
  have key :=
    PEqualNP.MetaComplexity.RepPath.path 3 5 6 A249 0 1 0 3 (by decide) (by decide) (by decide)
      (by decide) (Exists.intro 1 (by decide)) (Exists.intro 2 (by decide)) h
  revert key
  decide

/-- Three and five forced, so eight at least, against the posted seven. -/
theorem A292863_not_seven : ¬ RepSizeAtMost A292863 7 := by
  intro h
  have key :=
    PEqualNP.MetaComplexity.RepPath.path 4 6 7 A292863 1 2 1 3 (by decide) (by decide) (by decide)
      (by decide) (Exists.intro 5 (by decide)) (Exists.intro 3 (by decide)) h
  revert key
  decide

/-- Three and four forced, so seven at least, against the posted six. This is the
row whose own sketch records the floor as six. -/
theorem A7535_not_six : ¬ RepSizeAtMost A7535 6 := by
  intro h
  have key :=
    PEqualNP.MetaComplexity.RepPath.path 3 5 6 A7535 0 1 3 2 (by decide) (by decide) (by decide)
      (by decide) (Exists.intro 4 (by decide)) (Exists.intro 2 (by decide)) h
  revert key
  decide

end PEqualNP.Outside.PromiseFloor
