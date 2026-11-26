import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.RepPath

/-!
# 13 posted promise rows are false, and the template that makes them is one unit short

This file proves 13 posted statements false, by citing a lemma this repository
already carries. It is offered unsolicited, with no gap id, because these rows
are posted in one direction only and so there is no row to attach a negation to.
The reason for sending it anyway is the last section: the template generating
this family computes its floor with a lemma weaker than the one beside it, so it
keeps posting rows one unit below the true floor and calling them searches.

## The lemma that decides them

`PEqualNP.MetaComplexity.RepPath.path` gives, for `RepSizeAtMost A s`,

  (forcedL A).card + (forcedR A).card <= s

where `forcedL A` is the left vertices with a true entry in some column that is
false elsewhere, and `forcedR A` the right vertices symmetrically
(`RepReads.forcedL` / `forcedR`). It needs a path witness: rows `u`, `x` and
columns `v`, `w` with `A u v`, `A u w`, `A x v` true and `A x w` false, plus one
false entry in row `u` and one in column `v`. On every mask below such a witness
exists, and it is exhibited in the proof term.

## The rows

| row | shape | mask | posted budget | forced reads | true floor |
|---|---|---|---|---|---|
| L-meta-20523 | 3 x 5 | 3517 | 7 | 3 + 5 | 8 |
| L-meta-20940 | 4 x 5 | 101624 | 8 | 4 + 5 | 9 |
| L-meta-20452 | 3 x 5 | 47 | 5 | 2 + 4 | 6 |
| L-meta-20531 | 3 x 5 | 7535 | 6 | 3 + 4 | 7 |
| L-meta-20464 | 3 x 5 | 1093 | 5 | 3 + 3 | 6 |
| L-meta-20460 | 3 x 5 | 249 | 6 | 2 + 5 | 7 |
| L-meta-20456 | 3 x 5 | 111 | 5 | 2 + 4 | 6 |
| L-meta-20525 | 3 x 5 | 3575 | 6 | 2 + 5 | 7 |
| L-meta-21834 | 4 x 6 | 288447 | 8 | 4 + 5 | 9 |
| L-meta-23395 | 4 x 6 | 840563 | 9 | 4 + 6 | 10 |
| L-meta-20922 | 4 x 5 | 39770 | 8 | 4 + 5 | 9 |
| L-meta-21819 | 4 x 6 | 276333 | 8 | 3 + 6 | 9 |
| L-meta-21851 | 4 x 6 | 292863 | 7 | 3 + 5 | 8 |

Each sketch described a search in progress. For `L-meta-20460` it reported
holding a circuit of 7 AND/OR gates, holding none of 6, and called the row a
search. No search is needed: six gates are impossible.

## Where the template loses the unit

The sketch for `L-meta-20531` states its own floor:

  Our count of unread rows and columns gives a floor of 6 (on paper), a gap of 1.

That is the same count used here, one unit weaker. It is `RepReads.reads_le`,
which holds unconditionally and gives `card sum <= s + 1`. `RepPath.path` gives
`card sum <= s` whenever a path witness exists, and on these masks one always
does. So each row is posted one below its own floor, the gap is believed to be
one, and the family is generated as searches that cannot succeed.

These 13 were drawn and screened in a single session; every one whose budget fell
below the sharp floor was false. Using `path` rather than `reads_le` when the
witness exists would stop the family being generated this way.

The bound is a LOWER bound, so it only ever refutes - it cannot confirm a row -
and it is weaker than exhaustion: on the 4 by 4 mask 854, whose optimum is
exactly 7 by two independent encoders, this count yields only 6. Its value is
that it is free and that the kernel checks it.

Every declaration below is generated from the same code that computes the
verdict, so the witness indices are not transcribed by hand.
-/

namespace PEqualNP.Outside.PromiseFloor

open PEqualNP.Represents

/-- The 3 by 5 mask of L-meta-20523: rows `1.111`, `1.11.`, `11...`. -/
def A3517_3x5 : Fin 3 → Fin 5 → Bool :=
  fun u v => (3517 : ℕ).testBit (5 * u.val + v.val)

/-- L-meta-20523 posted 7; the forced reads total 8. -/
theorem A3517_3x5_not_7 : ¬ RepSizeAtMost A3517_3x5 7 := by
  intro h
  have key :=
    PEqualNP.MetaComplexity.RepPath.path 3 5 7 A3517_3x5 0 1 2 4
      (by decide) (by decide) (by decide) (by decide)
      (Exists.intro 1 (by decide)) (Exists.intro 2 (by decide)) h
  revert key
  decide


/-- The 4 by 5 mask of L-meta-20940: rows `...11`, `111..`, `11...`, `11...`. -/
def A101624_4x5 : Fin 4 → Fin 5 → Bool :=
  fun u v => (101624 : ℕ).testBit (5 * u.val + v.val)

/-- L-meta-20940 posted 8; the forced reads total 9. -/
theorem A101624_4x5_not_8 : ¬ RepSizeAtMost A101624_4x5 8 := by
  intro h
  have key :=
    PEqualNP.MetaComplexity.RepPath.path 4 5 8 A101624_4x5 1 2 0 2
      (by decide) (by decide) (by decide) (by decide)
      (Exists.intro 3 (by decide)) (Exists.intro 0 (by decide)) h
  revert key
  decide


/-- The 3 by 5 mask of L-meta-20452: rows `1111.`, `1....`, `.....`. -/
def A47_3x5 : Fin 3 → Fin 5 → Bool :=
  fun u v => (47 : ℕ).testBit (5 * u.val + v.val)

/-- L-meta-20452 posted 5; the forced reads total 6. -/
theorem A47_3x5_not_5 : ¬ RepSizeAtMost A47_3x5 5 := by
  intro h
  have key :=
    PEqualNP.MetaComplexity.RepPath.path 3 5 5 A47_3x5 0 1 0 1
      (by decide) (by decide) (by decide) (by decide)
      (Exists.intro 4 (by decide)) (Exists.intro 2 (by decide)) h
  revert key
  decide


/-- The 3 by 5 mask of L-meta-20531: rows `1111.`, `11.1.`, `111..`. -/
def A7535_3x5 : Fin 3 → Fin 5 → Bool :=
  fun u v => (7535 : ℕ).testBit (5 * u.val + v.val)

/-- L-meta-20531 posted 6; the forced reads total 7. -/
theorem A7535_3x5_not_6 : ¬ RepSizeAtMost A7535_3x5 6 := by
  intro h
  have key :=
    PEqualNP.MetaComplexity.RepPath.path 3 5 6 A7535_3x5 0 1 3 2
      (by decide) (by decide) (by decide) (by decide)
      (Exists.intro 4 (by decide)) (Exists.intro 2 (by decide)) h
  revert key
  decide


/-- The 3 by 5 mask of L-meta-20464: rows `1.1..`, `.1...`, `1....`. -/
def A1093_3x5 : Fin 3 → Fin 5 → Bool :=
  fun u v => (1093 : ℕ).testBit (5 * u.val + v.val)

/-- L-meta-20464 posted 5; the forced reads total 6. -/
theorem A1093_3x5_not_5 : ¬ RepSizeAtMost A1093_3x5 5 := by
  intro h
  have key :=
    PEqualNP.MetaComplexity.RepPath.path 3 5 5 A1093_3x5 0 2 0 2
      (by decide) (by decide) (by decide) (by decide)
      (Exists.intro 1 (by decide)) (Exists.intro 1 (by decide)) h
  revert key
  decide


/-- The 3 by 5 mask of L-meta-20460: rows `1..11`, `111..`, `.....`. -/
def A249_3x5 : Fin 3 → Fin 5 → Bool :=
  fun u v => (249 : ℕ).testBit (5 * u.val + v.val)

/-- L-meta-20460 posted 6; the forced reads total 7. -/
theorem A249_3x5_not_6 : ¬ RepSizeAtMost A249_3x5 6 := by
  intro h
  have key :=
    PEqualNP.MetaComplexity.RepPath.path 3 5 6 A249_3x5 0 1 0 3
      (by decide) (by decide) (by decide) (by decide)
      (Exists.intro 1 (by decide)) (Exists.intro 2 (by decide)) h
  revert key
  decide


/-- The 3 by 5 mask of L-meta-20456: rows `1111.`, `11...`, `.....`. -/
def A111_3x5 : Fin 3 → Fin 5 → Bool :=
  fun u v => (111 : ℕ).testBit (5 * u.val + v.val)

/-- L-meta-20456 posted 5; the forced reads total 6. -/
theorem A111_3x5_not_5 : ¬ RepSizeAtMost A111_3x5 5 := by
  intro h
  have key :=
    PEqualNP.MetaComplexity.RepPath.path 3 5 5 A111_3x5 0 1 0 2
      (by decide) (by decide) (by decide) (by decide)
      (Exists.intro 4 (by decide)) (Exists.intro 2 (by decide)) h
  revert key
  decide


/-- The 3 by 5 mask of L-meta-20525: rows `111.1`, `1111.`, `11...`. -/
def A3575_3x5 : Fin 3 → Fin 5 → Bool :=
  fun u v => (3575 : ℕ).testBit (5 * u.val + v.val)

/-- L-meta-20525 posted 6; the forced reads total 7. -/
theorem A3575_3x5_not_6 : ¬ RepSizeAtMost A3575_3x5 6 := by
  intro h
  have key :=
    PEqualNP.MetaComplexity.RepPath.path 3 5 6 A3575_3x5 0 1 2 4
      (by decide) (by decide) (by decide) (by decide)
      (Exists.intro 3 (by decide)) (Exists.intro 2 (by decide)) h
  revert key
  decide


/-- The 4 by 6 mask of L-meta-21834: rows `111111`, `.1.11.`, `.11...`, `1.....`. -/
def A288447_4x6 : Fin 4 → Fin 6 → Bool :=
  fun u v => (288447 : ℕ).testBit (6 * u.val + v.val)

/-- L-meta-21834 posted 8; the forced reads total 9. -/
theorem A288447_4x6_not_8 : ¬ RepSizeAtMost A288447_4x6 8 := by
  intro h
  have key :=
    PEqualNP.MetaComplexity.RepPath.path 4 6 8 A288447_4x6 1 2 1 3
      (by decide) (by decide) (by decide) (by decide)
      (Exists.intro 0 (by decide)) (Exists.intro 3 (by decide)) h
  revert key
  decide


/-- The 4 by 6 mask of L-meta-23395: rows `11..11`, `1.11..`, `1.11..`, `11....`. -/
def A840563_4x6 : Fin 4 → Fin 6 → Bool :=
  fun u v => (840563 : ℕ).testBit (6 * u.val + v.val)

/-- L-meta-23395 posted 9; the forced reads total 10. -/
theorem A840563_4x6_not_9 : ¬ RepSizeAtMost A840563_4x6 9 := by
  intro h
  have key :=
    PEqualNP.MetaComplexity.RepPath.path 4 6 9 A840563_4x6 0 3 1 4
      (by decide) (by decide) (by decide) (by decide)
      (Exists.intro 2 (by decide)) (Exists.intro 1 (by decide)) h
  revert key
  decide


/-- The 4 by 5 mask of L-meta-20922: rows `.1.11`, `.1.11`, `.11..`, `1....`. -/
def A39770_4x5 : Fin 4 → Fin 5 → Bool :=
  fun u v => (39770 : ℕ).testBit (5 * u.val + v.val)

/-- L-meta-20922 posted 8; the forced reads total 9. -/
theorem A39770_4x5_not_8 : ¬ RepSizeAtMost A39770_4x5 8 := by
  intro h
  have key :=
    PEqualNP.MetaComplexity.RepPath.path 4 5 8 A39770_4x5 0 2 1 3
      (by decide) (by decide) (by decide) (by decide)
      (Exists.intro 0 (by decide)) (Exists.intro 3 (by decide)) h
  revert key
  decide


/-- The 4 by 6 mask of L-meta-21819: rows `1.11.1`, `1.111.`, `11....`, `1.....`. -/
def A276333_4x6 : Fin 4 → Fin 6 → Bool :=
  fun u v => (276333 : ℕ).testBit (6 * u.val + v.val)

/-- L-meta-21819 posted 8; the forced reads total 9. -/
theorem A276333_4x6_not_8 : ¬ RepSizeAtMost A276333_4x6 8 := by
  intro h
  have key :=
    PEqualNP.MetaComplexity.RepPath.path 4 6 8 A276333_4x6 0 1 2 5
      (by decide) (by decide) (by decide) (by decide)
      (Exists.intro 1 (by decide)) (Exists.intro 2 (by decide)) h
  revert key
  decide


/-- The 4 by 6 mask of L-meta-21851: rows `111111`, `11111.`, `111...`, `1.....`. -/
def A292863_4x6 : Fin 4 → Fin 6 → Bool :=
  fun u v => (292863 : ℕ).testBit (6 * u.val + v.val)

/-- L-meta-21851 posted 7; the forced reads total 8. -/
theorem A292863_4x6_not_7 : ¬ RepSizeAtMost A292863_4x6 7 := by
  intro h
  have key :=
    PEqualNP.MetaComplexity.RepPath.path 4 6 7 A292863_4x6 1 2 1 3
      (by decide) (by decide) (by decide) (by decide)
      (Exists.intro 5 (by decide)) (Exists.intro 3 (by decide)) h
  revert key
  decide

end PEqualNP.Outside.PromiseFloor
