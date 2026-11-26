import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.RepPath

/-!
# Two posted promise rows are false, and the proof is counting, not search

The desk posts rows asking whether a given bipartite mask fits in a given budget of
AND and OR gates on the one-a-side promise. Its sketches say these are searches:
for L-meta-20460 it reported holding a circuit of 7 AND/OR gates for this graph that
shares nothing, holding none of 6, and called the row a search; L-meta-21851 is the
same shape one size up. Both are decided in a millisecond by a lemma already checked
in this repository, with no solver and no exhaustion.

`PEqualNP.MetaComplexity.RepPath.path` says that if `RepSizeAtMost A s` holds then

  (forcedL A).card + (forcedR A).card <= s,

where `forcedL A` collects the left vertices that have a true entry in some column
which is false somewhere else, and `forcedR A` the right vertices symmetrically.
It asks for a path witness: rows `u`, `x` and columns `v`, `w` with `A u v`, `A u w`
and `A x v` true and `A x w` false, plus a false entry in row `u` and one in
column `v`.

For the two masks below the forced counts exceed the posted budget, so no monotone
circuit of that size can exist. The bound is a LOWER bound on size, so this method
can only ever refute a row, never confirm one - and it is weaker than exhaustion:
on the 4 by 4 mask 854, whose optimum is exactly 7 by a two-encoder sweep, counting
yields only 6. Its virtue is that it is free and that the conclusion is checked by
the kernel rather than asserted by a search that did not return.
-/

namespace PEqualNP.Outside.PromiseCounting

open PEqualNP.Represents

/-- The 3 by 5 mask of L-meta-20460: rows `1..11`, `111..`, `.....`. -/
def A249 : Fin 3 → Fin 5 → Bool := fun u v => (249 : ℕ).testBit (5 * u.val + v.val)

/-- The 4 by 6 mask of L-meta-21851: rows `111111`, `11111.`, `111...`, `1.....`. -/
def A292863 : Fin 4 → Fin 6 → Bool := fun u v => (292863 : ℕ).testBit (6 * u.val + v.val)

/-- The 3 by 5 mask of L-meta-20531: rows `1111.`, `11.1.`, `111..`. -/
def A7535 : Fin 3 → Fin 5 → Bool := fun u v => (7535 : ℕ).testBit (5 * u.val + v.val)

/-- Three left vertices and five right ones are forced on `A249`, so eight gates at
least - and the posted budget was six. -/
theorem A249_not_six : ¬ RepSizeAtMost A249 6 := by
  intro h
  have key :=
    PEqualNP.MetaComplexity.RepPath.path 3 5 6 A249 0 1 0 3 (by decide) (by decide) (by decide)
      (by decide) (Exists.intro 1 (by decide)) (Exists.intro 2 (by decide)) h
  revert key
  decide

/-- The same count on the 4 by 6 mask, where the posted budget was seven. -/
theorem A292863_not_seven : ¬ RepSizeAtMost A292863 7 := by
  intro h
  have key :=
    PEqualNP.MetaComplexity.RepPath.path 4 6 7 A292863 1 2 1 3 (by decide) (by decide) (by decide)
      (by decide) (Exists.intro 5 (by decide)) (Exists.intro 3 (by decide)) h
  revert key
  decide

/-- The desk posted this one with its own floor written down: its sketch reads that the
count of unread rows and columns gives a floor of six on paper, a gap of one. That is the
`reads_le` bound, which loses a unit; the path witness below recovers it, and seven is
what the row needed to beat. -/
theorem A7535_not_six : ¬ RepSizeAtMost A7535 6 := by
  intro h
  have key :=
    PEqualNP.MetaComplexity.RepPath.path 3 5 6 A7535 0 1 3 2 (by decide) (by decide) (by decide)
      (by decide) (Exists.intro 4 (by decide)) (Exists.intro 2 (by decide)) h
  revert key
  decide

end PEqualNP.Outside.PromiseCounting
