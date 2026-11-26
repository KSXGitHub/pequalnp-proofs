import PEqualNP.Defs
import PEqualNP.Outside.L_meta_8305
import PEqualNP.Outside.R_meta_2658_412

/-!
SCRATCH / AUDIT FILE (not for submission).

Purpose: pin down exactly how much of the pair-cleanliness normal form for the public
`Monotone2` model is already merged upstream.

`R_meta_2658_412` (merged) derives the normal form from TWO hypotheses, `repairFew` and
`repairMany`. The merged, fully-proved `L_meta_8305` IS `repairFew`, verbatim. So the whole
normal form follows from `repairMany` ALONE. This file checks that composition in the kernel.
-/

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.NotPremium

/-- The pair-cleanliness normal form for `Monotone2`, from `repairMany` alone.
`repairFew` is discharged by the merged `PEqualNP.Outside.L_meta_8305`. -/
theorem gap_is_exactly_repairMany
    (repairMany : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → Monotone2 C → circuitFun n C = graphFun G ∅ → (junk G C).Nonempty →
      (∀ j ∈ junk G C, ∃ a b u v, G.Adj a b ∧ G.Adj u v ∧ pairInput a b ≠ pairInput u v ∧
        circuitFun n {C with gates := replaceByConst C.gates j false} (pairInput a b) = false ∧
        circuitFun n {C with gates := replaceByConst C.gates j false} (pairInput u v) = false) →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
        (junk G D).card < (junk G C).card) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x4 : Fin x1) (x5 : Fin x1), x2.Adj x4 x5) → (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x5 ≠ x7 → x5 ≠ x8 → x6 ≠ x7 → x6 ≠ x8 → x7 ≠ x8 → x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → ¬x2.Adj x8 x5) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin x1 → Bool), x3.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ (∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = Bool.true ↔ ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true) ∧ x8.size ≤ x3.size ∧ ∀ (x9 : ℕ) (x10 : PEqualNP.CircuitLowerBounds.Gate), x8.gates[x9]? = Option.some x10 → x10.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x13 : Fin x1 → Bool), (x8.wires (List.ofFn x13)).getD (x1 + x9) Bool.false = Bool.true → ∃ (x15 : Fin x1) (x16 : Fin x1), x2.Adj x15 x16 ∧ x13 x15 = Bool.true ∧ x13 x16 = Bool.true :=
  PEqualNP.Outside.R_meta_2658_412
    (fun n G inst C j => @PEqualNP.Outside.L_meta_8305 n G inst C j)
    repairMany
