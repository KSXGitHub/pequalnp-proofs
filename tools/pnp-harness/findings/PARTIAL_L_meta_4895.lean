import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4895 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x10 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) ∧ x9.size ≤ x5.size ∧ PEqualNP.ReadK.IsReadK (x1 + x2) x9 (1 : ℕ) := by
  intro x1 x2 x3 x4 x5 h4 hA hf
  by_cases he : ∃ (a : Fin x1) (b : Fin x2), x3 a b
  · refine ⟨x5, hA, hf, le_refl _, ?_⟩
    unfold PEqualNP.ReadK.IsReadK
    intro S hS
    have := hS.1
    simp_all [PEqualNP.ReadK.readsAtMost, PEqualNP.ReadK.readVectors, PEqualNP.ReadK.IsPrimeImplicant]
    sorry
  · refine ⟨⟨[], x1 + x2⟩, ?_, ?_, ?_, ?_⟩
    · simp [PEqualNP.TopForm.IsAO2, EdgeOwnership.AndOrOnly, PEqualNP.MetaComplexity.NestedCover.ReadsBack]
    · intro x
      simp_all [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires]
    · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
    · unfold PEqualNP.ReadK.IsReadK
      intro S hS
      have := hS.1
      simp_all [PEqualNP.ReadK.IsPrimeImplicant, PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires]
