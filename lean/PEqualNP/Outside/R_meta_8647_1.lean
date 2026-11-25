import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8647_1
    (h1 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeaa8a8a8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → 7 ≤ C.size)
    (h2 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeaa8a8a8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0xeaa8a8a8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeaa8a8a8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  obtain ⟨C, hfan, hsize, hcomp⟩ := hs
  obtain ⟨D, hmono, hdsize, hdcomp⟩ := h2
  exact ⟨D, hmono, le_trans hdsize (le_trans (h1 C hfan hcomp) hsize), hdcomp⟩
