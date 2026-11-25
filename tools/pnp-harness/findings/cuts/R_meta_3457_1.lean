import PEqualNP.Defs

-- A cut of the step along the normal form that minimality supplies.
--
-- The predecessor step L-meta-3456 settled, machine-checked, that the obvious repair moves
-- (forcing an offending AND gate to the constant false, or replacing the highest wire true at
-- a singleton by a copy of that input) CHANGE the computed function, and that both preserve
-- size, so minimality cannot be spent on a size contradiction: it has to be used inside the
-- function-preservation argument.  The cut below is exactly that reading.
--
--   leastSizeMemberExists   -- a nonempty class of circuits has a member of least size
--   cleanCopyExists         -- every fan-in-two AND/OR circuit has a wire-for-wire copy of the
--                              same size whose AND gates read either nothing or two DISTINCT
--                              wires (the `clean` move: a gate reading [a] or [a,a] becomes an
--                              OR with the same inputs; size-, wire- and function-preserving)
--   leastCleanCircuitIsPairClean
--                           -- the open core: a LEAST-size circuit of the class, already in
--                              that normal form, has no AND gate true at a non-incident pair
--
-- The first two are the normal form and are already carried out in the predecessor's work; the
-- third is the part the normal form does not control, where 4-cycle-freeness and the counting
-- must do their work.
theorem PEqualNP.Outside.R_meta_3457_1
    (leastSizeMemberExists : ∀ (Nice : PEqualNP.CircuitLowerBounds.Circuit → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), Nice C → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, Nice D ∧ ∀ E : PEqualNP.CircuitLowerBounds.Circuit, Nice E → D.size ≤ E.size)
    (cleanCopyExists : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.output = C.output ∧ D.size = C.size ∧ (∀ j : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs = (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs) ∧ (∀ j : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op) ∧ (∀ x : List Bool, D.wires x = C.wires x) ∧ ∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs = [] ∨ ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs = [a, b] ∧ a ≠ b)
    (leastCleanCircuitIsPairClean : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Nice : PEqualNP.CircuitLowerBounds.Circuit → Prop), (∀ E : PEqualNP.CircuitLowerBounds.Circuit, Nice E ↔ (PEqualNP.MetaComplexity.Monotone2 E ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) E ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) E z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ ∀ j < E.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt E j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (E.wires (List.ofFn (fun kf : Fin (N + N) => decide (kf = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (E.wires (List.ofFn (fun kg : Fin (N + N) => decide (kg = Fin.natAdd N l)))).getD (N + N + j) false = false)) → (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, Nice D → (∀ E : PEqualNP.CircuitLowerBounds.Circuit, Nice E → D.size ≤ E.size) → (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs = [] ∨ ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs = [a, b] ∧ a ≠ b) → ∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (C.wires (List.ofFn (fun kf : Fin (N + N) => decide (kf = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (C.wires (List.ofFn (fun kg : Fin (N + N) => decide (kg = Fin.natAdd N l)))).getD (N + N + j) false = false) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  intro N I inst C hK hm hr hf hsing
  -- a least-size member of the class the step's hypotheses describe
  obtain ⟨D, hD, hDmin⟩ :=
    leastSizeMemberExists
      (fun E : PEqualNP.CircuitLowerBounds.Circuit =>
        PEqualNP.MetaComplexity.Monotone2 E ∧
          PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) E ∧
          (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) E z = true ↔
            ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
          ∀ j < E.gates.length,
            (PEqualNP.MetaComplexity.NestedCover.gateAt E j).op =
                PEqualNP.CircuitLowerBounds.GateOp.and →
              (∀ p : Fin N, (E.wires (List.ofFn (fun kf : Fin (N + N) =>
                decide (kf = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
                ∀ l : Fin N, (E.wires (List.ofFn (fun kg : Fin (N + N) =>
                  decide (kg = Fin.natAdd N l)))).getD (N + N + j) false = false)
      C ⟨hm, hr, hf, hsing⟩
  obtain ⟨hDm, hDr, hDf, hDs⟩ := hD
  -- put it in the normal form; the copy has the same wires, so it is still a least member
  obtain ⟨B, hBm, hBo, hBsz, hBin, hBop, hBw, hBshape⟩ := cleanCopyExists D hDm
  have hBlen : B.gates.length = D.gates.length := hBsz
  have hne : ¬ (PEqualNP.CircuitLowerBounds.GateOp.or
      = PEqualNP.CircuitLowerBounds.GateOp.and) :=
    fun hc => PEqualNP.CircuitLowerBounds.GateOp.noConfusion hc
  have hBr : PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) B := by
    intro j hj i hi
    have hjD : j < D.gates.length := Nat.lt_of_lt_of_le hj (Nat.le_of_eq hBlen)
    have hiD : i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs := by
      rw [← hBin j]
      exact hi
    exact hDr j hjD i hiD
  have hBf : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) B z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
    intro z
    have hval : PEqualNP.MetaComplexity.circuitFun (N + N) B z
        = PEqualNP.MetaComplexity.circuitFun (N + N) D z := by
      show (B.wires (List.ofFn z)).getD B.output false
        = (D.wires (List.ofFn z)).getD D.output false
      rw [hBw, hBo]
    rw [hval]
    exact hDf z
  have hBsing : ∀ j < B.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt B j).op =
          PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ p : Fin N, (B.wires (List.ofFn (fun kc : Fin (N + N) =>
          decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
          ∀ l : Fin N, (B.wires (List.ofFn (fun kd : Fin (N + N) =>
            decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false := by
    intro j hj hand
    have hjD : j < D.gates.length := Nat.lt_of_lt_of_le hj (Nat.le_of_eq hBlen)
    have handD : (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op =
        PEqualNP.CircuitLowerBounds.GateOp.and := by
      rcases hBop j with hop | hop
      · exact absurd (hop.symm.trans hand) hne
      · exact hop.symm.trans hand
    obtain ⟨hp, hl⟩ := hDs j hjD handD
    refine ⟨?_, ?_⟩
    · intro p
      rw [hBw]
      exact hp p
    · intro l
      rw [hBw]
      exact hl l
  refine ⟨B, hBm, hBr,
    Nat.le_trans (Nat.le_of_eq hBsz) (hDmin C ⟨hm, hr, hf, hsing⟩), hBf, ?_, hBsing⟩
  exact @leastCleanCircuitIsPairClean N I inst
    (fun E : PEqualNP.CircuitLowerBounds.Circuit =>
      PEqualNP.MetaComplexity.Monotone2 E ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) E ∧
        (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) E z = true ↔
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
        ∀ j < E.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt E j).op =
              PEqualNP.CircuitLowerBounds.GateOp.and →
            (∀ p : Fin N, (E.wires (List.ofFn (fun kf : Fin (N + N) =>
              decide (kf = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
              ∀ l : Fin N, (E.wires (List.ofFn (fun kg : Fin (N + N) =>
                decide (kg = Fin.natAdd N l)))).getD (N + N + j) false = false)
    (fun E => Iff.rfl) hK B ⟨hBm, hBr, hBf, hBsing⟩
    (fun E hE => Nat.le_trans (Nat.le_of_eq hBsz) (hDmin E hE)) hBshape
