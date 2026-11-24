import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1000000 in
theorem zz_refute_L_meta_3628 : ¬ (have x1 : List PEqualNP.CircuitLowerBounds.Gate → ℕ := fun (x1 : List PEqualNP.CircuitLowerBounds.Gate) => List.countP (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x3 : ℕ) => Bool.true) Bool.true x2.op) x1; ∀ (x2 : ℕ) (x3 : Fin (x2 + (1 : ℕ))) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : List (Fin (x2 + (1 : ℕ)))),   PEqualNP.MetaComplexity.FanInTwo x4 →     have x7 : (Fin (x2 + (1 : ℕ)) → Bool) → Bool := fun (x7 : Fin (x2 + (1 : ℕ)) → Bool) => x4.eval (List.map x7 x5);     (∃ (x8 : Fin (x2 + (1 : ℕ)) → Bool), x7 (Function.update x8 x3 Bool.true) ≠ x7 (Function.update x8 x3 Bool.false)) → (∃ (x9 : Fin x2 → Bool) (x10 : Fin x2 → Bool), x7 (x3.insertNth Bool.false x9) ≠ x7 (x3.insertNth Bool.false x10)) → ∀ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x10 → x1 x10.gates + (1 : ℕ) ≤ x1 x4.gates → PEqualNP.MetaComplexity.circuitFun x2 x10 = fun (x13 : Fin x2 → Bool) => x7 (x3.insertNth Bool.false x13)) := by
  intro h
  have key := h 1 0 ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩], 2⟩ [0, 1]
    (by intro g hg; simp at hg; subst hg; refine ⟨by simp, by simp⟩)
    ⟨(fun _ => false), by decide⟩
    ⟨(fun _ => true), (fun _ => false), by decide⟩
    ⟨[], 5⟩
    (by intro g hg; simp at hg)
    (by decide)
  have bad := congrFun key (fun _ => true)
  simp [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
    PEqualNP.CircuitLowerBounds.Circuit.wires, PEqualNP.CircuitLowerBounds.GateOp.eval] at bad
