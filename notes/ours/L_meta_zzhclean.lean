import PEqualNP.Defs
import PEqualNP.Outside.L_meta_8305

/-!
SCRATCH / AUDIT FILE (not for submission).

Shows that the hypothesis `hclean` of our conditional L-meta-9796 proof is not merely
undischarged but REFUTABLE: as soon as some `Monotone2` circuit computes `f_G` at all, the
statement "every `Monotone2` circuit computing `f_G` has all its AND gates clean on
weight-<=2 inputs" is false. Append a dead AND gate reading the two left-side inputs 0 and 1
(a non-edge, since EL is bipartite from {0..11} to {12..23}): the circuit still computes
`f_G`, is still `Monotone2`, but that gate is true on the weight-2 input {0,1}.

Consequence: the pair-cleanliness hypothesis has to be used in NORMAL-FORM shape
(some circuit of size <= s is clean), not as a property of every circuit.
-/

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_8305

namespace Audit9796

/-- The 44 listed vertex pairs, verbatim from the conditional proof. -/
def EL : List (ℕ × ℕ) :=
  [(0, 12), (0, 16), (0, 22), (1, 13), (1, 17), (1, 23), (2, 12), (2, 13), (2, 14), (2, 18),
   (3, 14), (3, 15), (3, 19), (4, 13), (4, 15), (4, 16), (4, 20), (5, 14), (5, 16), (5, 17),
   (5, 21), (6, 15), (6, 17), (6, 18), (6, 22), (7, 16), (7, 18), (7, 19), (7, 23), (8, 12),
   (8, 17), (8, 19), (8, 20), (9, 18), (9, 20), (9, 21), (10, 13), (10, 19), (10, 21),
   (10, 22), (11, 14), (11, 20), (11, 22), (11, 23)]

def Computes (C : Circuit) : Prop :=
  ∀ x : Fin 24 → Bool, C.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 24, (u.val, v.val) ∈ EL ∧ x u = true ∧ x v = true

/-- Verbatim from the conditional proof. -/
def CleanAnds (gates : List Gate) : Prop :=
  ∀ (i : Fin gates.length) (x : Fin 24 → Bool),
    (x = (fun _ => false) ∨ (∃ u : Fin 24, x = fun z => decide (z = u)) ∨
      (∃ u v : Fin 24, x = fun z => decide (z = u ∨ z = v))) →
    (gates.get i).op = GateOp.and →
    (Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (24 + (i : ℕ)) false = true →
    ∃ u v : Fin 24, (edgeGraph 24 EL).Adj u v ∧ x u = true ∧ x v = true

lemma wires_eq (C : Circuit) (w : List Bool) : C.wires w = C.gates.foldl stepWire w := rfl

lemma wlen (gs : List Gate) (x : Fin 24 → Bool) :
    (gs.foldl stepWire (List.ofFn x)).length = 24 + gs.length := by
  rw [fold_length]; simp

/-- The dead dirty gate: AND of the two left-side inputs 0 and 1, a non-edge. -/
def g0 : Gate := ⟨GateOp.and, [0, 1]⟩

/-- The weight-2 input that lights `g0` up. -/
def xbad : Fin 24 → Bool := fun z => decide (z = 0 ∨ z = 1)

theorem hclean_false (hex : ∃ C : Circuit, Monotone2 C ∧ Computes C) :
    ¬ (∀ C : Circuit, Monotone2 C → Computes C → CleanAnds C.gates) := by
  intro hclean
  obtain ⟨C, hM, hC⟩ := hex
  -- The output wire is a real wire: otherwise `C.eval` is always `false`.
  have hout : C.output < 24 + C.gates.length := by
    by_contra hge
    have hzero : ∀ y : Fin 24 → Bool, C.eval (List.ofFn y) = false := by
      intro y
      show (C.gates.foldl stepWire (List.ofFn y)).getD C.output false = false
      apply List.getD_eq_default
      rw [wlen]; omega
    -- but (0,12) is an edge, so some input evaluates to `true`
    have : C.eval (List.ofFn (fun z : Fin 24 => decide (z = 0 ∨ z = 12))) = true := by
      apply (hC _).mpr
      refine ⟨0, 12, by decide, by decide, by decide⟩
    rw [hzero] at this
    exact absurd this (by simp)
  -- Append the dead dirty AND gate.
  let D : Circuit := ⟨C.gates ++ [g0], C.output⟩
  have hsplit : ∀ w : List Bool,
      (C.gates ++ [g0]).foldl stepWire w
        = (C.gates.foldl stepWire w) ++ [gateBit (C.gates.foldl stepWire w) g0] := by
    intro w; rw [List.foldl_append]; rfl
  have hDmono : Monotone2 D := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hM g h
    · simp only [List.mem_singleton] at h
      subst h
      exact ⟨by simp [g0], by simp [g0]⟩
  have hDeval : ∀ y : Fin 24 → Bool, D.eval (List.ofFn y) = C.eval (List.ofFn y) := by
    intro y
    show ((C.gates ++ [g0]).foldl stepWire (List.ofFn y)).getD C.output false
        = (C.gates.foldl stepWire (List.ofFn y)).getD C.output false
    rw [hsplit, List.getD_append _ _ _ _ (by rw [wlen]; omega)]
  have hDcomputes : Computes D := by
    intro y; rw [hDeval y]; exact hC y
  -- Apply the hypothesis to `D` and read off the appended gate.
  have hclean' := hclean D hDmono hDcomputes
  have hlen : C.gates.length < (C.gates ++ [g0]).length := by simp
  have hidx : ((⟨C.gates.length, hlen⟩ : Fin (C.gates ++ [g0]).length) : ℕ)
      = C.gates.length := rfl
  have hop : ((C.gates ++ [g0]).get ⟨C.gates.length, hlen⟩).op = GateOp.and := by
    simp [List.get_eq_getElem, g0]
  -- Its wire is true on `xbad`.
  have hbit : (Circuit.wires ⟨C.gates ++ [g0], 0⟩ (List.ofFn xbad)).getD
      (24 + C.gates.length) false = true := by
    rw [wires_eq, hsplit, List.getD_append_right]
    · have h0 : (C.gates.foldl stepWire (List.ofFn xbad)).getD 0 false = true := by
        rw [fold_getD_lt _ _ 0 (by simp)]
        simp [xbad]
      have h1 : (C.gates.foldl stepWire (List.ofFn xbad)).getD 1 false = true := by
        rw [fold_getD_lt _ _ 1 (by simp)]
        simp [xbad]
      rw [wlen, Nat.sub_self]
      show gateBit (C.gates.foldl stepWire (List.ofFn xbad)) g0 = true
      unfold gateBit g0
      simp only [List.map_cons, List.map_nil]
      rw [h0, h1]
      rfl
    · rw [wlen]
  obtain ⟨u, v, huv, hu, hv⟩ :=
    hclean' ⟨C.gates.length, hlen⟩ xbad
      (Or.inr (Or.inr ⟨0, 1, rfl⟩)) hop hbit
  -- But 0 and 1 are both on the left side of the bipartition, so they are not adjacent.
  have hu' : u = 0 ∨ u = 1 := by simpa [xbad] using hu
  have hv' : v = 0 ∨ v = 1 := by simpa [xbad] using hv
  have hno : ¬ (edgeGraph 24 EL).Adj u v := by
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl <;> decide
  exact hno huv

end Audit9796
