import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2571

open PEqualNP.CircuitLowerBounds

-- The 44-gate monotone circuit: for each of the nine points p with p < 12 and p outside
-- [0, 2, 8], an OR of its four incident lines (three gates) and an AND with the point
-- (one gate), then an OR chain over the nine terms.
def c1 : Circuit := { gates := [⟨GateOp.or, [13, 19]⟩, ⟨GateOp.or, [23, 24]⟩, ⟨GateOp.or, [25, 26]⟩, ⟨GateOp.and, [1, 27]⟩, ⟨GateOp.or, [17, 21]⟩, ⟨GateOp.or, [22, 24]⟩, ⟨GateOp.or, [29, 30]⟩, ⟨GateOp.and, [3, 31]⟩, ⟨GateOp.or, [16, 20]⟩, ⟨GateOp.or, [21, 23]⟩, ⟨GateOp.or, [33, 34]⟩, ⟨GateOp.and, [4, 35]⟩, ⟨GateOp.or, [15, 19]⟩, ⟨GateOp.or, [20, 22]⟩, ⟨GateOp.or, [37, 38]⟩, ⟨GateOp.and, [5, 39]⟩, ⟨GateOp.or, [14, 18]⟩, ⟨GateOp.or, [19, 21]⟩, ⟨GateOp.or, [41, 42]⟩, ⟨GateOp.and, [6, 43]⟩, ⟨GateOp.or, [13, 17]⟩, ⟨GateOp.or, [18, 20]⟩, ⟨GateOp.or, [45, 46]⟩, ⟨GateOp.and, [7, 47]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.or, [18, 24]⟩, ⟨GateOp.or, [49, 50]⟩, ⟨GateOp.and, [9, 51]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.or, [17, 23]⟩, ⟨GateOp.or, [53, 54]⟩, ⟨GateOp.and, [10, 55]⟩, ⟨GateOp.or, [13, 14]⟩, ⟨GateOp.or, [16, 22]⟩, ⟨GateOp.or, [57, 58]⟩, ⟨GateOp.and, [11, 59]⟩, ⟨GateOp.or, [28, 32]⟩, ⟨GateOp.or, [61, 36]⟩, ⟨GateOp.or, [62, 40]⟩, ⟨GateOp.or, [63, 44]⟩, ⟨GateOp.or, [64, 48]⟩, ⟨GateOp.or, [65, 52]⟩, ⟨GateOp.or, [66, 56]⟩, ⟨GateOp.or, [67, 60]⟩], output := 68 }

theorem ofFn25 (x : Fin 25 -> Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24] := by
  simp [List.ofFn_succ]

set_option maxHeartbeats 2000000 in
theorem e1 (x : Fin 25 -> Bool) : c1.eval (List.ofFn x) = ((x 1 && ((x 13 || x 19) || (x 23 || x 24))) || (x 3 && ((x 17 || x 21) || (x 22 || x 24))) || (x 4 && ((x 16 || x 20) || (x 21 || x 23))) || (x 5 && ((x 15 || x 19) || (x 20 || x 22))) || (x 6 && ((x 14 || x 18) || (x 19 || x 21))) || (x 7 && ((x 13 || x 17) || (x 18 || x 20))) || (x 9 && ((x 15 || x 16) || (x 18 || x 24))) || (x 10 && ((x 14 || x 15) || (x 17 || x 23))) || (x 11 && ((x 13 || x 14) || (x 16 || x 22)))) := by
  rw [ofFn25]
  simp [c1, Circuit.eval, Circuit.wires, GateOp.eval]

theorem f1 : PEqualNP.MetaComplexity.Monotone2 c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

-- Fin 25 numerals have the value they look like.
theorem fv (a b : Fin 25) (h : (a : ℕ) = (b : ℕ)) : a = b := Fin.ext h

theorem v1 : (((1 : Fin 25)) : ℕ) = 1 := by decide
theorem v2 : (((2 : Fin 25)) : ℕ) = 2 := by decide
theorem v3 : (((3 : Fin 25)) : ℕ) = 3 := by decide
theorem v4 : (((4 : Fin 25)) : ℕ) = 4 := by decide
theorem v5 : (((5 : Fin 25)) : ℕ) = 5 := by decide
theorem v6 : (((6 : Fin 25)) : ℕ) = 6 := by decide
theorem v7 : (((7 : Fin 25)) : ℕ) = 7 := by decide
theorem v8 : (((8 : Fin 25)) : ℕ) = 8 := by decide
theorem v9 : (((9 : Fin 25)) : ℕ) = 9 := by decide
theorem v10 : (((10 : Fin 25)) : ℕ) = 10 := by decide
theorem v11 : (((11 : Fin 25)) : ℕ) = 11 := by decide
theorem v12 : (((12 : Fin 25)) : ℕ) = 12 := by decide
theorem v13 : (((13 : Fin 25)) : ℕ) = 13 := by decide
theorem v14 : (((14 : Fin 25)) : ℕ) = 14 := by decide
theorem v15 : (((15 : Fin 25)) : ℕ) = 15 := by decide
theorem v16 : (((16 : Fin 25)) : ℕ) = 16 := by decide
theorem v17 : (((17 : Fin 25)) : ℕ) = 17 := by decide
theorem v18 : (((18 : Fin 25)) : ℕ) = 18 := by decide
theorem v19 : (((19 : Fin 25)) : ℕ) = 19 := by decide
theorem v20 : (((20 : Fin 25)) : ℕ) = 20 := by decide
theorem v21 : (((21 : Fin 25)) : ℕ) = 21 := by decide
theorem v22 : (((22 : Fin 25)) : ℕ) = 22 := by decide
theorem v23 : (((23 : Fin 25)) : ℕ) = 23 := by decide
theorem v24 : (((24 : Fin 25)) : ℕ) = 24 := by decide

set_option maxHeartbeats 4000000 in
theorem s1 (x : Fin 25 -> Bool) : ((x 1 && ((x 13 || x 19) || (x 23 || x 24))) || (x 3 && ((x 17 || x 21) || (x 22 || x 24))) || (x 4 && ((x 16 || x 20) || (x 21 || x 23))) || (x 5 && ((x 15 || x 19) || (x 20 || x 22))) || (x 6 && ((x 14 || x 18) || (x 19 || x 21))) || (x 7 && ((x 13 || x 17) || (x 18 || x 20))) || (x 9 && ((x 15 || x 16) || (x 18 || x 24))) || (x 10 && ((x 14 || x 15) || (x 17 || x 23))) || (x 11 && ((x 13 || x 14) || (x 16 || x 22)))) = Bool.true <-> (∃ (x4 : Fin (25 : ℕ)) (x5 : Fin (25 : ℕ)), ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ↑x4 ∉ [(0 : ℕ), (2 : ℕ), (8 : ℕ)] ∧ x x4 = Bool.true ∧ x x5 = Bool.true) := by
  constructor
  . intro h
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ((((((((h|h)|h)|h)|h)|h)|h)|h)|h) <;> obtain ⟨hp, hl⟩ := h <;> rcases hl with (hl|hl)|(hl|hl)
    exacts [⟨1, 13, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨1, 19, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨1, 23, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨1, 24, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨3, 17, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨3, 21, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨3, 22, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨3, 24, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨4, 16, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨4, 20, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨4, 21, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨4, 23, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨5, 15, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨5, 19, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨5, 20, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨5, 22, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨6, 14, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨6, 18, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨6, 19, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨6, 21, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨7, 13, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨7, 17, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨7, 18, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨7, 20, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨9, 15, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨9, 16, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨9, 18, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨9, 24, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨10, 14, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨10, 15, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨10, 17, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨10, 23, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨11, 13, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨11, 14, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨11, 16, by decide, by decide, by decide, by decide, hp, hl⟩, ⟨11, 22, by decide, by decide, by decide, by decide, hp, hl⟩]
  . rintro ⟨p, l, h1, h2, h3, h4, hp, hl⟩
    have hpv := p.isLt
    have hlv := l.isLt
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h3 h4
    obtain ⟨n0, n2, n8⟩ := h4
    have hp9 : (p : ℕ) = 1 ∨ (p : ℕ) = 3 ∨ (p : ℕ) = 4 ∨ (p : ℕ) = 5 ∨ (p : ℕ) = 6 ∨ (p : ℕ) = 7 ∨ (p : ℕ) = 9 ∨ (p : ℕ) = 10 ∨ (p : ℕ) = 11 := by omega
    rcases hp9 with hv|hv|hv|hv|hv|hv|hv|hv|hv
    . have hl4 : (l : ℕ) = 13 ∨ (l : ℕ) = 19 ∨ (l : ℕ) = 23 ∨ (l : ℕ) = 24 := by rcases h3 with h3|h3|h3|h3 <;> omega
      rw [fv p 1 (by rw [hv, v1])] at hp
      rcases hl4 with hw|hw|hw|hw
      . rw [fv l 13 (by rw [hw, v13])] at hl
        simp [hp, hl]
      . rw [fv l 19 (by rw [hw, v19])] at hl
        simp [hp, hl]
      . rw [fv l 23 (by rw [hw, v23])] at hl
        simp [hp, hl]
      . rw [fv l 24 (by rw [hw, v24])] at hl
        simp [hp, hl]
    . have hl4 : (l : ℕ) = 17 ∨ (l : ℕ) = 21 ∨ (l : ℕ) = 22 ∨ (l : ℕ) = 24 := by rcases h3 with h3|h3|h3|h3 <;> omega
      rw [fv p 3 (by rw [hv, v3])] at hp
      rcases hl4 with hw|hw|hw|hw
      . rw [fv l 17 (by rw [hw, v17])] at hl
        simp [hp, hl]
      . rw [fv l 21 (by rw [hw, v21])] at hl
        simp [hp, hl]
      . rw [fv l 22 (by rw [hw, v22])] at hl
        simp [hp, hl]
      . rw [fv l 24 (by rw [hw, v24])] at hl
        simp [hp, hl]
    . have hl4 : (l : ℕ) = 16 ∨ (l : ℕ) = 20 ∨ (l : ℕ) = 21 ∨ (l : ℕ) = 23 := by rcases h3 with h3|h3|h3|h3 <;> omega
      rw [fv p 4 (by rw [hv, v4])] at hp
      rcases hl4 with hw|hw|hw|hw
      . rw [fv l 16 (by rw [hw, v16])] at hl
        simp [hp, hl]
      . rw [fv l 20 (by rw [hw, v20])] at hl
        simp [hp, hl]
      . rw [fv l 21 (by rw [hw, v21])] at hl
        simp [hp, hl]
      . rw [fv l 23 (by rw [hw, v23])] at hl
        simp [hp, hl]
    . have hl4 : (l : ℕ) = 15 ∨ (l : ℕ) = 19 ∨ (l : ℕ) = 20 ∨ (l : ℕ) = 22 := by rcases h3 with h3|h3|h3|h3 <;> omega
      rw [fv p 5 (by rw [hv, v5])] at hp
      rcases hl4 with hw|hw|hw|hw
      . rw [fv l 15 (by rw [hw, v15])] at hl
        simp [hp, hl]
      . rw [fv l 19 (by rw [hw, v19])] at hl
        simp [hp, hl]
      . rw [fv l 20 (by rw [hw, v20])] at hl
        simp [hp, hl]
      . rw [fv l 22 (by rw [hw, v22])] at hl
        simp [hp, hl]
    . have hl4 : (l : ℕ) = 14 ∨ (l : ℕ) = 18 ∨ (l : ℕ) = 19 ∨ (l : ℕ) = 21 := by rcases h3 with h3|h3|h3|h3 <;> omega
      rw [fv p 6 (by rw [hv, v6])] at hp
      rcases hl4 with hw|hw|hw|hw
      . rw [fv l 14 (by rw [hw, v14])] at hl
        simp [hp, hl]
      . rw [fv l 18 (by rw [hw, v18])] at hl
        simp [hp, hl]
      . rw [fv l 19 (by rw [hw, v19])] at hl
        simp [hp, hl]
      . rw [fv l 21 (by rw [hw, v21])] at hl
        simp [hp, hl]
    . have hl4 : (l : ℕ) = 13 ∨ (l : ℕ) = 17 ∨ (l : ℕ) = 18 ∨ (l : ℕ) = 20 := by rcases h3 with h3|h3|h3|h3 <;> omega
      rw [fv p 7 (by rw [hv, v7])] at hp
      rcases hl4 with hw|hw|hw|hw
      . rw [fv l 13 (by rw [hw, v13])] at hl
        simp [hp, hl]
      . rw [fv l 17 (by rw [hw, v17])] at hl
        simp [hp, hl]
      . rw [fv l 18 (by rw [hw, v18])] at hl
        simp [hp, hl]
      . rw [fv l 20 (by rw [hw, v20])] at hl
        simp [hp, hl]
    . have hl4 : (l : ℕ) = 15 ∨ (l : ℕ) = 16 ∨ (l : ℕ) = 18 ∨ (l : ℕ) = 24 := by rcases h3 with h3|h3|h3|h3 <;> omega
      rw [fv p 9 (by rw [hv, v9])] at hp
      rcases hl4 with hw|hw|hw|hw
      . rw [fv l 15 (by rw [hw, v15])] at hl
        simp [hp, hl]
      . rw [fv l 16 (by rw [hw, v16])] at hl
        simp [hp, hl]
      . rw [fv l 18 (by rw [hw, v18])] at hl
        simp [hp, hl]
      . rw [fv l 24 (by rw [hw, v24])] at hl
        simp [hp, hl]
    . have hl4 : (l : ℕ) = 14 ∨ (l : ℕ) = 15 ∨ (l : ℕ) = 17 ∨ (l : ℕ) = 23 := by rcases h3 with h3|h3|h3|h3 <;> omega
      rw [fv p 10 (by rw [hv, v10])] at hp
      rcases hl4 with hw|hw|hw|hw
      . rw [fv l 14 (by rw [hw, v14])] at hl
        simp [hp, hl]
      . rw [fv l 15 (by rw [hw, v15])] at hl
        simp [hp, hl]
      . rw [fv l 17 (by rw [hw, v17])] at hl
        simp [hp, hl]
      . rw [fv l 23 (by rw [hw, v23])] at hl
        simp [hp, hl]
    . have hl4 : (l : ℕ) = 13 ∨ (l : ℕ) = 14 ∨ (l : ℕ) = 16 ∨ (l : ℕ) = 22 := by rcases h3 with h3|h3|h3|h3 <;> omega
      rw [fv p 11 (by rw [hv, v11])] at hp
      rcases hl4 with hw|hw|hw|hw
      . rw [fv l 13 (by rw [hw, v13])] at hl
        simp [hp, hl]
      . rw [fv l 14 (by rw [hw, v14])] at hl
        simp [hp, hl]
      . rw [fv l 16 (by rw [hw, v16])] at hl
        simp [hp, hl]
      . rw [fv l 22 (by rw [hw, v22])] at hl
        simp [hp, hl]

end PEqualNP.Outside.L_meta_2571


-- PARTIAL. Everything except the last conjunct is proved below. The last conjunct asks for a
-- wire carrying z13 or z15 or z21 (the star of the thirteenth point, needed by the sibling
-- step). On inputs where all nine point bits are false the circuit value is false, so that
-- wire must agree with z13 or z15 or z21 there exactly; hence some gate must be an OR whose
-- two arguments cover two of the three lines 13, 15, 21 and vanish on every other line. No
-- point star contains two of those three lines (they are a parallel class of AG(2,3)), so no
-- such wire is available for free and two further gates are needed: 46 in all, over budget.
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_meta_2571 : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (45 : ℕ) ∧ x1.output < (25 : ℕ) + x1.size ∧ x2 < (25 : ℕ) + x1.size ∧ ∀ (x3 : Fin (25 : ℕ) → Bool), (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (25 : ℕ)) (x5 : Fin (25 : ℕ)), ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ↑x4 ∉ [(0 : ℕ), (2 : ℕ), (8 : ℕ)] ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) ∧ (x1.eval (List.ofFn x3) = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ)))) := by
  refine ⟨PEqualNP.Outside.L_meta_2571.c1, 68, PEqualNP.Outside.L_meta_2571.f1, by decide,
    by decide, by decide, fun x3 => ⟨?_, ?_⟩⟩
  . rw [PEqualNP.Outside.L_meta_2571.e1 x3]
    exact PEqualNP.Outside.L_meta_2571.s1 x3
  . sorry

