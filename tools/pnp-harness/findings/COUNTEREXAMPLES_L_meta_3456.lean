import Mathlib
import PEqualNP.Defs

-- Two concrete witnesses about the repair moves for L-meta-3456.
-- N = 1, I = fun _ _ => True (4-cycle free vacuously), f z = z 0 && z 1.
-- Cbad satisfies every hypothesis of the step, gate 2 is an AND gate true at the point
-- singleton, and forcing that gate to the constant false (Cfix) destroys the function.

namespace zzScratch2_3456

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def Cbad : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.and, [4, 0]⟩,
    ⟨GateOp.and, [5, 1]⟩], 6⟩

def Cfix : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, []⟩, ⟨GateOp.and, [4, 0]⟩,
    ⟨GateOp.and, [5, 1]⟩], 6⟩

-- it is a legal circuit for the step
example : Monotone2 Cbad := by
  intro g hg
  simp only [Cbad, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h <;> subst h <;>
    exact ⟨by simp, by simp⟩

example : ReadsBack (1 + 1) Cbad := by decide

example : ∀ z : Fin (1 + 1) → Bool, circuitFun (1 + 1) Cbad z = true ↔
    ∃ p l : Fin 1, True ∧ z (Fin.castAdd 1 p) = true ∧ z (Fin.natAdd 1 l) = true := by decide

-- gate 2 is an AND gate that is true at the point singleton: the step must repair it
example : (gateAt Cbad 2).op = GateOp.and := rfl

example : (Cbad.wires
    (List.ofFn (fun kc : Fin (1 + 1) => decide (kc = Fin.castAdd 1 (0 : Fin 1))))).getD
      (1 + 1 + 2) false = true := by decide

-- but forcing that gate to the constant false destroys the function
example : circuitFun (1 + 1) Cfix (fun _ => true) = false := by decide

example : circuitFun (1 + 1) Cbad (fun _ => true) = true := by decide

-- second witness, for the other repair move (replace the highest gate that is true at the
-- singleton by a copy of that input): N = 2, I = diagonal, f = x0 y0 or x1 y1.
def Dbad : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [4, 3]⟩, ⟨GateOp.and, [5, 1]⟩, ⟨GateOp.and, [0, 2]⟩,
    ⟨GateOp.or, [6, 7]⟩], 8⟩

def Dcopy : Circuit :=
  ⟨[⟨GateOp.or, [0]⟩, ⟨GateOp.and, [4, 3]⟩, ⟨GateOp.and, [5, 1]⟩, ⟨GateOp.and, [0, 2]⟩,
    ⟨GateOp.or, [6, 7]⟩], 8⟩

example : ReadsBack (2 + 2) Dbad := by decide

example : ∀ z : Fin (2 + 2) → Bool, circuitFun (2 + 2) Dbad z = true ↔
    ∃ p l : Fin 2, p = l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true := by decide

-- gate 0 is the highest wire true at the singleton of point 0, and it is an OR gate
example : (Dbad.wires
    (List.ofFn (fun kc : Fin (2 + 2) => decide (kc = Fin.castAdd 2 (0 : Fin 2))))).getD
      (2 + 2 + 0) false = true := by decide

-- replacing it by a copy of x0 breaks the function at x1 = y1 = 1
example : circuitFun (2 + 2) Dcopy
    (fun k => decide (k = Fin.castAdd 2 (1 : Fin 2) ∨ k = Fin.natAdd 2 (1 : Fin 2))) = false := by
  decide

example : circuitFun (2 + 2) Dbad
    (fun k => decide (k = Fin.castAdd 2 (1 : Fin 2) ∨ k = Fin.natAdd 2 (1 : Fin 2))) = true := by
  decide

end zzScratch2_3456
