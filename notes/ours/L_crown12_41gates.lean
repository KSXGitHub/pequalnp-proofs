import PEqualNP.Defs

/-!
A monotone fan-in-two circuit for the 12 by 12 crown

The crown joins u to v exactly when u and v differ.  The circuit below is
`d u = x u or y u` for each of the twelve indices, then the threshold-two function of the
twelve `d` values, computed by placing the indices on a three by four grid, ORing each row
and each column of the grid, and taking threshold two of the three row values OR threshold
two of the four column values.  On the row `oneEach u v` exactly the `d` with index in the
set of u and v are on, so one of them when u and v agree and two when they differ, and two
distinct indices of the grid differ in their row or in their column.
-/

namespace PEqualNP.Outside.L_meta_18264

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- The crown circuit: 41 gates of AND and OR, each reading two earlier wires. -/
def crownCircuit : Circuit where
  gates :=
    [
    ⟨GateOp.or, [0, 12]⟩,
    ⟨GateOp.or, [1, 13]⟩,
    ⟨GateOp.or, [2, 14]⟩,
    ⟨GateOp.or, [3, 15]⟩,
    ⟨GateOp.or, [4, 16]⟩,
    ⟨GateOp.or, [5, 17]⟩,
    ⟨GateOp.or, [6, 18]⟩,
    ⟨GateOp.or, [7, 19]⟩,
    ⟨GateOp.or, [8, 20]⟩,
    ⟨GateOp.or, [9, 21]⟩,
    ⟨GateOp.or, [10, 22]⟩,
    ⟨GateOp.or, [11, 23]⟩,
    ⟨GateOp.or, [24, 25]⟩,
    ⟨GateOp.or, [26, 27]⟩,
    ⟨GateOp.or, [36, 37]⟩,
    ⟨GateOp.or, [28, 29]⟩,
    ⟨GateOp.or, [30, 31]⟩,
    ⟨GateOp.or, [39, 40]⟩,
    ⟨GateOp.or, [32, 33]⟩,
    ⟨GateOp.or, [34, 35]⟩,
    ⟨GateOp.or, [42, 43]⟩,
    ⟨GateOp.or, [24, 28]⟩,
    ⟨GateOp.or, [45, 32]⟩,
    ⟨GateOp.or, [25, 29]⟩,
    ⟨GateOp.or, [47, 33]⟩,
    ⟨GateOp.or, [26, 30]⟩,
    ⟨GateOp.or, [49, 34]⟩,
    ⟨GateOp.or, [27, 31]⟩,
    ⟨GateOp.or, [51, 35]⟩,
    ⟨GateOp.or, [38, 41]⟩,
    ⟨GateOp.and, [38, 41]⟩,
    ⟨GateOp.and, [53, 44]⟩,
    ⟨GateOp.or, [54, 55]⟩,
    ⟨GateOp.or, [46, 48]⟩,
    ⟨GateOp.and, [46, 48]⟩,
    ⟨GateOp.and, [57, 50]⟩,
    ⟨GateOp.or, [58, 59]⟩,
    ⟨GateOp.or, [57, 50]⟩,
    ⟨GateOp.and, [61, 52]⟩,
    ⟨GateOp.or, [60, 62]⟩,
    ⟨GateOp.or, [56, 63]⟩
    ]
  output := 64

lemma crownCircuit_mono : Monotone2 crownCircuit := by
  intro g hg
  fin_cases hg <;>
    exact ⟨by simp [Set.mem_insert_iff, Set.mem_singleton_iff], by simp⟩

lemma crownCircuit_size : crownCircuit.size ≤ 41 := by
  simp [Circuit.size, crownCircuit]

lemma crownCircuit_represents :
    Represents (fun u v : Fin 12 => decide (u ≠ v)) crownCircuit := by
  decide +kernel

end PEqualNP.Outside.L_meta_18264

theorem PEqualNP.Outside.L_meta_18264 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 12 => decide (u ≠ v)) 41 :=
  ⟨PEqualNP.Outside.L_meta_18264.crownCircuit,
    PEqualNP.Outside.L_meta_18264.crownCircuit_mono,
    PEqualNP.Outside.L_meta_18264.crownCircuit_size,
    PEqualNP.Outside.L_meta_18264.crownCircuit_represents⟩
