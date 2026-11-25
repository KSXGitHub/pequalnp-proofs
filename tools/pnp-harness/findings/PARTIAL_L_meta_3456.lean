import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3456_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- the function the circuit must compute
def F (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (z : Fin (N + N) → Bool) : Prop :=
  ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true

-- one step of the wire fold
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem eval_one (v : Bool) : GateOp.and.eval [v] = GateOp.or.eval [v] := by cases v <;> rfl

theorem eval_two (v : Bool) : GateOp.and.eval [v, v] = GateOp.or.eval [v, v] := by
  cases v <;> rfl

-- an AND gate whose two operands are the same wire, or which reads one wire, is a copy:
-- turn it into an OR gate, which the normalisation condition does not constrain
def fix : Gate → Gate
  | ⟨op, []⟩ => ⟨op, []⟩
  | ⟨_, [a]⟩ => ⟨GateOp.or, [a]⟩
  | ⟨op, [a, b]⟩ => if a = b then ⟨GateOp.or, [a, b]⟩ else ⟨op, [a, b]⟩
  | ⟨op, l⟩ => ⟨op, l⟩

theorem fix_nil (op : GateOp) : fix ⟨op, []⟩ = ⟨op, []⟩ := rfl

theorem fix_one (op : GateOp) (a : ℕ) : fix ⟨op, [a]⟩ = ⟨GateOp.or, [a]⟩ := rfl

theorem fix_two_eq (op : GateOp) (a : ℕ) : fix ⟨op, [a, a]⟩ = ⟨GateOp.or, [a, a]⟩ := by
  show (if a = a then (⟨GateOp.or, [a, a]⟩ : Gate) else ⟨op, [a, a]⟩) = _
  simp

theorem fix_two_ne (op : GateOp) (a b : ℕ) (h : ¬ a = b) : fix ⟨op, [a, b]⟩ = ⟨op, [a, b]⟩ := by
  show (if a = b then (⟨GateOp.or, [a, b]⟩ : Gate) else ⟨op, [a, b]⟩) = _
  simp [h]

theorem fix_inputs : ∀ g : Gate, (fix g).inputs = g.inputs
  | ⟨_, []⟩ => rfl
  | ⟨_, [_]⟩ => rfl
  | ⟨op, [a, b]⟩ => by
      by_cases h : a = b
      · subst h; rw [fix_two_eq]
      · rw [fix_two_ne op a b h]
  | ⟨_, _ :: _ :: _ :: _⟩ => rfl

theorem fix_op : ∀ g : Gate, (fix g).op = GateOp.or ∨ (fix g).op = g.op
  | ⟨_, []⟩ => Or.inr rfl
  | ⟨_, [_]⟩ => Or.inl rfl
  | ⟨op, [a, b]⟩ => by
      by_cases h : a = b
      · subst h; rw [fix_two_eq]; exact Or.inl rfl
      · rw [fix_two_ne op a b h]; exact Or.inr rfl
  | ⟨_, _ :: _ :: _ :: _⟩ => Or.inr rfl

theorem fix_step (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (w : List Bool) :
    step w (fix g) = step w g := by
  rcases g with ⟨op, l⟩
  match l with
  | [] => rfl
  | [a] =>
      rw [fix_one]
      rcases hop with h | h
      · have h' : op = GateOp.and := h
        subst h'
        show w ++ [GateOp.or.eval [w.getD a false]] = w ++ [GateOp.and.eval [w.getD a false]]
        rw [eval_one]
      · have h' : op = GateOp.or := h
        subst h'
        rfl
  | [a, b] =>
      by_cases hab : a = b
      · subst hab
        rw [fix_two_eq]
        rcases hop with h | h
        · have h' : op = GateOp.and := h
          subst h'
          show w ++ [GateOp.or.eval [w.getD a false, w.getD a false]]
            = w ++ [GateOp.and.eval [w.getD a false, w.getD a false]]
          rw [eval_two]
        · have h' : op = GateOp.or := h
          subst h'
          rfl
      · rw [fix_two_ne op a b hab]
  | _ :: _ :: _ :: _ => rfl

theorem foldl_fix (gs : List Gate) (hall : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w : List Bool, (gs.map fix).foldl step w = gs.foldl step w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
      intro w
      have h1 : step w (fix g) = step w g := fix_step g (hall g (by simp)) w
      show (gs.map fix).foldl step (step w (fix g)) = gs.foldl step (step w g)
      rw [h1]
      exact ih (fun h hh => hall h (by simp [hh])) _

-- the cleaned circuit
def clean (C : Circuit) : Circuit := ⟨C.gates.map fix, C.output⟩

theorem clean_len (C : Circuit) : (clean C).gates.length = C.gates.length :=
  List.length_map _

theorem clean_size (C : Circuit) : (clean C).size = C.size :=
  List.length_map _

theorem clean_wires (C : Circuit) (hm : Monotone2 C) (x : List Bool) :
    (clean C).wires x = C.wires x := by
  show (C.gates.map fix).foldl step x = C.gates.foldl step x
  refine foldl_fix C.gates (fun g hg => ?_) x
  have h := (hm g hg).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  exact h

theorem clean_gateAt (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt (clean C) j = fix (gateAt C j) := by
  have h1 : gateAt (clean C) j = (C.gates.map fix).getD j ⟨GateOp.or, []⟩ := rfl
  have h2 : gateAt C j = C.gates.getD j ⟨GateOp.or, []⟩ := rfl
  rw [h1, h2, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj),
    List.getD_eq_getElem _ _ hj, List.getElem_map]

theorem clean_mono (C : Circuit) (hm : Monotone2 C) : Monotone2 (clean C) := by
  intro g hg
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hg
  refine ⟨?_, ?_⟩
  · rcases fix_op h with hop | hop
    · rw [hop]; simp
    · rw [hop]; exact (hm h hh).1
  · rw [fix_inputs]; exact (hm h hh).2

theorem clean_reads (N : ℕ) (C : Circuit) (hr : ReadsBack N C) : ReadsBack N (clean C) := by
  intro j hj i hi
  have hj' : j < C.gates.length := by rw [clean_len] at hj; exact hj
  rw [clean_gateAt C j hj', fix_inputs] at hi
  exact hr j hj' i hi

-- after cleaning, an AND gate reads either no wire or two distinct wires
theorem clean_and_shape (C : Circuit) (hm : Monotone2 C) (j : ℕ) (hj : j < C.gates.length)
    (hand : (gateAt (clean C) j).op = GateOp.and) :
    (gateAt (clean C) j).inputs = [] ∨
      ∃ a b : ℕ, (gateAt (clean C) j).inputs = [a, b] ∧ ¬ a = b := by
  rw [clean_gateAt C j hj] at hand ⊢
  rcases hg : gateAt C j with ⟨op, l⟩
  match l with
  | [] => exact Or.inl (by rw [fix_nil])
  | [a] =>
      rw [hg, fix_one] at hand
      exact absurd hand (by simp)
  | [a, b] =>
      by_cases hab : a = b
      · subst hab
        rw [hg, fix_two_eq] at hand
        exact absurd hand (by simp)
      · exact Or.inr ⟨a, b, by rw [fix_two_ne op a b hab], hab⟩
  | c :: d :: e :: t =>
      have hlen : (gateAt C j).inputs.length ≤ 2 := by
        have : gateAt C j ∈ C.gates := by
          have h2 : gateAt C j = C.gates.getD j ⟨GateOp.or, []⟩ := rfl
          rw [h2, List.getD_eq_getElem _ _ hj]
          exact List.getElem_mem hj
        exact (hm _ this).2
      rw [hg] at hlen
      simp at hlen

-- the project's repair move: force gate c to the constant false
def kill (C : Circuit) (c : ℕ) : Circuit := ⟨C.gates.set c ⟨GateOp.or, []⟩, C.output⟩

theorem mem_set_aux {α : Type} : ∀ (l : List α) (i : ℕ) (a b : α), b ∈ l.set i a → b = a ∨ b ∈ l
  | [], _, _, _, h => absurd h (by simp)
  | x :: xs, 0, a, b, h => by
      rcases List.mem_cons.1 h with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (List.mem_cons_of_mem _ h1)
  | x :: xs, i + 1, a, b, h => by
      rcases List.mem_cons.1 h with h1 | h1
      · exact Or.inr (by rw [h1]; exact List.mem_cons_self)
      · rcases mem_set_aux xs i a b h1 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (List.mem_cons_of_mem _ h2)

theorem kill_len (C : Circuit) (c : ℕ) : (kill C c).gates.length = C.gates.length :=
  List.length_set

theorem kill_size (C : Circuit) (c : ℕ) : (kill C c).size = C.size :=
  List.length_set

theorem kill_mono (C : Circuit) (c : ℕ) (hm : Monotone2 C) : Monotone2 (kill C c) := by
  intro g hg
  rcases mem_set_aux C.gates c ⟨GateOp.or, []⟩ g hg with h | h
  · rw [h]; exact ⟨by simp, by simp⟩
  · exact hm g h

theorem kill_gateAt (C : Circuit) (c j : ℕ) (hj : j < C.gates.length) :
    gateAt (kill C c) j = if c = j then ⟨GateOp.or, []⟩ else gateAt C j := by
  have h1 : gateAt (kill C c) j = (C.gates.set c ⟨GateOp.or, []⟩).getD j ⟨GateOp.or, []⟩ := rfl
  have h2 : gateAt C j = C.gates.getD j ⟨GateOp.or, []⟩ := rfl
  rw [h1, h2, List.getD_eq_getElem _ _ (by rw [List.length_set]; exact hj),
    List.getD_eq_getElem _ _ hj, List.getElem_set]

theorem kill_reads (N : ℕ) (C : Circuit) (c : ℕ) (hr : ReadsBack N C) :
    ReadsBack N (kill C c) := by
  intro j hj i hi
  have hj' : j < C.gates.length := by rw [kill_len] at hj; exact hj
  rw [kill_gateAt C c j hj'] at hi
  by_cases h : c = j
  · rw [if_pos h] at hi; exact absurd hi (by simp)
  · rw [if_neg h] at hi; exact hr j hj' i hi

-- a minimum-size circuit computing the same function
theorem minimal_exists (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hm : Monotone2 C) (hr : ReadsBack (N + N) C)
    (hf : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔ F N I z) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔ F N I z) ∧
      (∀ E : Circuit, Monotone2 E → ReadsBack (N + N) E →
        (∀ z : Fin (N + N) → Bool, circuitFun (N + N) E z = true ↔ F N I z) →
        D.size ≤ E.size) := by
  classical
  have hex : ∃ k, ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size = k ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔ F N I z) :=
    ⟨C.size, C, hm, hr, rfl, hf⟩
  obtain ⟨D, hD1, hD2, hDsz, hD4⟩ := Nat.find_spec hex
  refine ⟨D, hD1, hD2, ?_, hD4, ?_⟩
  · rw [hDsz]; exact Nat.find_min' hex ⟨C, hm, hr, rfl, hf⟩
  · intro E hE1 hE2 hE3
    rw [hDsz]; exact Nat.find_min' hex ⟨E, hE1, hE2, rfl, hE3⟩

end PEqualNP.Outside.L_meta_3456_aux

open PEqualNP.Outside.L_meta_3456_aux

theorem PEqualNP.Outside.L_meta_3456 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  intro N I _ C hK hm hr hf
  by_cases hI : ∃ p l : Fin N, I p l
  case neg =>
    -- no incident pair at all (in particular N = 0): the empty circuit with an output wire
    -- past the inputs computes the constant false and has no gate to normalise
    refine ⟨⟨[], N + N⟩, ?_, ?_, Nat.zero_le _, ?_, ?_⟩
    · intro g hg; exact absurd hg (by simp)
    · intro j hj; exact absurd hj (by simp)
    · intro z
      have hval : PEqualNP.MetaComplexity.circuitFun (N + N)
          (⟨[], N + N⟩ : PEqualNP.CircuitLowerBounds.Circuit) z = false := by
        show (List.ofFn z).getD (N + N) false = false
        rw [List.getD_eq_default]
        rw [List.length_ofFn]
      rw [hval]
      constructor
      · intro h; exact absurd h (by simp)
      · intro h
        obtain ⟨p, l, hpl, _, _⟩ := h
        exact absurd ⟨p, l, hpl⟩ hI
    · intro j hj; exact absurd hj (by simp)
  obtain ⟨D, hD1, hD2, hDle, hD4, hDmin⟩ := minimal_exists N I C hm hr hf
  refine ⟨clean D, clean_mono D hD1, clean_reads (N + N) D hD2,
    le_trans (le_of_eq (clean_size D)) hDle, ?_, ?_⟩
  · intro z
    have h1 : PEqualNP.MetaComplexity.circuitFun (N + N) (clean D) z =
        PEqualNP.MetaComplexity.circuitFun (N + N) D z := by
      show ((clean D).wires (List.ofFn z)).getD D.output false
        = (D.wires (List.ofFn z)).getD D.output false
      rw [clean_wires D hD1]
    rw [h1]
    exact hD4 z
  · intro j hj hand
    have hj' : j < D.gates.length := by rw [clean_len] at hj; exact hj
    have hshape := clean_and_shape D hD1 j hj' hand
    -- OPEN. By clean_and_shape, gate j of the cleaned minimum circuit is either a zero-input
    -- AND (the constant true) or an AND of two DISTINCT wires. In the first case a strictly
    -- smaller circuit must be produced (a constant wire has to be deleted, which shifts
    -- indices); in the second the two operands have a common singleton, and the repair move
    -- kill (clean D) j only keeps the computed function for a minimum circuit -- that is the
    -- open part of the step (see zz_scratch2_3456 for a circuit where it fails).
    refine ⟨?_, ?_⟩
    · intro p
      sorry
    · intro l
      sorry
