import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_792
open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem eval_gate (C : Circuit) (x : List Bool) (j : ℕ) (g : Gate) (hj : C.gates[j]? = some g) :
    (C.wires x).getD (x.length + j) false
      = g.op.eval (g.inputs.map fun w =>
          if w < x.length + j then (C.wires x).getD w false else false) := by
  obtain ⟨hjl, hgj⟩ := List.getElem?_eq_some_iff.mp hj
  obtain ⟨pre, post, hpre, hsp⟩ : ∃ pre post : List Gate,
      pre.length = j ∧ C.gates = pre ++ g :: post := by
    refine ⟨C.gates.take j, C.gates.drop (j+1), by simp; omega, ?_⟩
    have := List.take_append_drop j C.gates
    rw [List.drop_eq_getElem_cons hjl, hgj] at this
    exact this.symm
  have hw : C.wires x = wiresFrom post (wiresFrom pre x ++
      [g.op.eval (g.inputs.map fun i => (wiresFrom pre x).getD i false)]) := by
    rw [wires_eq, hsp, wiresFrom_append]; rfl
  have hl0 : (wiresFrom pre x).length = x.length + j := by rw [length_wiresFrom, hpre]
  have hpref : ∀ i, i < x.length + j →
      (C.wires x).getD i false = (wiresFrom pre x).getD i false := by
    intro i hi
    rw [hw, getD_wiresFrom _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)]
  have hv : (C.wires x).getD (x.length + j) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre x).getD i false) := by
    rw [hw, getD_wiresFrom _ _ _ (by simp; omega), ← hl0]
    simp
  rw [hv]
  congr 1
  apply List.map_congr_left
  intro w _
  by_cases h : w < x.length + j
  · rw [if_pos h, hpref w h]
  · rw [if_neg h]
    rw [List.getD_eq_default _ _ (by omega)]

def W {n : ℕ} (C : Circuit) (p : Fin n) (w : ℕ) : Bool :=
  (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false

theorem W_gate {n : ℕ} (C : Circuit) (p : Fin n) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    W C p (n + j) = g.op.eval (g.inputs.map fun w => if w < n + j then W C p w else false) := by
  have := eval_gate C (List.ofFn (fun q : Fin n => decide (q = p))) j g hj
  simpa [W] using this

theorem W_input {n : ℕ} (C : Circuit) (p : Fin n) (w : ℕ) (hw : w < n) :
    W C p w = decide (w = p.val) := by
  have h1 : (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false
      = (List.ofFn (fun q : Fin n => decide (q = p))).getD w false := by
    obtain ⟨t, ht, _⟩ := wiresFrom_start C.gates (List.ofFn (fun q : Fin n => decide (q = p)))
    rw [wires_eq, ht, List.getD_append _ _ _ _ (by simpa using hw)]
  unfold W
  rw [h1]
  simp [List.getD_eq_getElem?_getD, hw, Fin.ext_iff, eq_comm]

theorem card_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    (Finset.univ.filter (fun p : Fin n => W C p w = true)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  rw [W_input C a w hw] at ha
  rw [W_input C b w hw] at hb
  simp at ha hb
  exact Fin.ext (by omega)

open Classical in
noncomputable def sel {n : ℕ} (C : Circuit) (ψ : ℕ → Bool) (j : ℕ) : Finset ℕ :=
  match C.gates[j]? with
  | none => ∅
  | some g =>
    if g.op = GateOp.or then g.inputs.toFinset.filter (fun w => w < n + j ∧ ψ w = false)
    else if h : ∃ w ∈ g.inputs, w < n + j ∧ ψ w = false then {Classical.choose h} else ∅

theorem sel_sub {n : ℕ} (C : Circuit) (ψ : ℕ → Bool) (j w : ℕ) (h : w ∈ sel (n := n) C ψ j) :
    ∃ g, C.gates[j]? = some g ∧ w ∈ g.inputs ∧ w < n + j ∧ ψ w = false := by
  classical
  unfold sel at h
  rcases hg : C.gates[j]? with _ | g
  · rw [hg] at h; simp at h
  · rw [hg] at h
    refine ⟨g, rfl, ?_⟩
    simp only at h
    split_ifs at h with h1 h2
    · simpa using h
    · have := Classical.choose_spec h2
      rw [Finset.mem_singleton] at h
      subst h
      exact ⟨this.1, this.2.1, this.2.2⟩
    · simp at h

theorem sel_card {n : ℕ} (C : Circuit) (ψ : ℕ → Bool) (j : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    (sel (n := n) C ψ j).card ≤ 2 := by
  classical
  unfold sel
  rcases hj : C.gates[j]? with _ | g
  · simp
  · have hgm : g ∈ C.gates := List.mem_of_getElem? hj
    have hl := (hg g hgm).2
    simp only
    split_ifs with h1 h2
    · exact (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans (by omega))
    · simp
    · simp

theorem sel_cover {n : ℕ} (C : Circuit) (ψ : ℕ → Bool) (j : ℕ) (g : Gate)
    (hgj : C.gates[j]? = some g)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hψ : ψ (n + j) = g.op.eval (g.inputs.map fun w => if w < n + j then ψ w else false))
    (h0 : ψ (n + j) = false) (p : Fin n) (hp : W C p (n + j) = true) :
    ∃ c ∈ sel (n := n) C ψ j, W C p c = true := by
  classical
  have hW := W_gate C p j g hgj
  rw [hp] at hW
  rw [h0] at hψ
  have hs : sel (n := n) C ψ j = (if g.op = GateOp.or then
      g.inputs.toFinset.filter (fun w => w < n + j ∧ ψ w = false)
      else if h : ∃ w ∈ g.inputs, w < n + j ∧ ψ w = false then {Classical.choose h} else ∅) := by
    unfold sel; rw [hgj]
  rcases hop with hop | hop
  · have hne : g.op ≠ GateOp.or := by rw [hop]; intro h; cases h
    rw [hop] at hW hψ
    simp only [GateOp.eval] at hW hψ
    have hW' := List.all_eq_true.mp hW.symm
    have hψ' : ¬ ((g.inputs.map fun w => if w < n + j then ψ w else false).all id = true) := by
      rw [← hψ]; simp
    have hall : ∀ w ∈ g.inputs, w < n + j ∧ W C p w = true := by
      intro w hw
      have := hW' _ (List.mem_map.mpr ⟨w, hw, rfl⟩)
      by_cases h : w < n + j
      · simp [h] at this; exact ⟨h, this⟩
      · simp [h] at this
    have hex : ∃ w ∈ g.inputs, w < n + j ∧ ψ w = false := by
      by_contra hcon
      apply hψ'
      rw [List.all_eq_true]
      intro x hx
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
      have h1 := (hall w hw).1
      have h2 : ¬ ψ w = false := fun h => hcon ⟨w, hw, h1, h⟩
      simp [h1]
      simpa using h2
    refine ⟨Classical.choose hex, ?_, ?_⟩
    · rw [hs, if_neg hne, dif_pos hex]; simp
    · exact (hall _ (Classical.choose_spec hex).1).2
  · rw [hop] at hW hψ
    simp only [GateOp.eval] at hW hψ
    have hψ' : ¬ ((g.inputs.map fun w => if w < n + j then ψ w else false).any id = true) := by
      rw [← hψ]; simp
    obtain ⟨_, hx, hwt⟩ := List.any_eq_true.mp hW.symm
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
    by_cases h : w < n + j
    · simp only [h, if_true] at hwt
      have hψw : ψ w = false := by
        by_contra hc
        apply hψ'
        exact List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨w, hw, rfl⟩, by simp [h]; simpa using hc⟩
      refine ⟨w, ?_, hwt⟩
      rw [hs, if_pos hop]
      simp [hw, h, hψw]
    · simp [h] at hwt

theorem main {n : ℕ} (C : Circuit) (Q : Finset ℕ) (ψ : ℕ → Bool) (r : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hr : r ∈ Q)
    (hψ : ∀ j ∈ Q, ∀ g : Gate, C.gates[j]? = some g →
      ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false)))
    (hQg : ∀ j ∈ Q, ∃ g, C.gates[j]? = some g)
    (hex : ∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g → ∀ w ∈ g.inputs, w < n + j →
      ψ w = false → (∀ j' ∈ Q, w ≠ n + j') →
      (Finset.univ.filter (fun p : Fin n => W C p w = true)).card ≤ 1)
    (hr0 : ψ (n + r) = false) :
    (Finset.univ.filter (fun p : Fin n => W C p (n + r) = true)).card ≤ Q.card + 1 := by
  classical
  let edge : ℕ → ℕ → Prop := fun a b => ∃ j ∈ Q, a = n + j ∧ b ∈ sel (n := n) C ψ j
  let N : ℕ → Prop := fun w => Relation.ReflTransGen edge (n + r) w
  have hNψ : ∀ w, N w → ψ w = false := by
    intro w hw
    induction hw with
    | refl => exact hr0
    | tail _ he _ =>
      obtain ⟨j, _, _, hb⟩ := he
      exact (sel_sub C ψ j _ hb).choose_spec.2.2.2
  have hNc : ∀ w, N w → w = n + r ∨ ∃ j ∈ Q, N (n + j) ∧ w ∈ sel (n := n) C ψ j := by
    intro w hw
    cases hw with
    | refl => exact Or.inl rfl
    | tail hb he =>
      obtain ⟨j, hj, rfl, hw⟩ := he
      exact Or.inr ⟨j, hj, hb, hw⟩
  let Qn : Finset ℕ := Q.filter (fun j => N (n + j))
  let M : Finset ℕ := Qn.biUnion (fun j => sel (n := n) C ψ j)
  let E : Finset ℕ := M.filter (fun w => ∀ j ∈ Q, w ≠ n + j)
  have hMN : ∀ w ∈ M, N w := by
    intro w hw
    obtain ⟨j, hj, hw⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨hjQ, hNj⟩ := Finset.mem_filter.mp hj
    exact Relation.ReflTransGen.tail hNj ⟨j, hjQ, rfl, hw⟩
  have cover : ∀ j, j ∈ Q → N (n + j) → ∀ p : Fin n, W C p (n + j) = true →
      ∃ e ∈ E, W C p e = true := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj hNj p hp
      obtain ⟨g, hgj⟩ := hQg j hj
      obtain ⟨c, hc, hWc⟩ := sel_cover C ψ j g hgj (hg g (List.mem_of_getElem? hgj)).1
        (hψ j hj g hgj) (hNψ _ hNj) p hp
      have hcM : c ∈ M := Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hNj⟩, hc⟩
      by_cases hcq : ∃ j' ∈ Q, c = n + j'
      · obtain ⟨j', hj', rfl⟩ := hcq
        have hlt := (sel_sub C ψ j _ hc).choose_spec.2.2.1
        exact ih j' (by omega) hj' (hMN _ hcM) p hWc
      · push_neg at hcq
        exact ⟨c, Finset.mem_filter.mpr ⟨hcM, hcq⟩, hWc⟩
  have himg : (Qn.image (fun j => n + j)).card = Qn.card :=
    Finset.card_image_of_injective _ (fun a b h => by simpa using h)
  have hsub : Qn.image (fun j => n + j) ⊆
      insert (n + r) (M.filter (fun w => w ∈ Qn.image (fun j => n + j))) := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hjQ, hNj⟩ := Finset.mem_filter.mp hj
    rcases hNc _ hNj with h | ⟨j2, hj2, hN2, hw2⟩
    · exact Finset.mem_insert.mpr (Or.inl h)
    · refine Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨?_, hw⟩))
      exact Finset.mem_biUnion.mpr ⟨j2, Finset.mem_filter.mpr ⟨hj2, hN2⟩, hw2⟩
  have hMcard : M.card ≤ Qn.card * 2 :=
    Finset.card_biUnion_le_card_mul _ _ 2 (fun j _ => sel_card C ψ j hg)
  have hsplit := Finset.card_filter_add_card_filter_not (s := M)
    (fun w => w ∈ Qn.image (fun j => n + j))
  have hEsub : E ⊆ M.filter (fun w => ¬ (w ∈ Qn.image (fun j => n + j))) := by
    intro w hw
    obtain ⟨hwM, hwe⟩ := Finset.mem_filter.mp hw
    refine Finset.mem_filter.mpr ⟨hwM, ?_⟩
    intro him
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp him
    exact hwe j (Finset.mem_filter.mp hj).1 rfl
  have hEc : E.card ≤ Qn.card + 1 := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le (n + r) (M.filter (fun w => w ∈ Qn.image (fun j => n + j)))
    have h3 := Finset.card_le_card hEsub
    omega
  have hQnQ : Qn.card ≤ Q.card := Finset.card_filter_le _ _
  have hsubA : Finset.univ.filter (fun p : Fin n => W C p (n + r) = true) ⊆
      E.biUnion (fun e => Finset.univ.filter (fun p : Fin n => W C p e = true)) := by
    intro p hp
    have hp' : W C p (n + r) = true := by simpa using hp
    obtain ⟨e, he, hWe⟩ := cover r hr Relation.ReflTransGen.refl p hp'
    exact Finset.mem_biUnion.mpr ⟨e, he, by simpa using hWe⟩
  have hbig : (E.biUnion (fun e => Finset.univ.filter (fun p : Fin n => W C p e = true))).card
      ≤ E.card * 1 := by
    apply Finset.card_biUnion_le_card_mul
    intro e he
    obtain ⟨heM, hee⟩ := Finset.mem_filter.mp he
    obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.mp heM
    obtain ⟨g, hgj, hin, hlt, hψe⟩ := sel_sub C ψ j e hej
    exact hex j (Finset.mem_filter.mp hj).1 g hgj e hin hlt hψe hee
  have := Finset.card_le_card hsubA
  omega

end PEqualNP.Outside.L_meta_792

theorem PEqualNP.Outside.L_meta_792 : ∀ (n r : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (Q : Finset ℕ) (ψ : ℕ → Bool), (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ p : Fin n, (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true → p ∈ S) → r ∈ Q → (∀ j ∈ Q, j < C.size ∧ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) ⊆ S ∧ 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)).card) → (∀ j ∈ Q, ∀ j' : ℕ, j' < j → (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ n + j' ∈ g.inputs) → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)) ⊆ S → 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)).card → j' ∈ Q) → (∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g → ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) → (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → ψ w = false → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (w) false = true)) ⊆ S) → ψ (n + r) = false → (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (n + r) false = true)).card ≤ Q.card + 1 := by
  intro n r S C Q ψ hg hS hr hQ hcl hψ hnot hr0
  classical
  have hex : ∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g → ∀ w ∈ g.inputs, w < n + j →
      ψ w = false → (∀ j' ∈ Q, w ≠ n + j') →
      (Finset.univ.filter (fun p : Fin n => PEqualNP.Outside.L_meta_792.W C p w = true)).card
        ≤ 1 := by
    intro j hj g hgj w hw hlt hψw hwQ
    by_cases hwn : w < n
    · exact PEqualNP.Outside.L_meta_792.card_input C w hwn
    · obtain ⟨j', rfl⟩ : ∃ j', w = n + j' := ⟨w - n, by omega⟩
      by_contra hc
      have h2 : 2 ≤ (Finset.univ.filter (fun p : Fin n => PEqualNP.Outside.L_meta_792.W C p (n + j') = true)).card := by omega
      exact hwQ j' (hcl j hj j' (by omega) ⟨g, hgj, hw⟩ (hnot _ hwQ hψw) h2) rfl
  exact PEqualNP.Outside.L_meta_792.main C Q ψ r hg hr hψ
    (fun j hj => by
      have := (hQ j hj).1
      exact ⟨_, List.getElem?_eq_getElem this⟩) hex hr0
