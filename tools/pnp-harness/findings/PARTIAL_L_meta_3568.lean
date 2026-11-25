import Mathlib
import PEqualNP.Defs

-- Gate elimination at a vertex read by an AND gate of a least AO2 circuit.
-- The degenerate case (every edge of G meets z) is settled by the support bound:
-- a fan-in-two circuit computing the edge function of G has at least
-- (number of vertices carrying an edge) - 1 gates.

namespace PEqualNP.Outside.L_meta_3568

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

-- One step of the wire fold.
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

-- The value of wire `u` of `C` at the list input `x`.
def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  have h : gateAt C j = C.gates.getD j ⟨GateOp.or, []⟩ := rfl
  rw [h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  have h : val C x u = (C.gates.foldl stepWire x).getD u false := rfl
  rw [h]
  exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  have h : val C x u = (C.gates.foldl stepWire x).getD u false := rfl
  rw [h]
  apply getD_ge
  rw [foldl_length]
  omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma dep (n : ℕ) (C : Circuit) (hR : ∀ j < C.gates.length, (gateAt C j).inputs.length = 2) :
    ∀ k, k ≤ C.gates.length → ∀ W : Finset ℕ, (∀ w ∈ W, w < n + k) →
      ∃ T : Finset (Fin n), T.card ≤ k + W.card ∧
        ∀ x y : Fin n → Bool, (∀ i ∈ T, x i = y i) →
          ∀ w ∈ W, val C (List.ofFn x) w = val C (List.ofFn y) w := by
  intro k
  induction k with
  | zero =>
    intro _ W hW
    refine ⟨Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ W), ?_, ?_⟩
    · rw [Nat.zero_add, ← Finset.card_image_of_injective _ Fin.val_injective]
      apply Finset.card_le_card
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
      exact (Finset.mem_filter.1 hi).2
    · intro x y h w hw
      have hw' : w < n := by simpa using hW w hw
      have e : ∀ z : Fin n → Bool, (List.ofFn z).getD w false = z ⟨w, hw'⟩ := by
        intro z; simp [List.getD_eq_getElem?_getD, hw']
      rw [val_input (by simp) hw', val_input (by simp) hw', e, e]
      exact h ⟨w, hw'⟩ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hw⟩)
  | succ k ih =>
    intro hk W hW
    by_cases hmem : n + k ∈ W
    · obtain ⟨W2, hW2⟩ : ∃ W2 : Finset ℕ, W2 = W.erase (n + k) ∪
          ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset := ⟨_, rfl⟩
      have hlt2 : ∀ w ∈ W2, w < n + k := by
        intro w hw
        rw [hW2] at hw
        rcases Finset.mem_union.1 hw with h | h
        · have h1 := hW w (Finset.mem_of_mem_erase h)
          have h2 := Finset.ne_of_mem_erase h
          omega
        · simp at h; exact h.2
      have hs1 : ∀ w ∈ W, w ≠ n + k → w ∈ W2 := by
        intro w hw hne
        rw [hW2]
        exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hne, hw⟩)
      have hs2 : ∀ i ∈ (gateAt C k).inputs, i < n + k → i ∈ W2 := by
        intro i hi hlt
        rw [hW2]
        exact Finset.mem_union_right _ (by simp [hi, hlt])
      have hc : W2.card + 1 ≤ W.card + 2 := by
        rw [hW2]
        have h1 := Finset.card_union_le (W.erase (n + k))
          ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset
        have h2 : ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset.card ≤ 2 :=
          (List.toFinset_card_le _).trans
            ((List.length_filter_le _ _).trans (hR k (by omega)).le)
        have h3 := Finset.card_erase_of_mem hmem
        have h4 : 0 < W.card := Finset.card_pos.2 ⟨_, hmem⟩
        omega
      obtain ⟨T, hT, hdep⟩ := ih (by omega) W2 hlt2
      refine ⟨T, by omega, ?_⟩
      intro x y h w hw
      by_cases hwk : w = n + k
      · rw [hwk, val_gate (by simp) (by omega), val_gate (by simp) (by omega)]
        congr 1
        apply List.map_congr_left
        intro i hi
        by_cases hlt : i < n + k
        · simp only [ite_eq_left hlt]
          exact hdep x y h i (hs2 i hi hlt)
        · simp only [ite_eq_right hlt]
      · exact hdep x y h w (hs1 w hw hwk)
    · obtain ⟨T, hT, hdep⟩ := ih (by omega) W (by
        intro w hw
        have h1 := hW w hw
        have h2 : w ≠ n + k := fun h => hmem (h ▸ hw)
        omega)
      exact ⟨T, by omega, hdep⟩

-- The support bound: a fan-in-two circuit for the edge function of `G` has at least
-- `|support G| - 1` gates.
lemma support_bound (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hF : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅) :
    G.support.ncard ≤ C.size + 1 := by
  have hgf : ∀ x : Fin n → Bool, graphFun G ∅ x =
      (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
        decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) := fun _ => rfl
  obtain ⟨T, hT, hdep⟩ : ∃ T : Finset (Fin n), T.card ≤ C.gates.length + 1 ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ T, x i = y i) →
        val C (List.ofFn x) C.output = val C (List.ofFn y) C.output := by
    by_cases ho : C.output < n + C.gates.length
    · obtain ⟨T, hT, hdep⟩ := dep n C (fun j hj => h2 _ (gateAt_mem hj)) C.gates.length le_rfl
        {C.output} (by simpa using ho)
      exact ⟨T, by simpa using hT, fun x y h => hdep x y h _ (by simp)⟩
    · exact ⟨∅, by simp, fun x y _ => by
        rw [val_ge (n := n) (by simp) (by omega), val_ge (n := n) (by simp) (by omega)]⟩
  have hsub : G.support ⊆ (T : Set (Fin n)) := by
    intro v hv
    obtain ⟨u, huv⟩ := (SimpleGraph.mem_support G).1 hv
    by_contra hvT
    have e := hdep (fun w => decide (w = u ∨ w = v)) (fun w => decide (w = u)) (by
      intro i hi
      have hne : i ≠ v := fun h => hvT (h ▸ hi)
      simp [hne])
    have fx : val C (List.ofFn (fun w => decide (w = u ∨ w = v))) C.output =
        graphFun G ∅ (fun w => decide (w = u ∨ w = v)) :=
      congrFun hF (fun w => decide (w = u ∨ w = v))
    have fy : val C (List.ofFn (fun w => decide (w = u))) C.output =
        graphFun G ∅ (fun w => decide (w = u)) :=
      congrFun hF (fun w => decide (w = u))
    have t1 : graphFun G ∅ (fun w => decide (w = u ∨ w = v)) = true := by
      rw [hgf]
      rw [Bool.or_eq_true]
      right
      rw [decide_eq_true_iff]
      exact ⟨v, u, huv, by simp, by simp⟩
    have t2 : graphFun G ∅ (fun w => decide (w = u)) = false := by
      rw [hgf]
      rw [Bool.or_eq_false_iff]
      refine ⟨by simp, ?_⟩
      rw [decide_eq_false_iff_not]
      rintro ⟨a, b, hab, ha, hb⟩
      have ha' : a = u := by simpa using ha
      have hb' : b = u := by simpa using hb
      exact hab.ne (ha'.trans hb'.symm)
    rw [fx, fy, t1, t2] at e
    cases e
  calc G.support.ncard ≤ (T : Set (Fin n)).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet T)
    _ = T.card := Set.ncard_coe_finset T
    _ ≤ C.size + 1 := hT

-- In the degenerate case every edge of `G` meets `z`, so the support of `G` is
-- `{z}` together with the neighbours of `z`, of size `deg z + 1`.
lemma star_degree_le (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : PEqualNP.TopForm.IsLeastAO G C) (z : Fin n) (hE : 2 ≤ G.edgeFinset.card)
    (hA : ¬ ∃ p q : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj p q) :
    G.degree z ≤ C.size := by
  have hall : ∀ u v : Fin n, G.Adj u v → u = z ∨ v = z := by
    intro u v huv
    by_contra hc
    push_neg at hc
    refine hA ⟨u, v, ?_⟩
    have hmem : s(u, v) ∉ G.incidenceSet z := by
      intro hin
      have h2 : s(u, v) ∈ G.edgeSet ∧ z ∈ s(u, v) := hin
      rcases Sym2.mem_iff.1 h2.2 with h | h
      · exact hc.1 h.symm
      · exact hc.2 h.symm
    exact SimpleGraph.deleteEdges_adj.2 ⟨huv, hmem⟩
  obtain ⟨u0, v0, huv0⟩ : ∃ u v : Fin n, G.Adj u v := by
    by_contra hcon
    push_neg at hcon
    have hemp : G.edgeFinset = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      have he' : e ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.1 he
      exact Sym2.ind (f := fun e => e ∈ G.edgeSet → False)
        (fun a b h => hcon a b ((SimpleGraph.mem_edgeSet G).1 h)) e he'
    rw [hemp] at hE
    simp at hE
  have hz : ∃ w, G.Adj z w := by
    rcases hall u0 v0 huv0 with h | h
    · exact ⟨v0, h ▸ huv0⟩
    · exact ⟨u0, h ▸ huv0.symm⟩
  have hsupp : G.support = ((insert z (G.neighborFinset z) : Finset (Fin n)) : Set (Fin n)) := by
    apply Set.eq_of_subset_of_subset
    · intro v hv
      obtain ⟨u, huv⟩ := (SimpleGraph.mem_support G).1 hv
      rcases hall v u huv with h | h
      · refine Finset.mem_coe.2 ?_
        rw [h]
        exact Finset.mem_insert_self z _
      · refine Finset.mem_coe.2 (Finset.mem_insert_of_mem ?_)
        refine (SimpleGraph.mem_neighborFinset G z v).2 ?_
        rw [← h]
        exact huv.symm
    · intro v hv
      rcases Finset.mem_insert.1 (Finset.mem_coe.1 hv) with h | h
      · exact h ▸ (SimpleGraph.mem_support G).2 hz
      · exact (SimpleGraph.mem_support G).2
          ⟨z, ((SimpleGraph.mem_neighborFinset G z v).1 h).symm⟩
  have hcard : G.support.ncard = G.degree z + 1 := by
    rw [hsupp, Set.ncard_coe_finset,
      Finset.card_insert_of_notMem (SimpleGraph.notMem_neighborFinset_self G z)]
    rfl
  have hb := support_bound n G C hL.1.2.2 hL.2.1
  rw [hcard] at hb
  omega

-- ## The upper bound: a cover of size t for a graph with m edges gives an AO2 circuit of
-- size m + t - 1.  The gate lists and their value lemmas are the ones of the published
-- construction; what is added here is that every gate reads only earlier wires, which the
-- published statement (fan-in at most two, NOT gates allowed) does not record.

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem run_append (a b : List Gate) (w : List Bool) : run (a ++ b) w = run b (run a w) := by
  unfold run; rw [List.foldl_append]

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (step w g) := rfl

theorem run_nil (w : List Bool) : run [] w = w := rfl

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem step_pre (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  unfold step; exact List.getD_append _ _ _ _ h

theorem step_last (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  unfold step
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

theorem run_len (gs : List Gate) : ∀ w : List Bool, (run gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [run_nil]
  | cons g gs ih => intro w; rw [run_cons, ih, step_len]; simp; omega

theorem run_pre (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (run gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i h
    rw [run_cons, ih _ _ (by rw [step_len]; omega), step_pre _ _ _ h]

theorem any_congr (l : List ℕ) (f g : ℕ → Bool) (h : ∀ k ∈ l, f k = g k) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun k hk => h k (by simp [hk]))]

-- The two gate values, as named lemmas, so that no tactic ever unfolds `GateOp.eval`.
theorem or_eval (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem and_eval (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

-- An OR chain starting from wire prev over the wires ks.
def chainG : ℕ → ℕ → List ℕ → List Gate
  | _, _, [] => []
  | p, prev, k :: ks => ⟨GateOp.or, [prev, k]⟩ :: chainG (p + 1) p ks

def res : ℕ → ℕ → List ℕ → ℕ
  | _, prev, [] => prev
  | p, _, _ :: ks => res (p + 1) p ks

theorem chainG_len : ∀ (ks : List ℕ) (p prev : ℕ), (chainG p prev ks).length = ks.length := by
  intro ks
  induction ks with
  | nil => intro p prev; rfl
  | cons k ks ih => intro p prev; simp [chainG, ih]

theorem chainG_fan : ∀ (ks : List ℕ) (p prev : ℕ), ∀ g ∈ chainG p prev ks,
    g.op = GateOp.or ∧ g.inputs.length = 2 := by
  intro ks
  induction ks with
  | nil => intro p prev g hg; simp [chainG] at hg
  | cons k ks ih =>
    intro p prev g hg
    simp only [chainG, List.mem_cons] at hg
    rcases hg with hg | hg
    · subst hg; simp
    · exact ih _ _ g hg

theorem chain_val (v : ℕ → Bool) : ∀ (ks : List ℕ) (p prev : ℕ) (w : List Bool) (b : Bool),
    w.length = p → prev < p → (∀ k ∈ ks, k < p ∧ w.getD k false = v k) →
    w.getD prev false = b →
    (run (chainG p prev ks) w).getD (res p prev ks) false = (b || ks.any v) := by
  intro ks
  induction ks with
  | nil => intro p prev w b _ _ _ hb; simp only [chainG, res, run_nil]; rw [hb]; simp
  | cons k ks ih =>
    intro p prev w b hl hp hk hb
    simp only [chainG, res, run_cons]
    have hk0 := hk k (by simp)
    rw [ih (p + 1) p _ (b || v k) (by rw [step_len]; omega) (by omega)]
    · simp [Bool.or_assoc]
    · intro k' hk'
      have := hk k' (by simp [hk'])
      refine ⟨by omega, ?_⟩
      rw [step_pre _ _ _ (by omega)]; exact this.2
    · rw [← hl, step_last]
      simp only [List.map_cons, List.map_nil, or_eval]
      rw [hb, hk0.2]

-- One block per star: an OR chain over its leaves, then an AND with its centre.
def stars : ℕ → List (ℕ × List ℕ) → List Gate
  | _, [] => []
  | p, (_, []) :: S => stars p S
  | p, (t, j :: js) :: S =>
      chainG p j js ++ [⟨GateOp.and, [res p j js, t]⟩] ++ stars (p + js.length + 1) S

def outs : ℕ → List (ℕ × List ℕ) → List ℕ
  | _, [] => []
  | p, (_, []) :: S => outs p S
  | p, (_, _ :: js) :: S => (p + js.length) :: outs (p + js.length + 1) S

theorem stars_len : ∀ (S : List (ℕ × List ℕ)) (p : ℕ),
    (stars p S).length = (S.map fun e => e.2.length).sum := by
  intro S
  induction S with
  | nil => intro p; rfl
  | cons e S ih =>
    intro p
    obtain ⟨t, L⟩ := e
    cases L with
    | nil => simp [stars, ih]
    | cons j js => simp [stars, ih, chainG_len]; omega

theorem outs_len : ∀ (S : List (ℕ × List ℕ)) (p : ℕ), (outs p S).length ≤ S.length := by
  intro S
  induction S with
  | nil => intro p; simp [outs]
  | cons e S ih =>
    intro p
    obtain ⟨t, L⟩ := e
    cases L with
    | nil => have := ih p; simp [outs]; omega
    | cons j js => have := ih (p + js.length + 1); simp [outs]; omega

theorem outs_lt : ∀ (S : List (ℕ × List ℕ)) (p : ℕ), ∀ o ∈ outs p S, o < p + (stars p S).length := by
  intro S
  induction S with
  | nil => intro p o ho; simp [outs] at ho
  | cons e S ih =>
    intro p o ho
    obtain ⟨t, L⟩ := e
    cases L with
    | nil => simp only [outs] at ho; simp only [stars]; exact ih p o ho
    | cons j js =>
      simp only [outs, List.mem_cons] at ho
      simp only [stars, List.length_append, chainG_len]
      rcases ho with ho | ho
      · simp; omega
      · have := ih _ o ho; simp at this ⊢; omega

theorem stars_fan : ∀ (S : List (ℕ × List ℕ)) (p : ℕ), ∀ g ∈ stars p S,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro S
  induction S with
  | nil => intro p g hg; simp [stars] at hg
  | cons e S ih =>
    intro p g hg
    obtain ⟨t, L⟩ := e
    cases L with
    | nil => simp only [stars] at hg; exact ih p g hg
    | cons j js =>
      simp only [stars, List.mem_append, List.mem_singleton] at hg
      rcases hg with (hg | hg) | hg
      · have := chainG_fan js p j g hg; exact ⟨Or.inr this.1, this.2⟩
      · subst hg; simp
      · exact ih _ g hg

theorem stars_val (v : ℕ → Bool) (m : ℕ) : ∀ (S : List (ℕ × List ℕ)) (p : ℕ) (w : List Bool),
    w.length = p → m ≤ p → (∀ i < m, w.getD i false = v i) →
    (∀ e ∈ S, e.1 < m ∧ ∀ j ∈ e.2, j < m) →
    (outs p S).any (fun o => (run (stars p S) w).getD o false) =
      S.any (fun e => v e.1 && e.2.any v) := by
  intro S
  induction S with
  | nil => intro p w _ _ _ _; simp [outs]
  | cons e S ih =>
    intro p w hl hm hv hS
    obtain ⟨t, L⟩ := e
    have hS' : ∀ e ∈ S, e.1 < m ∧ ∀ j ∈ e.2, j < m := fun e he => hS e (by simp [he])
    have he := hS (t, L) (by simp)
    cases L with
    | nil =>
      simp only [outs, stars]
      rw [ih p w hl hm hv hS']
      simp
    | cons j js =>
      simp only [outs, stars, List.any_cons]
      set w1 := run (chainG p j js ++ [⟨GateOp.and, [res p j js, t]⟩]) w with hw1
      have hl1 : w1.length = p + js.length + 1 := by
        rw [hw1, run_len]; simp [chainG_len]; omega
      have hv1 : ∀ i < m, w1.getD i false = v i := by
        intro i hi; rw [hw1, run_pre _ _ _ (by omega)]; exact hv i hi
      rw [run_append, ← hw1, ih _ w1 hl1 (by omega) hv1 hS',
        run_pre _ _ _ (by omega)]
      congr 1
      rw [hw1, run_append]
      have hc := chain_val v js p j w (v j) hl (by have := he.2 j (by simp); omega)
        (fun k hk => ⟨by have := he.2 k (by simp [hk]); omega, hv k (he.2 k (by simp [hk]))⟩)
        (hv j (he.2 j (by simp)))
      have hlc : (run (chainG p j js) w).length = p + js.length := by
        rw [run_len, chainG_len, hl]
      rw [run_cons, run_nil, ← hlc, step_last]
      simp only [List.map_cons, List.map_nil, and_eval]
      rw [hc, run_pre _ _ _ (by rw [hl]; have := he.1; omega), hv t he.1]
      simp [Bool.and_comm]

-- The leaves assigned to a cover vertex t: neighbours j, with t below j when j is in T too.
def leaves {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (t : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => G.Adj t j ∧ (j ∈ T → t < j))

theorem leaves_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)) :
    ∑ t ∈ T, (leaves G T t).card ≤ G.edgeFinset.card := by
  rw [← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn (fun e => s(e.1, e.2))
  · intro e he
    simp only [Finset.mem_coe, Finset.mem_sigma, leaves, Finset.mem_filter] at he
    simp [SimpleGraph.mem_edgeFinset, he.2.2.1]
  · intro e he e' he' h
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, leaves,
      Finset.mem_filter] at he he'
    simp only [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Sigma.ext h1 (heq_of_eq h2)
    · exfalso
      have a := he.2.2.2 (by rw [h2]; exact he'.1)
      have b := he'.2.2.2 (by rw [← h1]; exact he.1)
      rw [h1, h2] at a
      exact lt_asymm a b

-- Gate number q of a gate list.
def gd (gs : List Gate) (q : ℕ) : Gate := gs.getD q ⟨GateOp.or, []⟩

theorem gd_left (a b : List Gate) (q : ℕ) (h : q < a.length) : gd (a ++ b) q = gd a q :=
  List.getD_append _ _ _ _ h

theorem gd_right (a b : List Gate) (q : ℕ) (h : a.length ≤ q) :
    gd (a ++ b) q = gd b (q - a.length) :=
  List.getD_append_right _ _ _ _ h

theorem gd_zero (g : Gate) (b : List Gate) : gd (g :: b) 0 = g := rfl

theorem res_lt : ∀ (ks : List ℕ) (p prev : ℕ), prev < p → res p prev ks < p + ks.length := by
  intro ks
  induction ks with
  | nil => intro p prev h; simpa [res] using h
  | cons k ks ih =>
    intro p prev h
    have := ih (p + 1) p (by omega)
    simp only [res, List.length_cons]
    omega

theorem chainG_back : ∀ (ks : List ℕ) (p prev : ℕ), prev < p → (∀ k ∈ ks, k < p) →
    ∀ q < (chainG p prev ks).length, ∀ i ∈ (gd (chainG p prev ks) q).inputs, i < p + q := by
  intro ks
  induction ks with
  | nil => intro p prev _ _ q hq; simp [chainG] at hq
  | cons k ks ih =>
    intro p prev hp hk q hq i hi
    cases q with
    | zero =>
      have h0 : gd (chainG p prev (k :: ks)) 0 = ⟨GateOp.or, [prev, k]⟩ := by
        show gd (⟨GateOp.or, [prev, k]⟩ :: chainG (p + 1) p ks) 0 = _
        exact gd_zero _ _
      rw [h0] at hi
      have hk0 := hk k (by simp)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hi | hi
      · omega
      · omega
    | succ q =>
      have h1 : gd (chainG p prev (k :: ks)) (q + 1) = gd (chainG (p + 1) p ks) q := by
        show gd (⟨GateOp.or, [prev, k]⟩ :: chainG (p + 1) p ks) (q + 1) = _
        rfl
      rw [h1] at hi
      have hq' : q < (chainG (p + 1) p ks).length := by
        simp only [chainG, List.length_cons, chainG_len] at hq
        rw [chainG_len]
        omega
      have := ih (p + 1) p (by omega) (fun k' hk' => by have := hk k' (by simp [hk']); omega)
        q hq' i hi
      omega

theorem stars_back : ∀ (S : List (ℕ × List ℕ)) (m p : ℕ), m ≤ p →
    (∀ e ∈ S, e.1 < m ∧ ∀ j ∈ e.2, j < m) →
    ∀ q < (stars p S).length, ∀ i ∈ (gd (stars p S) q).inputs, i < p + q := by
  intro S
  induction S with
  | nil => intro m p _ _ q hq; simp [stars] at hq
  | cons e S ih =>
    intro m p hm hS q hq i hi
    obtain ⟨t, L⟩ := e
    have hS' : ∀ e ∈ S, e.1 < m ∧ ∀ j ∈ e.2, j < m := fun e he => hS e (by simp [he])
    have he := hS (t, L) (by simp)
    cases L with
    | nil =>
      simp only [stars] at hq hi
      exact ih m p hm hS' q hq i hi
    | cons j js =>
      have hjp : j < p := by have := he.2 j (by simp); omega
      have htp : t < p := by have := he.1; omega
      have hdef : stars p ((t, j :: js) :: S) =
          chainG p j js ++ ([⟨GateOp.and, [res p j js, t]⟩] ++ stars (p + js.length + 1) S) := by
        show chainG p j js ++ [⟨GateOp.and, [res p j js, t]⟩] ++
          stars (p + js.length + 1) S = _
        rw [List.append_assoc]
      rw [hdef] at hq hi
      have hcl : (chainG p j js).length = js.length := chainG_len js p j
      by_cases hlt : q < js.length
      · rw [gd_left _ _ _ (by omega)] at hi
        exact chainG_back js p j hjp
          (fun k hk => by have := he.2 k (by simp [hk]); omega) q (by omega) i hi
      · rw [gd_right _ _ _ (by omega)] at hi
        rw [hcl] at hi
        cases hq2 : q - js.length with
        | zero =>
          rw [hq2] at hi
          have hz : gd ([⟨GateOp.and, [res p j js, t]⟩] ++ stars (p + js.length + 1) S) 0
              = ⟨GateOp.and, [res p j js, t]⟩ := rfl
          rw [hz] at hi
          have hr := res_lt js p j hjp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with hi | hi
          · omega
          · omega
        | succ r =>
          rw [hq2] at hi
          have h1 : gd ([⟨GateOp.and, [res p j js, t]⟩] ++ stars (p + js.length + 1) S)
              (r + 1) = gd (stars (p + js.length + 1) S) r := rfl
          rw [h1] at hi
          have hrq : q = js.length + r + 1 := by omega
          have hrl : r < (stars (p + js.length + 1) S).length := by
            simp only [List.length_append, List.length_cons, List.length_nil, hcl] at hq
            omega
          have := ih m (p + js.length + 1) (by omega) hS' r hrl i hi
          omega

-- The upper bound in the AO2 model.
theorem ub (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (hcov : ∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) (hne : ∃ i j : Fin n, G.Adj i j) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧
      (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n D x =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
      D.size + 1 ≤ G.edgeFinset.card + T.card := by
  set S : List (ℕ × List ℕ) :=
    T.toList.map (fun t : Fin n => ((t : ℕ), (leaves G T t).toList.map Fin.val)) with hSdef
  set I : List ℕ := outs n S with hIdef
  set P : ℕ := n + (stars n S).length with hP
  have hSlt : ∀ e ∈ S, e.1 < n ∧ ∀ j ∈ e.2, j < n := by
    intro e he
    simp only [hSdef, List.mem_map] at he
    obtain ⟨t, _, rfl⟩ := he
    refine ⟨t.isLt, ?_⟩
    intro j hj
    simp only [List.mem_map] at hj
    obtain ⟨j, _, rfl⟩ := hj
    exact j.isLt
  have hIlt : ∀ i ∈ I, i < P := by
    intro i hi
    rw [hIdef] at hi
    exact outs_lt S n i hi
  refine ⟨⟨stars n S ++ chainG P (I.headD 0) I.tail,
    if I = [] then P else res P (I.headD 0) I.tail⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append] at hg
    rcases hg with hg | hg
    · exact (stars_fan S n g hg).1
    · exact Or.inr (chainG_fan _ _ _ g hg).1
  · intro q hq i hi
    show i < n + q
    have hq' : q < (stars n S ++ chainG P (I.headD 0) I.tail).length := hq
    have hcl : (chainG P (I.headD 0) I.tail).length = I.tail.length := chainG_len _ _ _
    by_cases hlt : q < (stars n S).length
    · have h2 : (PEqualNP.MetaComplexity.NestedCover.gateAt
          (⟨stars n S ++ chainG P (I.headD 0) I.tail,
            if I = [] then P else res P (I.headD 0) I.tail⟩ : Circuit) q).inputs
          = (gd (stars n S) q).inputs := by
        rw [show (PEqualNP.MetaComplexity.NestedCover.gateAt
          (⟨stars n S ++ chainG P (I.headD 0) I.tail,
            if I = [] then P else res P (I.headD 0) I.tail⟩ : Circuit) q)
          = gd (stars n S ++ chainG P (I.headD 0) I.tail) q from rfl,
          gd_left _ _ _ hlt]
      rw [h2] at hi
      exact stars_back S n n le_rfl hSlt q hlt i hi
    · have h2 : (PEqualNP.MetaComplexity.NestedCover.gateAt
          (⟨stars n S ++ chainG P (I.headD 0) I.tail,
            if I = [] then P else res P (I.headD 0) I.tail⟩ : Circuit) q).inputs
          = (gd (chainG P (I.headD 0) I.tail) (q - (stars n S).length)).inputs := by
        rw [show (PEqualNP.MetaComplexity.NestedCover.gateAt
          (⟨stars n S ++ chainG P (I.headD 0) I.tail,
            if I = [] then P else res P (I.headD 0) I.tail⟩ : Circuit) q)
          = gd (stars n S ++ chainG P (I.headD 0) I.tail) q from rfl,
          gd_right _ _ _ (by omega)]
      rw [h2] at hi
      rcases hIc : I with _ | ⟨i0, is⟩
      · rw [hIc] at hcl hi
        simp only [List.tail_nil, List.length_nil] at hcl
        simp only [List.tail_nil, chainG] at hi
        simp only [gd, List.getD_nil] at hi
        simp at hi
      · have h0 : I.headD 0 < P := hIlt _ (by rw [hIc]; simp)
        have hts : ∀ k ∈ I.tail, k < P := by
          intro k hk
          refine hIlt k ?_
          rw [hIc] at hk ⊢
          simp only [List.tail_cons] at hk
          simp [hk]
        have hql : q - (stars n S).length < (chainG P (I.headD 0) I.tail).length := by
          simp only [List.length_append, hcl] at hq'
          rw [hcl]
          omega
        have := chainG_back I.tail P (I.headD 0) h0 hts _ hql i hi
        omega
  · intro g hg
    simp only [List.mem_append] at hg
    rcases hg with hg | hg
    · exact (stars_fan S n g hg).2
    · exact (chainG_fan _ _ _ g hg).2
  · intro x
    set v : ℕ → Bool := fun i => (List.ofFn x).getD i false with hv
    have hvx : ∀ i : Fin n, v i = x i := by
      intro i; simp [hv]
    set W := run (stars n S) (List.ofFn x) with hW
    have hWl : W.length = P := by rw [hW, run_len]; simp [hP]
    have heval : PEqualNP.MetaComplexity.circuitFun n
        (⟨stars n S ++ chainG P (I.headD 0) I.tail,
          if I = [] then P else res P (I.headD 0) I.tail⟩ : Circuit) x =
        I.any (fun o => W.getD o false) := by
      show (run _ _).getD _ false = _
      rw [run_append, ← hW]
      rcases hIc : I with _ | ⟨i0, is⟩
      · simp only [List.headD_nil, List.tail_nil, chainG, run_nil, ↓reduceIte, List.any_nil]
        rw [List.getD_eq_default _ _ (by omega)]
      · simp only [List.headD_cons, List.tail_cons, reduceCtorEq, ↓reduceIte]
        have h0 := hIlt i0 (by rw [hIc]; simp)
        rw [chain_val (fun o => W.getD o false) is P i0 W _ hWl h0
          (fun k hk => ⟨hIlt k (by rw [hIc]; simp [hk]), rfl⟩) rfl]
        simp
    rw [heval, hIdef, hW, stars_val v n S n (List.ofFn x) (by simp) le_rfl (fun i _ => rfl) hSlt]
    rw [Bool.eq_iff_iff]
    simp only [hSdef, List.any_eq_true, List.mem_map, Finset.mem_toList,
      Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, h1, k, hk, h2⟩
      simp only [List.mem_map, Finset.mem_toList] at hk
      obtain ⟨j, hj, rfl⟩ := hk
      exact ⟨t, j, (Finset.mem_filter.mp hj).2.1, by rw [← hvx]; exact h1,
        by rw [← hvx]; exact h2⟩
    · rintro ⟨i, j, hij, hi, hj⟩
      have key : ∀ i j : Fin n, G.Adj i j → x i = true → x j = true → i ∈ T →
          (j ∈ T → i < j) → ∃ e, (∃ t, t ∈ T ∧ ((t : ℕ), (leaves G T t).toList.map Fin.val) = e)
            ∧ v e.1 = true ∧ ∃ k ∈ e.2, v k = true := by
        intro i j hij hi hj hiT hlt
        refine ⟨_, ⟨i, hiT, rfl⟩, by rw [hvx]; exact hi, j, ?_, by rw [hvx]; exact hj⟩
        simp only [List.mem_map, Finset.mem_toList, leaves, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨j, ⟨hij, hlt⟩, rfl⟩
      have hne' : i ≠ j := G.ne_of_adj hij
      by_cases hiT : i ∈ T
      · by_cases hjT : j ∈ T
        · rcases lt_or_gt_of_ne hne' with h | h
          · exact key i j hij hi hj hiT (fun _ => h)
          · exact key j i hij.symm hj hi hjT (fun _ => h)
        · exact key i j hij hi hj hiT (fun h => absurd h hjT)
      · have hjT : j ∈ T := (hcov i j hij).resolve_left hiT
        exact key j i hij.symm hj hi hjT (fun h => absurd h hiT)
  · have heq : (stars n S).length = ∑ t ∈ T, (leaves G T t).card := by
      rw [stars_len, hSdef, List.map_map, ← Finset.sum_map_toList]
      simp [Function.comp_def]
    have hsum : (stars n S).length ≤ G.edgeFinset.card := heq ▸ leaves_card G T
    have hI : I.length ≤ T.card := by
      have := outs_len S n
      have hSl : S.length = T.card := by rw [hSdef, List.length_map, Finset.length_toList]
      rw [hIdef]
      omega
    have hT1 : 1 ≤ T.card := by
      obtain ⟨i, j, hij⟩ := hne
      rcases hcov i j hij with h | h
      · exact Finset.card_pos.2 ⟨i, h⟩
      · exact Finset.card_pos.2 ⟨j, h⟩
    show (stars n S ++ chainG P (I.headD 0) I.tail).length + 1 ≤ _
    rw [List.length_append, chainG_len, List.length_tail]
    omega

-- THE ONE REMAINING GAP.  The edges-plus-cover lower bound for a least AO2 circuit of a
-- 2-colourable graph with no 4-cycle.  It is known for circuits every AND gate of which is
-- below F (that is the published row with the clean-AND hypothesis), and it is exactly what
-- the junk-gate program is for; nothing in the Defs tree supplies it in general.
theorem lower_bound (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hbip : ∃ c : Fin n → Bool, ∀ u v : Fin n, G.Adj u v → c u ≠ c v)
    (h4 : PEqualNP.TopForm.NoFourCycle G) (hne : ∃ u v : Fin n, G.Adj u v)
    (hL : PEqualNP.TopForm.IsLeastAO G C) :
    ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  sorry

end PEqualNP.Outside.L_meta_3568

theorem PEqualNP.Outside.L_meta_3568 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∃ c : Fin n → Bool, ∀ u v : Fin n, G.Adj u v → c u ≠ c v) → PEqualNP.TopForm.NoFourCycle G → 2 ≤ G.edgeFinset.card → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C → ∀ z : Fin n, (∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (z : ℕ) ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ PEqualNP.MetaComplexity.circuitFun n D = (fun y : Fin n → Bool => @decide (∃ a b : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj a b ∧ y a = true ∧ y b = true) (Classical.propDecidable _)) ∧ D.size + G.degree z ≤ C.size ∧ ((∃ p q : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj p q) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (G.deleteEdges (G.incidenceSet z)) S ∧ ∀ T : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T → S.card < T.card) → D.size + G.degree z + 1 ≤ C.size) := by
  intro n G hdec hbip h4c hE C hL z hzand
  by_cases hA : ∃ p q : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj p q
  · haveI hdec' : DecidableRel (G.deleteEdges (G.incidenceSet z)).Adj := by
      intro u v
      refine decidable_of_iff (G.Adj u v ∧ u ≠ z ∧ v ≠ z) ?_
      rw [SimpleGraph.deleteEdges_adj]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, ?_⟩
        intro hin
        have h4 : s(u, v) ∈ G.edgeSet ∧ z ∈ s(u, v) := hin
        rcases Sym2.mem_iff.1 h4.2 with h | h
        · exact h2 h.symm
        · exact h3 h.symm
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_, ?_⟩
        · intro hh
          have hmem : s(u, v) ∈ G.edgeSet ∧ z ∈ s(u, v) :=
            ⟨h1, by rw [hh]; exact Sym2.mem_iff.2 (Or.inl rfl)⟩
          exact h2 hmem
        · intro hh
          have hmem : s(u, v) ∈ G.edgeSet ∧ z ∈ s(u, v) :=
            ⟨h1, by rw [hh]; exact Sym2.mem_iff.2 (Or.inr rfl)⟩
          exact h2 hmem
    obtain ⟨T, hTcov, hTb⟩ := PEqualNP.Outside.L_meta_3568.lower_bound n G C hbip h4c
      (by obtain ⟨p, q, hpq⟩ := hA; exact ⟨p, q, (SimpleGraph.deleteEdges_adj.1 hpq).1⟩) hL
    have hef : (G.deleteEdges (G.incidenceSet z)).edgeFinset
        = G.edgeFinset \ G.incidenceFinset z := by
      ext e
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges, Set.mem_diff,
        Finset.mem_sdiff, SimpleGraph.mem_incidenceFinset]
    have hle : G.degree z ≤ G.edgeFinset.card := by
      rw [← SimpleGraph.card_incidenceFinset_eq_degree]
      exact Finset.card_le_card (G.incidenceFinset_subset z)
    have hm' : (G.deleteEdges (G.incidenceSet z)).edgeFinset.card + G.degree z
        = G.edgeFinset.card := by
      rw [hef, Finset.card_sdiff_of_subset (G.incidenceFinset_subset z),
        SimpleGraph.card_incidenceFinset_eq_degree]
      omega
    have hbool : ∀ (p : Prop) (i1 i2 : Decidable p), @decide p i1 = @decide p i2 := by
      intro p i1 i2
      cases i1 with
      | isTrue h =>
        cases i2 with
        | isTrue h' => rfl
        | isFalse h' => exact absurd h h'
      | isFalse h =>
        cases i2 with
        | isTrue h' => exact absurd h' h
        | isFalse h' => rfl
    by_cases hstrict : ∃ S : Finset (Fin n),
        PEqualNP.MetaComplexity.CoverPromise.IsVertexCover
          (G.deleteEdges (G.incidenceSet z)) S ∧
        ∀ T1 : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T1 →
          S.card < T1.card
    · obtain ⟨S, hScov, hSlt⟩ := hstrict
      obtain ⟨D, hD1, hD2, hD3⟩ := PEqualNP.Outside.L_meta_3568.ub n
        (G.deleteEdges (G.incidenceSet z)) S hScov hA
      have hST : S.card < T.card := hSlt T hTcov
      refine ⟨D, hD1, ?_, ?_, ?_⟩
      · funext y
        rw [hD2 y]
        exact hbool _ _ _
      · omega
      · exact fun _ _ => by omega
    · obtain ⟨D, hD1, hD2, hD3⟩ := PEqualNP.Outside.L_meta_3568.ub n
        (G.deleteEdges (G.incidenceSet z)) T
        (fun u v huv => hTcov u v (SimpleGraph.deleteEdges_adj.1 huv).1) hA
      refine ⟨D, hD1, ?_, ?_, ?_⟩
      · funext y
        rw [hD2 y]
        exact hbool _ _ _
      · omega
      · exact fun _ hs => absurd hs hstrict
  · refine ⟨⟨[], n⟩, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro g hg; simp at hg
      · intro j hj; simp at hj
      · intro g hg; simp at hg
    · funext y
      have h1 : PEqualNP.MetaComplexity.circuitFun n (⟨[], n⟩ : PEqualNP.CircuitLowerBounds.Circuit) y
          = (List.ofFn y).getD n false := rfl
      rw [h1, PEqualNP.Outside.L_meta_3568.getD_ge (List.ofFn y) n (le_of_eq List.length_ofFn)]
      refine (@decide_eq_false _ (Classical.propDecidable _) ?_).symm
      rintro ⟨a, b, hab, _, _⟩
      exact hA ⟨a, b, hab⟩
    · have hs : (⟨[], n⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = 0 := rfl
      rw [hs, Nat.zero_add]
      exact PEqualNP.Outside.L_meta_3568.star_degree_le n G C hL z hE hA
    · exact fun hex _ => absurd hex hA
