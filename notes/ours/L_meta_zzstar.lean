import PEqualNP.Defs

/-!
Structure of Monotone2 circuits for the edge function f_G, for the repairMany step.

Everything here is proved from PEqualNP.Defs alone, so that it can be inlined into a
submission (lint.py allows only Mathlib plus the step import list).

Contents
* wire-level infrastructure (gateBit, stepWire, WiresLE, monotonicity, patch),
* wireVal and the fact that an OR gate true at x has an earlier operand true at x,
* edge_has_clean_and: for EVERY edge of G there is an AND gate of C that is BELOW f_G
  (clean) and true at the pair input of that edge.  The AND gates met by an OR-only
  descent from the output are clean for free, and one of them carries each edge.
* clean_and_star: under NoFourCycle the two operands of a clean AND gate have
  all cross pairs in E, so one of the two operand vertex sets has at most one element -
  a clean AND gate is a STAR.
* patchOne: the general one-slot surgery lemma.  Replacing gate j by ANY monotone gate h
  that is clean and true on every edge that dropping j loses gives a circuit of the same
  size computing f_G with strictly less junk.  This subsumes the one-edge repair, whose
  h is the single edge gate; no hypothesis h <= gate j is needed.
-/

namespace PEqualNP.Outside.ZZStar

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.NotPremium

/-- The value of a gate on a wire list. -/
def gateBit (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

/-- One step of the wire fold. -/
def stepWire (w : List Bool) (g : Gate) : List Bool := w ++ [gateBit w g]

/-- Pointwise domination of wire lists. -/
def WiresLE (w z : List Bool) : Prop :=
  w.length = z.length ∧ ∀ i, w.getD i false = true → z.getD i false = true

/-- An AND or an OR gate. -/
def IsMonoGate (g : Gate) : Prop := g.op = GateOp.and ∨ g.op = GateOp.or

lemma monoGate_of_mem {C : Circuit} (hC : Monotone2 C) {g : Gate} (hg : g ∈ C.gates) :
    IsMonoGate g := by
  simpa [IsMonoGate] using (hC g hg).1

lemma bit_mono {w z : List Bool} (h : WiresLE w z) {g : Gate} (hg : IsMonoGate g)
    (hw : gateBit w g = true) : gateBit z g = true := by
  rcases hg with hop | hop
  · simp only [gateBit, hop, GateOp.eval, List.all_map, List.all_eq_true,
      Function.comp_apply, id_eq] at hw ⊢
    exact fun i hi => h.2 i (hw i hi)
  · simp only [gateBit, hop, GateOp.eval, List.any_map, List.any_eq_true,
      Function.comp_apply, id_eq] at hw ⊢
    obtain ⟨i, hi, hv⟩ := hw
    exact ⟨i, hi, h.2 i hv⟩

lemma append_mono {w z : List Bool} {a b : Bool} (h : WiresLE w z)
    (hab : a = true → b = true) : WiresLE (w ++ [a]) (z ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  rw [List.getD_eq_getElem?_getD] at hi ⊢
  by_cases hlt : i < w.length
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.getElem?_append_left (by rwa [← h.1])]
    simpa only [List.getD_eq_getElem?_getD] using h.2 i
      (by simpa only [List.getD_eq_getElem?_getD] using hi)
  · rw [List.getElem?_append_right (Nat.le_of_not_gt hlt)] at hi
    rw [List.getElem?_append_right (by rw [← h.1]; omega), ← h.1]
    cases hd : i - w.length with
    | zero =>
      simp only [hd, List.getElem?_cons_zero, Option.getD_some] at hi ⊢
      exact hab hi
    | succ k => simp [hd] at hi

lemma fold_mono (gs : List Gate) (hg : ∀ g ∈ gs, IsMonoGate g)
    {w z : List Bool} (h : WiresLE w z) :
    WiresLE (gs.foldl stepWire w) (gs.foldl stepWire z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun k hk => hg k (List.mem_cons_of_mem _ hk))
      (append_mono h (bit_mono h (hg g (by simp))))

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (stepWire w g) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : Fin n) :
    (List.ofFn x).getD u.val false = x u := by
  simp [List.getD_eq_getElem?_getD]

lemma ofFn_mono {n : ℕ} {x y : Fin n → Bool} (h : ∀ u, x u = true → y u = true) :
    WiresLE (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hlt : i < n
  · rw [ofFn_getD y ⟨i, hlt⟩]
    exact h ⟨i, hlt⟩ (by simpa only [ofFn_getD x ⟨i, hlt⟩] using hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hlt)] at hi
    cases hi

/-- The circuit with gate `j` replaced by `g`. -/
def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := ⟨C.gates.set j g, C.output⟩

/-- The wires of `C` that exist when gate `j` is evaluated. -/
def earlierWires (C : Circuit) (j : ℕ) (w : List Bool) : List Bool :=
  (C.gates.take j).foldl stepWire w

/-- The constant false gate, which is what replaceByConst .. false installs. -/
def off : Gate := ⟨GateOp.or, []⟩

/-- The gate computing the single edge `u v`. -/
def edgeGate {n : ℕ} (u v : Fin n) : Gate := ⟨GateOp.and, [u.val, v.val]⟩

lemma off_bit (w : List Bool) : gateBit w off = false := rfl

lemma replace_patch (C : Circuit) (j : ℕ) :
    (⟨replaceByConst C.gates j false, C.output⟩ : Circuit) = patch C j off := by
  simp [patch, replaceByConst, PEqualNP.NotPremium.constGate, off]

lemma wires_patch {C : Circuit} {j : ℕ} (hj : j < C.gates.length) (g : Gate) (w : List Bool) :
    (patch C j g).wires w
      = (C.gates.drop (j + 1)).foldl stepWire (stepWire (earlierWires C j w) g) := by
  change (C.gates.set j g).foldl stepWire w = _
  rw [List.set_eq_take_append_cons_drop, ite_eq_left hj, List.foldl_append, List.foldl_cons]
  rfl

lemma original_patch {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    patch C j C.gates[j] = C := by
  cases C with
  | mk gates output =>
    change Circuit.mk (gates.set j gates[j]) output = Circuit.mk gates output
    congr 1
    exact List.set_getElem_self hj

lemma patch_mono {C : Circuit} (hC : Monotone2 C) {j : ℕ} (hj : j < C.gates.length)
    (g h : Gate) (w : List Bool)
    (hbit : gateBit (earlierWires C j w) g = true → gateBit (earlierWires C j w) h = true) :
    WiresLE ((patch C j g).wires w) ((patch C j h).wires w) := by
  rw [wires_patch hj, wires_patch hj]
  apply fold_mono _ (fun k hk => monoGate_of_mem hC (List.mem_of_mem_drop hk))
  exact append_mono ⟨rfl, fun _ h => h⟩ hbit

lemma patch_bit {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length)
    (g : Gate) (x : Fin n → Bool) :
    gateVal n (patch C j g) j x = gateBit (earlierWires C j (List.ofFn x)) g := by
  have hlen : (earlierWires C j (List.ofFn x)).length = n + j := by
    unfold earlierWires
    rw [fold_length]
    simp [Nat.min_eq_left (Nat.le_of_lt hj)]
  unfold gateVal
  rw [wires_patch hj, fold_getD_lt _ _ _ (by simp [stepWire, hlen]), ← hlen]
  simp [stepWire, List.getD_eq_getElem?_getD]

lemma patch_isMono {C : Circuit} (hC : Monotone2 C) {j : ℕ} {g : Gate}
    (hg : IsMonoGate g) (hlen : g.inputs.length ≤ 2) : Monotone2 (patch C j g) := by
  intro k hk
  change k ∈ C.gates.set j g at hk
  rcases List.mem_or_eq_of_mem_set hk with hk | rfl
  · exact hC k hk
  · exact ⟨by simpa [IsMonoGate] using hg, hlen⟩

lemma gateAt_patch_ne (C : Circuit) (j k : ℕ) (g : Gate) (hne : j ≠ k) :
    gateAt (patch C j g) k = gateAt C k := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma pair_le {n : ℕ} {x : Fin n → Bool} {u v : Fin n}
    (hu : x u = true) (hv : x v = true) (k : Fin n) :
    pairInput u v k = true → x k = true := by
  simp only [pairInput, decide_eq_true_eq]
  rintro (rfl | rfl)
  · exact hu
  · exact hv

lemma circuit_mono {n : ℕ} {C : Circuit} (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ u, x u = true → y u = true) :
    circuitFun n C x = true → circuitFun n C y = true :=
  (fold_mono C.gates (fun _ hg => monoGate_of_mem hC hg) (ofFn_mono hxy)).2 C.output

lemma mem_junk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {j : ℕ} :
    j ∈ junk G C ↔ j < C.gates.length ∧ IsDirtyAnd n G C j := by
  unfold junk gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]

/-! ### Wire values -/

/-- The value of wire `w` of `C` at the input `x`; `gateVal n C j = wireVal n C (n + j)`. -/
def wireVal (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma gateVal_eq_wireVal {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wireVal n C (n + j) x := rfl

lemma wires_length {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  change (C.gates.foldl stepWire (List.ofFn x)).length = _
  rw [fold_length]
  simp

lemma wires_split {n : ℕ} (C : Circuit) (k : ℕ) (x : Fin n → Bool) :
    C.wires (List.ofFn x)
      = (C.gates.drop k).foldl stepWire (earlierWires C k (List.ofFn x)) := by
  change C.gates.foldl stepWire (List.ofFn x) = _
  unfold earlierWires
  rw [← List.foldl_append, List.take_append_drop]

lemma earlier_length {n : ℕ} (C : Circuit) {k : ℕ} (hk : k ≤ C.gates.length)
    (x : Fin n → Bool) : (earlierWires C k (List.ofFn x)).length = n + k := by
  unfold earlierWires
  rw [fold_length]
  simp [Nat.min_eq_left hk]

lemma earlier_getD {n : ℕ} (C : Circuit) {k i : ℕ} (hk : k ≤ C.gates.length)
    (x : Fin n → Bool) (hi : i < n + k) :
    (earlierWires C k (List.ofFn x)).getD i false = wireVal n C i x := by
  unfold wireVal
  rw [wires_split C k x,
    fold_getD_lt _ _ _ (by rw [earlier_length C hk x]; exact hi)]

lemma gateAt_eq {C : Circuit} {k : ℕ} (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

lemma wireVal_gate {n : ℕ} {C : Circuit} {k : ℕ} (hk : k < C.gates.length)
    (x : Fin n → Bool) :
    wireVal n C (n + k) x = gateBit (earlierWires C k (List.ofFn x)) (gateAt C k) := by
  have h := patch_bit (C := C) hk C.gates[k] x
  rw [original_patch hk] at h
  rw [gateAt_eq hk, ← gateVal_eq_wireVal]
  exact h

lemma wireVal_input {n : ℕ} (C : Circuit) (i : Fin n) (x : Fin n → Bool) :
    wireVal n C i.val x = x i := by
  unfold wireVal
  change (C.gates.foldl stepWire (List.ofFn x)).getD i.val false = _
  rw [fold_getD_lt _ _ _ (by simp)]
  exact ofFn_getD x i

lemma wireVal_high {n : ℕ} (C : Circuit) {w : ℕ} (x : Fin n → Bool)
    (hw : n + C.gates.length ≤ w) : wireVal n C w x = false := by
  unfold wireVal
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (by rw [wires_length]; exact hw)]
  rfl

lemma wire_mono {n : ℕ} {C : Circuit} (hC : Monotone2 C) (m : ℕ) {x y : Fin n → Bool}
    (hxy : ∀ u, x u = true → y u = true) :
    wireVal n C m x = true → wireVal n C m y = true :=
  (fold_mono C.gates (fun _ hg => monoGate_of_mem hC hg) (ofFn_mono hxy)).2 m

lemma graph_false_single {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i : Fin n) :
    graphFun G ∅ (pairInput i i) = false := by
  rcases h : graphFun G ∅ (pairInput i i) with _ | _
  · rfl
  · obtain ⟨a, b, hab, ha, hb⟩ := (graph_true G (pairInput i i)).mp h
    simp only [pairInput, decide_eq_true_eq, or_self] at ha hb
    subst ha
    subst hb
    exact absurd rfl (G.ne_of_adj hab)

/-- An OR gate true at `x` reads an earlier wire that is true at `x`. -/
lemma or_descends {n : ℕ} {C : Circuit} {k : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (x : Fin n → Bool)
    (hval : wireVal n C (n + k) x = true) :
    ∃ i, i ∈ (gateAt C k).inputs ∧ i < n + k ∧ wireVal n C i x = true := by
  rw [wireVal_gate hk] at hval
  simp only [gateBit, hop, GateOp.eval, List.any_map, List.any_eq_true,
    Function.comp_apply, id_eq] at hval
  obtain ⟨i, hi, hv⟩ := hval
  have hlt : i < n + k := by
    by_contra hge
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none
      (by rw [earlier_length C (le_of_lt hk) x]; omega)] at hv
    exact absurd hv (by simp)
  exact ⟨i, hi, hlt, by rwa [earlier_getD C (le_of_lt hk) x hlt] at hv⟩

/-- An OR gate is at least each earlier wire it reads. -/
lemma or_ge {n : ℕ} {C : Circuit} {k : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) {i : ℕ} (hi : i ∈ (gateAt C k).inputs)
    (hilt : i < n + k) (y : Fin n → Bool) (hy : wireVal n C i y = true) :
    wireVal n C (n + k) y = true := by
  rw [wireVal_gate hk]
  simp only [gateBit, hop, GateOp.eval, List.any_map, List.any_eq_true,
    Function.comp_apply, id_eq]
  exact ⟨i, hi, by rwa [earlier_getD C (le_of_lt hk) y hilt]⟩

/-! ### Every edge is carried by a CLEAN AND gate

The AND gates met by a descent from the output through OR gates only are below `f_G` for
free, and each edge of `G` is true at one of them.  This is the fact an induction on the
junk count needs: junk gates always sit strictly below some clean AND gate. -/

theorem edge_has_clean_and {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : Monotone2 C) (hF : circuitFun n C = graphFun G ∅)
    {u v : Fin n} (huv : G.Adj u v) :
    ∃ k, k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      (∀ y : Fin n → Bool, gateVal n C k y = true → graphFun G ∅ y = true) ∧
      gateVal n C k (pairInput u v) = true := by
  classical
  have key : ∀ w : ℕ, (∀ y : Fin n → Bool, wireVal n C w y = true → graphFun G ∅ y = true) →
      wireVal n C w (pairInput u v) = true →
      ∃ k, k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
        (∀ y : Fin n → Bool, gateVal n C k y = true → graphFun G ∅ y = true) ∧
        gateVal n C k (pairInput u v) = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hcl hval
      by_cases hlow : w < n
      · exfalso
        have h0 : wireVal n C w (pairInput ⟨w, hlow⟩ ⟨w, hlow⟩) = true := by
          have hb := wireVal_input C (⟨w, hlow⟩ : Fin n) (pairInput ⟨w, hlow⟩ ⟨w, hlow⟩)
          simpa [pairInput] using hb
        have hbad := hcl _ h0
        rw [graph_false_single G ⟨w, hlow⟩] at hbad
        exact absurd hbad (by simp)
      · have hwk : w = n + (w - n) := by omega
        set k := w - n with hk
        by_cases hhigh : k < C.gates.length
        · have hmono : IsMonoGate (gateAt C k) := by
            rw [gateAt_eq hhigh]
            exact monoGate_of_mem hC (List.getElem_mem hhigh)
          rcases hmono with hop | hop
          · refine ⟨k, hhigh, hop, ?_, ?_⟩
            · intro y hy
              exact hcl y (by rwa [hwk, ← gateVal_eq_wireVal])
            · rw [gateVal_eq_wireVal, ← hwk]; exact hval
          · obtain ⟨i, hi, hilt, hiv⟩ := or_descends hhigh hop (pairInput u v) (by
              rw [← hwk]; exact hval)
            refine ih i (by omega) (fun y hy => hcl y ?_) hiv
            rw [hwk]
            exact or_ge hhigh hop hi hilt y hy
        · exfalso
          rw [hwk, wireVal_high C (pairInput u v) (by omega)] at hval
          exact absurd hval (by simp)
  refine key C.output (fun y hy => ?_) ?_
  · have : circuitFun n C y = true := hy
    rwa [hF] at this
  · have : circuitFun n C (pairInput u v) = true := by
      rw [hF]
      exact (graph_true G _).mpr ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
    exact this

/-! ### A clean AND gate is a star

For a clean AND gate reading wires `a` and `b`, every cross pair of the vertex sets
`Lset a` and `Lset b` is an edge of `G`; with `NoFourCycle` one of the two sets therefore
has at most one element. -/

/-- The vertices `i` with wire `m` true at the single-vertex input `1_i`. -/
def Lset (n : ℕ) (C : Circuit) (m : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => wireVal n C m (pairInput i i) = true

lemma mem_Lset {n : ℕ} {C : Circuit} {m : ℕ} {i : Fin n} :
    i ∈ Lset n C m ↔ wireVal n C m (pairInput i i) = true := by
  simp [Lset]

theorem clean_and_cross {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : Monotone2 C) {k a b : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (hin : (gateAt C k).inputs = [a, b])
    (halt : a < n + k) (hblt : b < n + k)
    (hclean : ∀ y : Fin n → Bool, gateVal n C k y = true → graphFun G ∅ y = true)
    {i i' : Fin n} (hi : i ∈ Lset n C a) (hi' : i' ∈ Lset n C b) :
    G.Adj i i' := by
  have hmono : ∀ w : Fin n, pairInput i i w = true → pairInput i i' w = true := by
    intro w hw
    simp only [pairInput, decide_eq_true_eq, or_self] at hw
    simp [pairInput, hw]
  have hmono' : ∀ w : Fin n, pairInput i' i' w = true → pairInput i i' w = true := by
    intro w hw
    simp only [pairInput, decide_eq_true_eq, or_self] at hw
    simp [pairInput, hw]
  have hav : wireVal n C a (pairInput i i') = true :=
    wire_mono hC a hmono (mem_Lset.mp hi)
  have hbv : wireVal n C b (pairInput i i') = true :=
    wire_mono hC b hmono' (mem_Lset.mp hi')
  have hgate : gateVal n C k (pairInput i i') = true := by
    rw [gateVal_eq_wireVal, wireVal_gate hk]
    simp only [gateBit, hop, hin, GateOp.eval, List.map_cons, List.map_nil,
      List.all_cons, List.all_nil, id_eq, Bool.and_true]
    rw [earlier_getD C (le_of_lt hk) _ halt, earlier_getD C (le_of_lt hk) _ hblt, hav, hbv]
    rfl
  obtain ⟨p, q, hpq, hp, hq⟩ := (graph_true G _).mp (hclean _ hgate)
  simp only [pairInput, decide_eq_true_eq] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact absurd rfl (G.ne_of_adj hpq)
  · exact hpq
  · exact hpq.symm
  · exact absurd rfl (G.ne_of_adj hpq)

theorem clean_and_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : Monotone2 C) {k a b : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (hin : (gateAt C k).inputs = [a, b])
    (halt : a < n + k) (hblt : b < n + k)
    (hclean : ∀ y : Fin n → Bool, gateVal n C k y = true → graphFun G ∅ y = true)
    (hnf : NoFourCycle G) :
    (Lset n C a).card ≤ 1 ∨ (Lset n C b).card ≤ 1 := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨i, hi, i2, hi2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (Lset n C a).card)
  obtain ⟨j, hj, j2, hj2, hne'⟩ := Finset.one_lt_card.mp (by omega : 1 < (Lset n C b).card)
  have h1 := clean_and_cross G C hC hk hop hin halt hblt hclean hi hj
  have h2 := clean_and_cross G C hC hk hop hin halt hblt hclean hi hj2
  have h3 := clean_and_cross G C hC hk hop hin halt hblt hclean hi2 hj
  have h4 := clean_and_cross G C hC hk hop hin halt hblt hclean hi2 hj2
  have hsub : ({j, j2} : Finset (Fin n)) ⊆
      Finset.univ.filter fun w => G.Adj i w ∧ G.Adj i2 w := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · simp [h1, h3]
    · simp [h2, h4]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_pair hne'] at hcard
  exact absurd (le_trans hcard (hnf i i2 hne)) (by omega)

/-! ### One-slot surgery, in its most general form

`patchOne` is everything a replacement of ONE gate can achieve.  Replacing gate `j` by any
monotone gate `h` of fan-in at most two that is
* CLEAN (below `f_G`), and
* true at `1_ab` for every edge `ab` that forcing gate `j` low would lose,
gives a circuit of the same size computing `f_G` with strictly less junk.  No hypothesis
`h ≤ gate j` is needed: where `h` is true, `f_G` is true, so nothing above can overshoot.
The one-edge repair is the case `h = edgeGate u v`. -/

lemma patch_le_orig {C : Circuit} (hC : Monotone2 C) {j : ℕ} (hj : j < C.gates.length)
    (g : Gate) (w : List Bool)
    (hbit : gateBit (earlierWires C j w) g = true →
      gateBit (earlierWires C j w) C.gates[j] = true) :
    WiresLE ((patch C j g).wires w) (C.wires w) := by
  have h := patch_mono hC hj g C.gates[j] w hbit
  rwa [original_patch hj] at h

lemma orig_le_patch {C : Circuit} (hC : Monotone2 C) {j : ℕ} (hj : j < C.gates.length)
    (g : Gate) (w : List Bool)
    (hbit : gateBit (earlierWires C j w) C.gates[j] = true →
      gateBit (earlierWires C j w) g = true) :
    WiresLE (C.wires w) ((patch C j g).wires w) := by
  have h := patch_mono hC hj C.gates[j] g w hbit
  rwa [original_patch hj] at h

theorem patchOne {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : Monotone2 C) (hF : circuitFun n C = graphFun G ∅)
    {j : ℕ} (hjunk : j ∈ junk G C) (h : Gate)
    (hmg : IsMonoGate h) (hlen : h.inputs.length ≤ 2)
    (hclean : ∀ x : Fin n → Bool,
      gateBit (earlierWires C j (List.ofFn x)) h = true → graphFun G ∅ x = true)
    (hcover : ∀ a b : Fin n, G.Adj a b →
      circuitFun n (patch C j off) (pairInput a b) = false →
      gateBit (earlierWires C j (List.ofFn (pairInput a b))) h = true) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size ≤ C.size ∧ (junk G D).card < (junk G C).card := by
  have hj := (mem_junk.mp hjunk).1
  let D := patch C j h
  have hmono : Monotone2 D := patch_isMono hC hmg hlen
  have hdown : ∀ x : Fin n → Bool, gateBit (earlierWires C j (List.ofFn x)) h = false →
      WiresLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x)) := by
    intro x hx
    refine patch_le_orig hC hj h _ (fun ht => ?_)
    rw [hx] at ht
    exact absurd ht (by simp)
  have hup : ∀ x : Fin n → Bool, gateBit (earlierWires C j (List.ofFn x)) h = true →
      WiresLE (C.wires (List.ofFn x)) (D.wires (List.ofFn x)) :=
    fun x hx => orig_le_patch hC hj h _ (fun _ => hx)
  have allEdges : ∀ a b : Fin n, G.Adj a b → circuitFun n D (pairInput a b) = true := by
    intro a b hab
    have hCtrue : circuitFun n C (pairInput a b) = true := by
      rw [hF]
      exact (graph_true G _).mpr
        ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩
    cases hcut : circuitFun n (patch C j off) (pairInput a b) with
    | true =>
      exact (patch_mono hC hj off h (List.ofFn (pairInput a b))
        (by simp [off_bit])).2 C.output hcut
    | false => exact (hup _ (hcover a b hab hcut)).2 C.output hCtrue
  have hcomp : circuitFun n D = graphFun G ∅ := by
    funext x
    cases hg : graphFun G ∅ x with
    | true =>
      obtain ⟨a, b, hab, ha, hb⟩ := (graph_true G x).mp hg
      exact circuit_mono hmono (pair_le ha hb) (allEdges a b hab)
    | false =>
      cases hDv : circuitFun n D x with
      | false => rfl
      | true =>
        exfalso
        cases hh : gateBit (earlierWires C j (List.ofFn x)) h with
        | true =>
          rw [hclean x hh] at hg
          exact absurd hg (by simp)
        | false =>
          have hCv := (hdown x hh).2 C.output hDv
          change circuitFun n C x = true at hCv
          rw [hF, hg] at hCv
          exact absurd hCv (by simp)
  have hlen2 : D.gates.length = C.gates.length := List.length_set
  have hcleanJ : j ∉ junk G D := by
    intro hmem
    obtain ⟨x, hx, hxG⟩ := (mem_junk.mp hmem).2.2.2
    change gateVal n (patch C j h) j x = true at hx
    rw [patch_bit hj] at hx
    rw [hclean x hx] at hxG
    exact absurd hxG (by simp)
  have hsub : junk G D ⊆ junk G C := by
    intro k hk
    have hne : j ≠ k := fun he => hcleanJ (he ▸ hk)
    obtain ⟨hklen, hkop, _, x, hx, hxG⟩ := mem_junk.mp hk
    have hkc : k < C.gates.length := hlen2 ▸ hklen
    have hcop : (gateAt C k).op = GateOp.and := by
      rwa [show gateAt D k = gateAt C k from gateAt_patch_ne C j k h hne] at hkop
    have hhx : gateBit (earlierWires C j (List.ofFn x)) h = false := by
      cases hb : gateBit (earlierWires C j (List.ofFn x)) h with
      | false => rfl
      | true =>
        rw [hclean x hb] at hxG
        exact absurd hxG (by simp)
    exact mem_junk.mpr ⟨hkc, hcop, hkc, x, (hdown x hhx).2 (n + k) hx, hxG⟩
  exact ⟨D, hmono, hcomp, Nat.le_of_eq hlen2,
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨hsub, fun he => hcleanJ (he.symm ▸ hjunk)⟩)⟩

/-! ### The route with measured evidence behind it

A junk-free circuit that is no larger than `C` discharges the conclusion of `repairMany`
for `C` outright: the two-edge hypothesis and `NoFourCycle` are not used.  So the whole
step follows from `m0 = s*`, that is, from the existence of a junk-free circuit no larger
than any given one.  This is the shape the small-graph verification used. -/

theorem repairMany_of_cleanNoLarger {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (cleanOpt : ∀ C : Circuit, Monotone2 C → circuitFun n C = graphFun G ∅ →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
        D.size ≤ C.size ∧ junk G D = ∅)
    (C : Circuit) (hC : Monotone2 C) (hF : circuitFun n C = graphFun G ∅)
    (hne : (junk G C).Nonempty) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size ≤ C.size ∧ (junk G D).card < (junk G C).card := by
  obtain ⟨D, hD, hDF, hDs, hDj⟩ := cleanOpt C hC hF
  exact ⟨D, hD, hDF, hDs, by
    rw [hDj, Finset.card_empty]
    exact Finset.card_pos.mpr hne⟩

/-- The repairMany statement VERBATIM, derived from the junk-free normal form.  Together
with the merged reduction that derives the normal form from repairFew and repairMany, this
shows repairMany is EQUIVALENT to the normal form: it is not a weaker stepping stone, so
no proof of it can avoid producing a junk-free circuit of size at most `C.size`.  Neither
`NoFourCycle` nor the two-edge hypothesis is used here. -/
theorem repairMany_of_normalForm
    (cleanOpt : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → Monotone2 C → circuitFun n C = graphFun G ∅ →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
        D.size ≤ C.size ∧ junk G D = ∅) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → Monotone2 C → circuitFun n C = graphFun G ∅ → (junk G C).Nonempty →
      (∀ j ∈ junk G C, ∃ a b u v, G.Adj a b ∧ G.Adj u v ∧ pairInput a b ≠ pairInput u v ∧
        circuitFun n {C with gates := replaceByConst C.gates j false} (pairInput a b) = false ∧
        circuitFun n {C with gates := replaceByConst C.gates j false} (pairInput u v) = false) →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
        (junk G D).card < (junk G C).card := by
  intro n G inst C hnf hC hF hne _
  obtain ⟨D, hD, hDF, hDs, hDj⟩ := cleanOpt n G C hnf hC hF
  exact ⟨D, hD, hDF, hDs, by
    rw [hDj, Finset.card_empty]
    exact Finset.card_pos.mpr hne⟩

/-! ### A kernel-checked instance: the hypothesis holds and surgery cannot discharge it

`hardG` is the C4-free graph on `Fin 4` with the two disjoint edges `01` and `23`, so
`f_G = x0 x1 or x2 x3`.  `hardC` computes it as a product of four ORs,
`(x0 or x2)(x1 or x3)(x1 or x2)(x0 or x3)`, whose minimal hitting sets are exactly `01`
and `23`.  Gates 2 and 4 are junk and each one, forced low, loses BOTH edges, so the
hypothesis of `repairMany` holds here with two DISJOINT edges at stake.

For this instance the two operands of gate 2 are `x0 or x2` and `x1 or x3`: both are true
at `1_01` and at `1_23`, every wire below gate 2 is dirty, and no star covers two disjoint
edges - so `patchOne` has no applicable `h`.  An exhaustive search over all legal gates in
every slot (and over all PAIRS of slots) finds no circuit computing `f_G` with less junk:
at least THREE of the seven gates must change.  The witness `D` for this `C` is the padded
clean circuit `and[0,1], and[2,3], or[4,5]`, which is not a patch of `C` in any slot. -/

/-- The graph with the two disjoint edges `01` and `23` on `Fin 4`. -/
def hardG : SimpleGraph (Fin 4) := edgeGraph 4 [(0, 1), (2, 3)]

instance hardG_dec : DecidableRel hardG.Adj :=
  inferInstanceAs (DecidableRel (edgeGraph 4 [(0, 1), (2, 3)]).Adj)

/-- A seven-gate Monotone2 circuit for `f_hardG` with two junk AND gates. -/
def hardC : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [4, 5]⟩,
    ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [0, 3]⟩,
    ⟨GateOp.and, [8, 9]⟩], 10⟩

theorem hardG_noFourCycle : NoFourCycle hardG := by decide

theorem hardC_mono : Monotone2 hardC := by
  intro g hg
  fin_cases hg <;> exact ⟨by simp, by simp⟩

theorem hardC_computes : ∀ x : Fin 4 → Bool, circuitFun 4 hardC x = graphFun hardG ∅ x := by
  decide

theorem hardC_junk : junk hardG hardC = {2, 4} := by decide

/-- Both junk gates are load-bearing on the two DISJOINT edges `01` and `23`, so the
hypothesis of `repairMany` is satisfied, with `repairFew` inapplicable at either gate. -/
theorem hardC_loadBearing :
    (circuitFun 4 (patch hardC 2 off) (pairInput 0 1) = false ∧
      circuitFun 4 (patch hardC 2 off) (pairInput 2 3) = false) ∧
    (circuitFun 4 (patch hardC 4 off) (pairInput 0 1) = false ∧
      circuitFun 4 (patch hardC 4 off) (pairInput 2 3) = false) := by
  decide

theorem hardG_adj : hardG.Adj 0 1 ∧ hardG.Adj 2 3 ∧
    (pairInput (0 : Fin 4) 1 ≠ pairInput (2 : Fin 4) 3) := by
  refine ⟨by decide, by decide, fun hcon => ?_⟩
  have := congrFun hcon 0
  simp [pairInput] at this

/-- The clean witness for `hardC`: same size, junk-free, and NOT a patch of `hardC`. -/
def hardD : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.or, []⟩, ⟨GateOp.or, []⟩, ⟨GateOp.or, []⟩, ⟨GateOp.or, []⟩], 6⟩

theorem hardD_mono : Monotone2 hardD := by
  intro g hg
  fin_cases hg <;> exact ⟨by simp, by simp⟩

theorem hardD_computes : ∀ x : Fin 4 → Bool, circuitFun 4 hardD x = graphFun hardG ∅ x := by
  decide

theorem hardD_clean : junk hardG hardD = ∅ := by decide

theorem hardD_size : hardD.size ≤ hardC.size := by decide

/-! ### The cone of a gate

`cones_len`, `cones_char`, `inCone_iff` and `inCone_trans` are the cone facts the descent
below needs: a wire read by a gate in the cone of `k` is itself in the cone of `k`. -/

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

/-- A wire that gate `k` reads and that is an earlier gate lies in the cone of gate `k`. -/
lemma inCone_of_reads {n : ℕ} {C : Circuit} {k i : ℕ} (hk : k < C.gates.length) (hik : i < k)
    (hin : n + i ∈ (gateAt C k).inputs) : InCone n C i k :=
  (inCone_iff n C i k).mpr ⟨hk, i, hik, hin, Or.inl rfl⟩

/-! ### The descent from an owning AND gate

A gate that OWNS the pair `uv` has no AND gate of its cone true at `1_uv`, so from each wire it
reads the descent through gates true at `1_uv` meets no AND gate and ends at an INPUT, which can
only be `u` or `v`.  Lifting back up through the OR gates of that descent, the wire is true at
the single-vertex input of that endpoint: it lies in the `Lset` of the wire. -/

lemma descend {n : ℕ} {C : Circuit} (hC : Monotone2 C) {k : ℕ} (hk : k < C.gates.length)
    {u v : Fin n}
    (hmin : ∀ i < k, InCone n C i k → (gateAt C i).op = GateOp.and →
      gateVal n C i (pairInput u v) = false) :
    ∀ w : ℕ, (w < n ∨ ∃ i, w = n + i ∧ i < k ∧ InCone n C i k) →
      wireVal n C w (pairInput u v) = true →
      ∃ p : Fin n, (p = u ∨ p = v) ∧ wireVal n C w (pairInput p p) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hloc hval
    rcases hloc with hlow | ⟨i, hwi, hik, hcone⟩
    · refine ⟨⟨w, hlow⟩, ?_, ?_⟩
      · rw [wireVal_input C ⟨w, hlow⟩] at hval
        simpa only [pairInput, decide_eq_true_eq] using hval
      · rw [wireVal_input C ⟨w, hlow⟩]
        simp [pairInput]
    · subst hwi
      have hilen : i < C.gates.length := lt_trans hik hk
      have hmono : IsMonoGate (gateAt C i) := by
        rw [gateAt_eq hilen]
        exact monoGate_of_mem hC (List.getElem_mem hilen)
      rcases hmono with hop | hop
      · exfalso
        have hbad := hmin i hik hcone hop
        rw [gateVal_eq_wireVal] at hbad
        rw [hbad] at hval
        exact absurd hval (by simp)
      · obtain ⟨j, hjin, hjlt, hjval⟩ := or_descends hilen hop (pairInput u v) hval
        have hjloc : j < n ∨ ∃ i', j = n + i' ∧ i' < k ∧ InCone n C i' k := by
          by_cases hjn : j < n
          · exact Or.inl hjn
          · refine Or.inr ⟨j - n, by omega, by omega, ?_⟩
            have hji : InCone n C (j - n) i :=
              (inCone_iff n C (j - n) i).mpr
                ⟨hilen, j - n, by omega, by rw [show n + (j - n) = j by omega]; exact hjin,
                  Or.inl rfl⟩
            exact inCone_trans n C (j - n) i hji k hcone
        obtain ⟨p, hp, hpv⟩ := ih j (by omega) hjloc hjval
        exact ⟨p, hp, or_ge hilen hop hjin hjlt (pairInput p p) hpv⟩

/-! ### An owned edge splits between the two operands

Everything above is assembled here: a CLEAN AND gate that owns an edge reads exactly two earlier
wires, and the two endpoints of the edge lie one in each operand vertex set.  With
`clean_and_star` (one of the two sets is a single vertex) that single vertex lies on EVERY edge
the gate owns: a clean AND gate owns a star. -/

lemma and_bit_true {w : List Bool} {g : Gate} (hop : g.op = GateOp.and) :
    gateBit w g = true ↔ ∀ i ∈ g.inputs, w.getD i false = true := by
  simp only [gateBit, hop, GateOp.eval, List.all_map, List.all_eq_true,
    Function.comp_apply, id_eq]

lemma gateVal_and_iff {n : ℕ} {C : Circuit} {k : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C k x = true ↔
      ∀ i ∈ (gateAt C k).inputs, (earlierWires C k (List.ofFn x)).getD i false = true := by
  rw [gateVal_eq_wireVal, wireVal_gate hk]
  exact and_bit_true hop

lemma operand_lt {n : ℕ} {C : Circuit} {k : ℕ} (hk : k ≤ C.gates.length) (x : Fin n → Bool)
    {i : ℕ} (h : (earlierWires C k (List.ofFn x)).getD i false = true) : i < n + k := by
  by_contra hge
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (by rw [earlier_length C hk x]; omega)] at h
  exact absurd h (by simp)

/-- An AND gate all of whose operands hold the single vertex `p` is true at `1_p`. -/
lemma gateVal_of_Lset {n : ℕ} {C : Circuit} {k : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) {p : Fin n}
    (h : ∀ i ∈ (gateAt C k).inputs, i < n + k ∧ p ∈ Lset n C i) :
    gateVal n C k (pairInput p p) = true := by
  rw [gateVal_and_iff hk hop]
  intro i hi
  obtain ⟨hilt, hmem⟩ := h i hi
  rw [earlier_getD C (le_of_lt hk) _ hilt]
  exact mem_Lset.mp hmem

/-- Each wire read by an AND gate that owns the pair `uv` is an earlier wire and holds one of the
two endpoints of `uv` alone. -/
lemma owned_operand_endpoint {n : ℕ} {C : Circuit} (hC : Monotone2 C) {k : ℕ} {u v : Fin n}
    (ho : Owns n C k u v) {i : ℕ} (hi : i ∈ (gateAt C k).inputs) :
    i < n + k ∧ ∃ p : Fin n, (p = u ∨ p = v) ∧ p ∈ Lset n C i := by
  obtain ⟨hk, hop, hval, hmin⟩ := ho
  have hbits := (gateVal_and_iff hk hop (pairInput u v)).mp hval
  have hilt : i < n + k := operand_lt (le_of_lt hk) _ (hbits i hi)
  refine ⟨hilt, ?_⟩
  have hwv : wireVal n C i (pairInput u v) = true := by
    rw [← earlier_getD C (le_of_lt hk) (pairInput u v) hilt]
    exact hbits i hi
  have hloc : i < n ∨ ∃ i', i = n + i' ∧ i' < k ∧ InCone n C i' k := by
    by_cases hin : i < n
    · exact Or.inl hin
    · exact Or.inr ⟨i - n, by omega, by omega,
        inCone_of_reads hk (by omega) (by rw [show n + (i - n) = i by omega]; exact hi)⟩
  obtain ⟨p, hp, hpv⟩ := descend hC hk hmin i hloc hwv
  exact ⟨p, hp, mem_Lset.mpr hpv⟩

/-- A clean AND gate that owns an edge reads exactly two earlier wires, and the endpoints of
that edge lie one in each operand vertex set. -/
theorem owns_splits {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hC : Monotone2 C) {k : ℕ} {u v : Fin n} (ho : Owns n C k u v)
    (hclean : ∀ y : Fin n → Bool, gateVal n C k y = true → graphFun G ∅ y = true) :
    ∃ a b : ℕ, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k ∧
      ((u ∈ Lset n C a ∧ v ∈ Lset n C b) ∨ (v ∈ Lset n C a ∧ u ∈ Lset n C b)) := by
  have hk := ho.1
  have hop := ho.2.1
  have hlen : (gateAt C k).inputs.length ≤ 2 := by
    rw [gateAt_eq hk]
    exact (hC _ (List.getElem_mem hk)).2
  have hsingle : ∀ p : Fin n, gateVal n C k (pairInput p p) = true → False := by
    intro p hpv
    have hg := hclean _ hpv
    rw [graph_false_single G p] at hg
    exact absurd hg (by simp)
  cases hL : (gateAt C k).inputs with
  | nil =>
    exact absurd (gateVal_of_Lset hk hop (p := u) (by rw [hL]; simp)) (fun h => hsingle u h)
  | cons a as =>
    cases has : as with
    | nil =>
      exfalso
      obtain ⟨halt, p, _, hpa⟩ := owned_operand_endpoint hC ho (i := a) (by rw [hL]; simp)
      refine hsingle p (gateVal_of_Lset hk hop (p := p) ?_)
      intro i hi
      rw [hL, has] at hi
      simp only [List.mem_singleton] at hi
      subst hi
      exact ⟨halt, hpa⟩
    | cons b bs =>
      cases hbs : bs with
      | cons c cs =>
        exfalso
        rw [hL, has, hbs] at hlen
        simp at hlen
      | nil =>
        have hmemA : a ∈ (gateAt C k).inputs := by rw [hL]; simp
        have hmemB : b ∈ (gateAt C k).inputs := by rw [hL, has, hbs]; simp
        obtain ⟨halt, p, hp, hpa⟩ := owned_operand_endpoint hC ho hmemA
        obtain ⟨hblt, q, hq, hqb⟩ := owned_operand_endpoint hC ho hmemB
        have hpq : p ≠ q := by
          intro he
          subst he
          refine hsingle p (gateVal_of_Lset hk hop (p := p) ?_)
          intro i hi
          rw [hL, has, hbs] at hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact ⟨halt, hpa⟩
          · exact ⟨hblt, hqb⟩
        refine ⟨a, b, by simp only [hL, has, hbs], halt, hblt, ?_⟩
        rcases hp with rfl | rfl
        · rcases hq with rfl | rfl
          · exact absurd rfl hpq
          · exact Or.inl ⟨hpa, hqb⟩
        · rcases hq with rfl | rfl
          · exact Or.inr ⟨hpa, hqb⟩
          · exact absurd rfl hpq

/-- THE STAR PROFILE, for the gates that are below `f_G`: a clean AND gate either owns no edge of
`G`, or some vertex lies on every edge of `G` it owns.  Only `NoFourCycle` is used. -/
theorem clean_owns_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hC : Monotone2 C) (hnf : NoFourCycle G) (k : ℕ)
    (hclean : ∀ y : Fin n → Bool, gateVal n C k y = true → graphFun G ∅ y = true) :
    (∀ u v : Fin n, G.Adj u v → ¬ Owns n C k u v) ∨
      ∃ c : Fin n, ∀ u v : Fin n, G.Adj u v → Owns n C k u v → u = c ∨ v = c := by
  classical
  by_cases hex : ∃ u v : Fin n, G.Adj u v ∧ Owns n C k u v
  · obtain ⟨u, v, hadj, ho⟩ := hex
    obtain ⟨a, b, hin, halt, hblt, hsplit⟩ := owns_splits G C hC ho hclean
    have hstar := clean_and_star G C hC ho.1 ho.2.1 hin halt hblt hclean hnf
    have hsame : ∀ u' v' : Fin n, Owns n C k u' v' →
        ((u' ∈ Lset n C a ∧ v' ∈ Lset n C b) ∨ (v' ∈ Lset n C a ∧ u' ∈ Lset n C b)) := by
      intro u' v' ho'
      obtain ⟨a', b', hin', _, _, hsplit'⟩ := owns_splits G C hC ho' hclean
      have he : ([a, b] : List ℕ) = [a', b'] := by rw [← hin, hin']
      simp only [List.cons.injEq, and_true] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hsplit'
    rcases hstar with hcard | hcard
    · obtain ⟨c, hc⟩ : ∃ c : Fin n, c ∈ Lset n C a := by
        rcases hsplit with ⟨h, _⟩ | ⟨h, _⟩
        · exact ⟨u, h⟩
        · exact ⟨v, h⟩
      refine Or.inr ⟨c, fun u' v' _ ho' => ?_⟩
      rcases hsame u' v' ho' with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Or.inl (Finset.card_le_one.mp hcard u' h1 c hc)
      · exact Or.inr (Finset.card_le_one.mp hcard v' h1 c hc)
    · obtain ⟨c, hc⟩ : ∃ c : Fin n, c ∈ Lset n C b := by
        rcases hsplit with ⟨_, h⟩ | ⟨_, h⟩
        · exact ⟨v, h⟩
        · exact ⟨u, h⟩
      refine Or.inr ⟨c, fun u' v' _ ho' => ?_⟩
      rcases hsame u' v' ho' with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact Or.inr (Finset.card_le_one.mp hcard v' h2 c hc)
      · exact Or.inl (Finset.card_le_one.mp hcard u' h2 c hc)
  · refine Or.inl (fun u v hadj ho => hex ⟨u, v, hadj, ho⟩)

/-! ### Pairwise meeting owned edges, and the row conditional on ONE named lemma

Two facts finish the row from the material above.

* `star_of_pairwise_meet`: in a TRIANGLE-FREE graph, a symmetric family of edges that meets
  pairwise has a common vertex.  Three edges meeting pairwise with no common vertex are a
  triangle, so this is exactly where the row's triangle-free hypothesis earns its place.
* `clean_owns_star`: a clean AND gate owns a star (proved above, from `NoFourCycle`).

So the ONLY thing missing is the case of an AND gate that owns two DISJOINT edges.  Such a gate
cannot be below `f_G`: `clean_owns_star` would make its owned edges a star.  The named lemma is
therefore

    a JUNK AND gate owns no two disjoint edges of `G`

(`junkOwnsNoDisjointPair` below), and the row follows from it.  Nothing in this file proves it,
and the reason is sharp: for a gate not below `f_G` the cross pairs of its two operand vertex
sets need not be edges, so `clean_and_cross` says nothing, and `pathC` below is a circuit for a
4-cycle-free, triangle-free graph in which exactly this happens. -/

/-- `pairInput` does not see the order of its two vertices. -/
lemma pairInput_comm {n : ℕ} (u v : Fin n) : pairInput u v = pairInput v u := by
  funext w
  simp [pairInput, or_comm]

/-- Ownership of a pair is symmetric in the pair. -/
lemma owns_comm {n : ℕ} {C : Circuit} {j : ℕ} {u v : Fin n} (ho : Owns n C j u v) :
    Owns n C j v u := by
  obtain ⟨hk, hop, hval, hmin⟩ := ho
  rw [pairInput_comm u v] at hval hmin
  exact ⟨hk, hop, hval, hmin⟩

/-- In a triangle-free graph, a symmetric family of edges that meets pairwise has a common
vertex.  (Three edges meeting pairwise with no common vertex form a triangle.) -/
lemma star_of_pairwise_meet {n : ℕ} {G : SimpleGraph (Fin n)}
    (htri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (P : Fin n → Fin n → Prop) (hsub : ∀ u v, P u v → G.Adj u v)
    (hsymm : ∀ u v, P u v → P v u)
    (hmeet : ∀ u v u' v', P u v → P u' v' → u = u' ∨ u = v' ∨ v = u' ∨ v = v') :
    (∀ u v, ¬ P u v) ∨ ∃ c, ∀ u v, P u v → u = c ∨ v = c := by
  classical
  by_cases hex : ∃ u v, P u v
  · obtain ⟨a, b, hab⟩ := hex
    by_cases hA : ∀ u v, P u v → u = a ∨ v = a
    · exact Or.inr ⟨a, hA⟩
    by_cases hB : ∀ u v, P u v → u = b ∨ v = b
    · exact Or.inr ⟨b, hB⟩
    exfalso
    push_neg at hA hB
    obtain ⟨p, q, hpq, hpa, hqa⟩ := hA
    obtain ⟨r, s, hrs, hrb, hsb⟩ := hB
    -- the edge `pq`, which avoids `a`, meets `ab`, so it carries `b`
    have hbx : ∃ x : Fin n, P b x ∧ x ≠ a := by
      rcases hmeet p q a b hpq hab with h | h | h | h
      · exact absurd h hpa
      · exact ⟨q, by rw [← h]; exact hpq, hqa⟩
      · exact absurd h hqa
      · exact ⟨p, by rw [← h]; exact hsymm p q hpq, hpa⟩
    -- the edge `rs`, which avoids `b`, meets `ab`, so it carries `a`
    have hay : ∃ y : Fin n, P a y ∧ y ≠ b := by
      rcases hmeet r s a b hrs hab with h | h | h | h
      · exact ⟨s, by rw [← h]; exact hrs, hsb⟩
      · exact absurd h hrb
      · exact ⟨r, by rw [← h]; exact hsymm r s hrs, hrb⟩
      · exact absurd h hsb
    obtain ⟨x, hbxP, hxa⟩ := hbx
    obtain ⟨y, hayP, hyb⟩ := hay
    -- the two of them meet, and the only way left is `x = y`: a triangle `a b x`
    have hxy : x = y := by
      rcases hmeet b x a y hbxP hayP with h | h | h | h
      · exact absurd h.symm (G.ne_of_adj (hsub a b hab))
      · exact absurd h.symm hyb
      · exact absurd h hxa
      · exact h
    subst hxy
    exact htri a b x (hsub a b hab) (hsub b x hbxP) (hsub a x hayP).symm
  · exact Or.inl fun u v huv => hex ⟨u, v, huv⟩

/-- THE ROW, granted the one named lemma: in a least monotone circuit for the edge function of a
triangle-free, 4-cycle-free graph, a JUNK AND gate (one not below `f_G`) owns no two DISJOINT
edges of `G`.

The row's own per-gate three-way disjunction and its hypothesis on the gates before `k` are not
used, and the witness is the circuit itself: granted the lemma, EVERY AND gate owns a star. -/
theorem step_of_junkOwnsNoDisjointPair
    (junkOwnsNoDisjointPair :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
        (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → NoFourCycle G →
        IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
        ∀ (j : ℕ) (u v u' v' : Fin n), G.Adj u v → G.Adj u' v' →
          Owns n C j u v → Owns n C j u' v' →
          ¬ (u = u' ∨ u = v' ∨ v = u' ∨ v = v') →
          ∀ y : Fin n → Bool, gateVal n C j y = true → graphFun G ∅ y = true) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →     PEqualNP.TopForm.NoFourCycle x2 →       have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Fin x1 → Fin x1 → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 x9 : Fin x1) => x2.Adj x8 x9 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x8 x9;       have x7 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x7 ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ ∀ (x8 : ℕ), (∀ (x9 x10 : Fin x1), ¬x6 x7 x8 x9 x10) ∨ (∃ (x9 : Fin x1) (x10 : Fin x1), x6 x7 x8 x9 x10 ∧ ∀ (x11 x12 : Fin x1), x6 x7 x8 x11 x12 → x11 = x9 ∨ x12 = x9 ∨ x11 = x10 ∨ x12 = x10) ∨ ∃ (x9 : Fin x1) (x10 : Fin x1) (x11 : Fin x1) (x12 : Fin x1) (x13 : Fin x1), x6 x7 x8 x9 x10 ∧ x6 x7 x8 x10 x11 ∧ x6 x7 x8 x11 x12 ∧ x6 x7 x8 x12 x13 ∧ x6 x7 x8 x13 x9 ∧ (∀ (x14 x15 : Fin x1), x6 x7 x8 x14 x15 → x14 = x9 ∨ x14 = x10 ∨ x14 = x11 ∨ x14 = x12 ∨ x14 = x13) ∧ PEqualNP.EdgeOwnership.gateVal x1 x7 x8 (PEqualNP.EdgeOwnership.pairInput x9 x9) = Bool.true;       have x8 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : ℕ) => ∀ x10 < x9, (∀ (x12 x13 : Fin x1), ¬x6 x8 x10 x12 x13) ∨ ∃ (x12 : Fin x1), ∀ (x13 x14 : Fin x1), x6 x8 x10 x13 x14 → x13 = x12 ∨ x14 = x12;       ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ), x7 x9 → x10 < x9.size → x8 x9 x10 → ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit), x7 x14 ∧ x8 x14 (x10 + (1 : ℕ)) := by
  classical
  intro n G inst htri hnf OwnsE Inv Star C k hInv hk hstar
  refine ⟨C, hInv, ?_⟩
  intro j _
  have hC : Monotone2 C := hInv.1.1
  have hF : circuitFun n C = graphFun G ∅ := hInv.2.1
  by_cases hmeet : ∀ u v u' v' : Fin n, (G.Adj u v ∧ Owns n C j u v) →
      (G.Adj u' v' ∧ Owns n C j u' v') → (u = u' ∨ u = v' ∨ v = u' ∨ v = v')
  · exact star_of_pairwise_meet htri (fun u v => G.Adj u v ∧ Owns n C j u v)
      (fun _ _ h => h.1) (fun _ _ h => ⟨h.1.symm, owns_comm h.2⟩) hmeet
  · push_neg at hmeet
    obtain ⟨u, v, u', v', h1, h2, hdisj⟩ := hmeet
    have hclean := junkOwnsNoDisjointPair n G C htri hnf hInv.1 hF j u v u' v'
      h1.1 h2.1 h1.2 h2.2 (by tauto)
    rcases clean_owns_star G C hC hnf j hclean with h | ⟨c, hc⟩
    · exact Or.inl fun a b hab => h a b hab.1 hab.2
    · exact Or.inr ⟨c, fun a b hab => hc a b hab.1 hab.2⟩

/-- The same row from the plainer, stronger lemma: a junk AND gate owns no edge of `G` at all.
It needs neither the pairwise-meeting step nor triangle-freeness. -/
theorem step_of_owningClean
    (owningAndIsClean : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → NoFourCycle G →
      IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
      ∀ (j : ℕ) (u v : Fin n), G.Adj u v → Owns n C j u v →
        ∀ y : Fin n → Bool, gateVal n C j y = true → graphFun G ∅ y = true) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →     PEqualNP.TopForm.NoFourCycle x2 →       have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Fin x1 → Fin x1 → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 x9 : Fin x1) => x2.Adj x8 x9 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x8 x9;       have x7 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x7 ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ ∀ (x8 : ℕ), (∀ (x9 x10 : Fin x1), ¬x6 x7 x8 x9 x10) ∨ (∃ (x9 : Fin x1) (x10 : Fin x1), x6 x7 x8 x9 x10 ∧ ∀ (x11 x12 : Fin x1), x6 x7 x8 x11 x12 → x11 = x9 ∨ x12 = x9 ∨ x11 = x10 ∨ x12 = x10) ∨ ∃ (x9 : Fin x1) (x10 : Fin x1) (x11 : Fin x1) (x12 : Fin x1) (x13 : Fin x1), x6 x7 x8 x9 x10 ∧ x6 x7 x8 x10 x11 ∧ x6 x7 x8 x11 x12 ∧ x6 x7 x8 x12 x13 ∧ x6 x7 x8 x13 x9 ∧ (∀ (x14 x15 : Fin x1), x6 x7 x8 x14 x15 → x14 = x9 ∨ x14 = x10 ∨ x14 = x11 ∨ x14 = x12 ∨ x14 = x13) ∧ PEqualNP.EdgeOwnership.gateVal x1 x7 x8 (PEqualNP.EdgeOwnership.pairInput x9 x9) = Bool.true;       have x8 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : ℕ) => ∀ x10 < x9, (∀ (x12 x13 : Fin x1), ¬x6 x8 x10 x12 x13) ∨ ∃ (x12 : Fin x1), ∀ (x13 x14 : Fin x1), x6 x8 x10 x13 x14 → x13 = x12 ∨ x14 = x12;       ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ), x7 x9 → x10 < x9.size → x8 x9 x10 → ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit), x7 x14 ∧ x8 x14 (x10 + (1 : ℕ)) := by
  classical
  intro n G inst htri hnf OwnsE Inv Star C k hInv hk hstar
  refine ⟨C, hInv, ?_⟩
  intro j _
  have hC : Monotone2 C := hInv.1.1
  have hF : circuitFun n C = graphFun G ∅ := hInv.2.1
  by_cases hex : ∃ u v : Fin n, G.Adj u v ∧ Owns n C j u v
  · obtain ⟨u, v, hadj, ho⟩ := hex
    have hclean := owningAndIsClean n G C htri hnf hInv.1 hF j u v hadj ho
    rcases clean_owns_star G C hC hnf j hclean with h | ⟨c, hc⟩
    · exact Or.inl fun u' v' hcon => h u' v' hcon.1 hcon.2
    · exact Or.inr ⟨c, fun u' v' hcon => hc u' v' hcon.1 hcon.2⟩
  · exact Or.inl fun u' v' hcon => hex ⟨u', v', hcon.1, hcon.2⟩

/-! ### Why the missing lemma cannot be dropped: minimality is load-bearing

`pathG` is the path `0 - 1 - 2 - 3`: triangle-free and 4-cycle-free.  `pathC` computes its edge
function and its gate `1` is an AND gate equal to `x1 or x2`, so it is true at every edge of
`pathG` and at no AND gate below it, hence it OWNS all three edges.  They are covered by the two
ends `1, 2` of one owned edge - the row's SECOND disjunct - and no single vertex lies on all
three, so the star fails at that gate.  The gate is not below `f_G` (it is true at the
single-vertex input `1_1`), which is the only reason the cross-pair argument of
`clean_and_cross` does not apply.

So no proof of the row can get the star at gate `k` from the three-way disjunction and the two
graph hypotheses alone: this circuit satisfies all of them and fails the star.  What rules it out
is `IsMinimalMonoCircuit`, and that is exactly the force `owningAndIsClean` has to supply. -/

/-- The path `0 - 1 - 2 - 3` on `Fin 4`. -/
def pathG : SimpleGraph (Fin 4) := edgeGraph 4 [(0, 1), (1, 2), (2, 3)]

instance pathG_dec : DecidableRel pathG.Adj :=
  inferInstanceAs (DecidableRel (edgeGraph 4 [(0, 1), (1, 2), (2, 3)]).Adj)

/-- A circuit for the edge function of `pathG` whose gate `1` owns a 2-covered non-star. -/
def pathC : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [4, 4]⟩, ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [1, 2]⟩,
    ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [9, 8]⟩], 10⟩

theorem pathG_triangleFree :
    ∀ a b c : Fin 4, pathG.Adj a b → pathG.Adj b c → ¬ pathG.Adj c a := by decide

theorem pathG_noFourCycle : NoFourCycle pathG := by decide

theorem pathC_mono : Monotone2 pathC := by
  intro g hg
  fin_cases hg <;> exact ⟨by simp, by simp⟩

theorem pathC_computes : ∀ x : Fin 4 → Bool, circuitFun 4 pathC x = graphFun pathG ∅ x := by
  decide

/-- Gate `1` of `pathC` satisfies the row's SECOND disjunct: the edges it owns are covered by the
two ends of one of them. -/
theorem pathC_twoCover :
    ∃ a b : Fin 4, (pathG.Adj a b ∧ Owns 4 pathC 1 a b) ∧
      ∀ u v : Fin 4, pathG.Adj u v ∧ Owns 4 pathC 1 u v →
        u = a ∨ v = a ∨ u = b ∨ v = b := by decide

/-- And it owns no star: it owns an edge, and no vertex lies on every edge it owns. -/
theorem pathC_notStar :
    ¬ ((∀ u v : Fin 4, ¬ (pathG.Adj u v ∧ Owns 4 pathC 1 u v)) ∨
      ∃ c : Fin 4, ∀ u v : Fin 4, pathG.Adj u v ∧ Owns 4 pathC 1 u v → u = c ∨ v = c) := by
  decide

/-- Gate `0`, the only earlier gate, owns nothing, so the row's hypothesis on the gates before
`k = 1` holds as well. -/
theorem pathC_starBelow :
    ∀ j < 1, (∀ u v : Fin 4, ¬ (pathG.Adj u v ∧ Owns 4 pathC j u v)) ∨
      ∃ c : Fin 4, ∀ u v : Fin 4, pathG.Adj u v ∧ Owns 4 pathC j u v → u = c ∨ v = c := by
  decide

/-- Every gate satisfies the row's per-gate disjunction: the first two disjuncts already do,
so the whole hypothesis of the row EXCEPT `IsMinimalMonoCircuit` holds for `pathC`. -/
theorem pathC_profile_small :
    ∀ j < 7, (∀ u v : Fin 4, ¬ (pathG.Adj u v ∧ Owns 4 pathC j u v)) ∨
      ∃ a b : Fin 4, (pathG.Adj a b ∧ Owns 4 pathC j a b) ∧
        ∀ u v : Fin 4, pathG.Adj u v ∧ Owns 4 pathC j u v →
          u = a ∨ v = a ∨ u = b ∨ v = b := by decide

theorem pathC_profile :
    ∀ j : ℕ, (∀ u v : Fin 4, ¬ (pathG.Adj u v ∧ Owns 4 pathC j u v)) ∨
      ∃ a b : Fin 4, (pathG.Adj a b ∧ Owns 4 pathC j a b) ∧
        ∀ u v : Fin 4, pathG.Adj u v ∧ Owns 4 pathC j u v →
          u = a ∨ v = a ∨ u = b ∨ v = b := by
  intro j
  by_cases hj : j < 7
  · exact pathC_profile_small j hj
  · refine Or.inl fun u v h => ?_
    have hlen := h.2.1
    simp only [pathC, List.length_cons, List.length_nil] at hlen
    omega
end PEqualNP.Outside.ZZStar
