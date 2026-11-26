import PEqualNP.Defs

/-!
What the missing lemma of the star-profile row really is.

The row L-meta-5377 is closed by one named lemma, `junkOwnsNoDisjointPair`: in a LEAST
monotone circuit for the edge function of a triangle-free, 4-cycle-free graph, an AND gate
that OWNS two DISJOINT edges and is not below `f_G` would have to be below `f_G`.  This
file proves, from `PEqualNP.Defs` alone, that the `junk` qualifier in that lemma carries no
weight and that the lemma is not a weaker stepping stone towards the star profile: it IS the
star profile, for the same circuit, as an equivalence.

* `owns_disjoint_dirty`: under `NoFourCycle` alone (no minimality, no `ReadsBack`, no
  triangle-freeness, and no hypothesis that `C` computes `f_G`), an AND gate of a
  `Monotone2` circuit that owns two disjoint EDGES of `G` is NEVER below `f_G`.  So the
  hypothesis of `junkOwnsNoDisjointPair` can never be met together with its conclusion:
  the lemma says exactly that no gate owns two disjoint edges.

* `noDisjointOwned_iff_starProfile`: with triangle-freeness added, no gate owning two
  disjoint edges is EQUIVALENT to `HasStarProfile n G C`, the row's own conclusion.

* `lemmaBody_iff_starProfile` and `junkLemma_iff_starProfile`: putting the two together,
  the body of `junkOwnsNoDisjointPair` for a circuit is equivalent to the star profile of
  that circuit, and the universally quantified lemma is equivalent to the statement that
  every least monotone circuit of a triangle-free, 4-cycle-free graph has a star profile.

The practical reading.  `clean_owns_star` of the companion file gives the star profile for
the gates BELOW `f_G`; the gates not below `f_G` are all that is left, and the work above
shows that for them the row's conditional has no slack at all.  Whatever proves
`junkOwnsNoDisjointPair` proves the whole star profile, and the force has to come from
`IsMinimalMonoCircuit`, since the counterexample `pathC` of the companion file satisfies
every other hypothesis of the row and fails the star.

Measured evidence for the lemma, by exact synthesis with a simulator transcribed from the
definitions below (SAT, cadical): for EVERY triangle-free, 4-cycle-free graph on at most 6
vertices with no isolated vertex and two disjoint edges (2 on four vertices, 4 on five, 11
on six, up to isomorphism), and for 17 of the 24 such graphs on seven vertices, NO
minimum-size `Monotone2` circuit for `f_G` has a gate owning two disjoint edges.  The least
size itself came out as the number of edges plus the vertex cover number minus one on every
one of those graphs.  And the margin is one gate: for 8 of the 15 five- and six-vertex
graphs the least size of a circuit for `f_G` WITH a gate owning two disjoint edges is
exactly one more than the least size of a circuit for `f_G`.  The lemma is therefore true
at that scale and tight to a single gate.

AND THE ONE-SLOT SURGERIES DO NOT REACH IT.  For seven of those one-gate-above circuits,
every one-gate reduction was tried exhaustively: delete gate `r` and redirect every read of
its wire to any other wire, input, gate or nonexistent (the `bypass` of the merged artifact
L-meta-8237, the most general surgery that removes exactly one gate).  NONE of them still
computes `f_G`, for any of the seven circuits.  Every size-preserving one-slot patch was
tried as well - replace one gate by any AND or OR of any two earlier wires - and none gives
a circuit that computes `f_G` and has no owning gate.  So the smaller circuit that minimality
promises is not a local modification of the counterexample: it has a different gate
structure.  `patchOne`, `reduce` and a collapse to one operand are therefore all unable to
produce the contradiction, and the smaller circuit has to be built globally, which is the
same move the universal lower bound needs.  That, in one sentence, is the obstacle.

The infrastructure up to `star_of_pairwise_meet` is copied verbatim from the companion
file, where it is already kernel-checked; the new material starts at `graph_pair_false`.
-/

namespace PEqualNP.Outside.L_meta_zzjunk

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

lemma graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

/-- The value of wire `w` of `C` at the input `x`; `gateVal n C j = wireVal n C (n + j)`. -/
def wireVal (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma gateVal_eq_wireVal {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wireVal n C (n + j) x := rfl

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

lemma wire_mono {n : ℕ} {C : Circuit} (hC : Monotone2 C) (m : ℕ) {x y : Fin n → Bool}
    (hxy : ∀ u, x u = true → y u = true) :
    wireVal n C m x = true → wireVal n C m y = true :=
  (fold_mono C.gates (fun _ hg => monoGate_of_mem hC hg) (ofFn_mono hxy)).2 m

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

/-- The vertices `i` with wire `m` true at the single-vertex input `1_i`. -/
def Lset (n : ℕ) (C : Circuit) (m : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => wireVal n C m (pairInput i i) = true

lemma mem_Lset {n : ℕ} {C : Circuit} {m : ℕ} {i : Fin n} :
    i ∈ Lset n C m ↔ wireVal n C m (pairInput i i) = true := by
  simp [Lset]

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

/-! ### A gate that owns two disjoint edges is never below `f_G`

Only `NoFourCycle` is used here: no minimality, no `ReadsBack`, no triangle-freeness, and
no hypothesis that `C` computes the edge function.  Each wire the gate reads holds an
endpoint of the first owned edge and an endpoint of the second (`owned_operand_endpoint`
applied twice), and with the two edges DISJOINT those endpoints are distinct.  Feeding the
gate a pair taken one endpoint from each wire keeps it true, and the only way for every
such pair to be an edge of `G` is a 4-cycle on the four endpoints. -/

/-- At the input `1_st` the edge function is false unless `s` and `t` are adjacent. -/
lemma graph_pair_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {s t : Fin n}
    (h : ¬ G.Adj s t) : graphFun G ∅ (pairInput s t) = false := by
  rcases hv : graphFun G ∅ (pairInput s t) with _ | _
  · rfl
  · obtain ⟨a, b, hab, ha, hb⟩ := (graph_true G (pairInput s t)).mp hv
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl (G.ne_of_adj hab)
    · exact absurd hab h
    · exact absurd hab.symm h
    · exact absurd rfl (G.ne_of_adj hab)

/-- An AND gate each of whose operands holds `s` alone or holds `t` alone is true at the
pair input `1_st`. -/
lemma gateVal_of_Lset_pair {n : ℕ} {C : Circuit} (hC : Monotone2 C) {k : ℕ}
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.and) {s t : Fin n}
    (h : ∀ i ∈ (gateAt C k).inputs, i < n + k ∧ (s ∈ Lset n C i ∨ t ∈ Lset n C i)) :
    gateVal n C k (pairInput s t) = true := by
  rw [gateVal_and_iff hk hop]
  intro i hi
  obtain ⟨hilt, hmem⟩ := h i hi
  rw [earlier_getD C (le_of_lt hk) _ hilt]
  rcases hmem with hm | hm
  · refine wire_mono hC i (fun w hw => ?_) (mem_Lset.mp hm)
    simp only [pairInput, decide_eq_true_eq, or_self] at hw
    simp [pairInput, hw]
  · refine wire_mono hC i (fun w hw => ?_) (mem_Lset.mp hm)
    simp only [pairInput, decide_eq_true_eq, or_self] at hw
    simp [pairInput, hw]

/-- THE CONVERSE OF THE ROW'S NAMED LEMMA.  In a 4-cycle-free graph an AND gate of a
`Monotone2` circuit that owns two DISJOINT edges is true at some input where `f_G` is
false, so it is NEVER below `f_G`.  The `junk` hypothesis of `junkOwnsNoDisjointPair` is
therefore automatic, and the conclusion of that lemma contradicts it: the lemma says
exactly that no gate owns two disjoint edges. -/
theorem owns_disjoint_dirty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : Monotone2 C) (hnf : NoFourCycle G) {j : ℕ} {u v u' v' : Fin n}
    (huv : G.Adj u v) (huv' : G.Adj u' v') (ho : Owns n C j u v) (ho' : Owns n C j u' v')
    (hdis : ¬ (u = u' ∨ u = v' ∨ v = u' ∨ v = v')) :
    ∃ y : Fin n → Bool, gateVal n C j y = true ∧ graphFun G ∅ y = false := by
  classical
  have hk := ho.1
  have hop := ho.2.1
  have hlen : (gateAt C j).inputs.length ≤ 2 := by
    rw [gateAt_eq hk]
    exact (hC _ (List.getElem_mem hk)).2
  have hirr : ∀ w : Fin n, ¬ G.Adj w w := fun w h => (G.ne_of_adj h) rfl
  obtain ⟨hne1, hne2, hne3, hne4⟩ : u ≠ u' ∧ u ≠ v' ∧ v ≠ u' ∧ v ≠ v' :=
    ⟨fun h => hdis (Or.inl h), fun h => hdis (Or.inr (Or.inl h)),
      fun h => hdis (Or.inr (Or.inr (Or.inl h))),
      fun h => hdis (Or.inr (Or.inr (Or.inr h)))⟩
  have hAdj : ∀ s t : Fin n, (s = u ∨ s = v) → (t = u ∨ t = v) → s ≠ t → G.Adj s t := by
    intro s t hs ht hst
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact absurd rfl hst
    · exact huv
    · exact huv.symm
    · exact absurd rfl hst
  have hAdj' : ∀ s t : Fin n, (s = u' ∨ s = v') → (t = u' ∨ t = v') → s ≠ t →
      G.Adj s t := by
    intro s t hs ht hst
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact absurd rfl hst
    · exact huv'
    · exact huv'.symm
    · exact absurd rfl hst
  have hoff : ∀ s t : Fin n, (s = u ∨ s = v) → (t = u' ∨ t = v') → s ≠ t := by
    intro s t hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact hne1
    · exact hne2
    · exact hne3
    · exact hne4
  have mk : ∀ s t : Fin n, (∀ i ∈ (gateAt C j).inputs, i < n + j ∧
      (s ∈ Lset n C i ∨ t ∈ Lset n C i)) → ¬ G.Adj s t →
      ∃ y : Fin n → Bool, gateVal n C j y = true ∧ graphFun G ∅ y = false := by
    intro s t hall hadj
    exact ⟨pairInput s t, gateVal_of_Lset_pair hC hk hop hall, graph_pair_false G hadj⟩
  cases hL : (gateAt C j).inputs with
  | nil => exact mk u u (by rw [hL]; simp) (hirr u)
  | cons a as =>
    cases has : as with
    | nil =>
      obtain ⟨halt, p, _, hpa⟩ := owned_operand_endpoint hC ho (i := a) (by rw [hL]; simp)
      refine mk p p ?_ (hirr p)
      intro i hi
      rw [hL, has] at hi
      simp only [List.mem_singleton] at hi
      subst hi
      exact ⟨halt, Or.inl hpa⟩
    | cons b bs =>
      cases hbs : bs with
      | cons c cs =>
        exfalso
        rw [hL, has, hbs] at hlen
        simp at hlen
      | nil =>
        have hmemA : a ∈ (gateAt C j).inputs := by rw [hL]; simp
        have hmemB : b ∈ (gateAt C j).inputs := by rw [hL, has, hbs]; simp
        obtain ⟨halt, p, hp, hpa⟩ := owned_operand_endpoint hC ho hmemA
        obtain ⟨hblt, q, hq, hqb⟩ := owned_operand_endpoint hC ho hmemB
        obtain ⟨_, p2, hp2, hp2a⟩ := owned_operand_endpoint hC ho' hmemA
        obtain ⟨_, q2, hq2, hq2b⟩ := owned_operand_endpoint hC ho' hmemB
        have cover : ∀ s t : Fin n, s ∈ Lset n C a → t ∈ Lset n C b →
            ∀ i ∈ (gateAt C j).inputs, i < n + j ∧
              (s ∈ Lset n C i ∨ t ∈ Lset n C i) := by
          intro s t hs ht i hi
          rw [hL, has, hbs] at hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact ⟨halt, Or.inl hs⟩
          · exact ⟨hblt, Or.inr ht⟩
        by_cases hpq : p = q
        · subst hpq
          exact mk p p (cover p p hpa hqb) (hirr p)
        by_cases hpq2 : p2 = q2
        · subst hpq2
          exact mk p2 p2 (cover p2 p2 hp2a hq2b) (hirr p2)
        by_cases hx : G.Adj p q2
        · by_cases hy : G.Adj p2 q
          · exfalso
            have h1 : G.Adj p q := hAdj p q hp hq hpq
            have h4 : G.Adj p2 q2 := hAdj' p2 q2 hp2 hq2 hpq2
            have hpp2 : p ≠ p2 := hoff p p2 hp hp2
            have hqq2 : q ≠ q2 := hoff q q2 hq hq2
            have hsub : ({q, q2} : Finset (Fin n)) ⊆
                Finset.univ.filter fun w => G.Adj p w ∧ G.Adj p2 w := by
              intro w hw
              simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl
              · simp [h1, hy]
              · simp [hx, h4]
            have hcard := Finset.card_le_card hsub
            rw [Finset.card_pair hqq2] at hcard
            exact absurd (le_trans hcard (hnf p p2 hpp2)) (by omega)
          · exact mk p2 q (cover p2 q hp2a hqb) hy
        · exact mk p q2 (cover p q2 hpa hq2b) hx

/-! ### The configuration a gate owning two disjoint pairs is forced into

This is where any argument from `IsMinimalMonoCircuit` has to start, so it is recorded
exactly.  A gate owning two DISJOINT pairs reads only EARLIER GATE wires, never an input
wire, and every one of those gates is an OR gate of its cone whose vertex set contains an
endpoint of each pair.  An input wire is excluded for a sharp reason: the vertex set of an
input wire is that one vertex, while here it has to hold two. -/

/-- Each wire read by a gate owning two DISJOINT pairs is the wire of an earlier OR gate
inside its cone, and holds an endpoint of each of the two pairs. -/
theorem owns_disjoint_operands {n : ℕ} {C : Circuit} (hC : Monotone2 C) {j : ℕ}
    {u v u' v' : Fin n} (ho : Owns n C j u v) (ho' : Owns n C j u' v')
    (hdis : ¬ (u = u' ∨ u = v' ∨ v = u' ∨ v = v')) {i : ℕ}
    (hi : i ∈ (gateAt C j).inputs) :
    (∃ i0 : ℕ, i = n + i0 ∧ i0 < j ∧ InCone n C i0 j ∧
        (gateAt C i0).op = GateOp.or) ∧
      (∃ p : Fin n, (p = u ∨ p = v) ∧ p ∈ Lset n C i) ∧
      (∃ p : Fin n, (p = u' ∨ p = v') ∧ p ∈ Lset n C i) := by
  have hk := ho.1
  have hop := ho.2.1
  obtain ⟨hilt, p, hp, hpa⟩ := owned_operand_endpoint hC ho hi
  obtain ⟨_, p2, hp2, hp2a⟩ := owned_operand_endpoint hC ho' hi
  refine ⟨?_, ⟨p, hp, hpa⟩, ⟨p2, hp2, hp2a⟩⟩
  -- an input wire would hold ONE vertex, but it holds both `p` and `p2`, which differ
  have hpp2 : p ≠ p2 := by
    rcases hp with rfl | rfl <;> rcases hp2 with rfl | rfl
    · exact fun h => hdis (Or.inl h)
    · exact fun h => hdis (Or.inr (Or.inl h))
    · exact fun h => hdis (Or.inr (Or.inr (Or.inl h)))
    · exact fun h => hdis (Or.inr (Or.inr (Or.inr h)))
  have hin : n ≤ i := by
    by_contra hlow
    have hlt : i < n := Nat.lt_of_not_ge hlow
    have hone : ∀ w : Fin n, w ∈ Lset n C i → (⟨i, hlt⟩ : Fin n) = w := by
      intro w hw
      have h0 := mem_Lset.mp hw
      rw [show i = (⟨i, hlt⟩ : Fin n).val from rfl, wireVal_input C ⟨i, hlt⟩] at h0
      simpa only [pairInput, decide_eq_true_eq, or_self] using h0
    exact hpp2 (((hone p hpa).symm).trans (hone p2 hp2a))
  refine ⟨i - n, by omega, by omega, inCone_of_reads hk (by omega) ?_, ?_⟩
  · rw [show n + (i - n) = i by omega]; exact hi
  · -- the gate is true at `1_uv`, and no AND gate of the cone is
    have hbits := (gateVal_and_iff hk hop (pairInput u v)).mp ho.2.2.1
    have hval : gateVal n C (i - n) (pairInput u v) = true := by
      rw [gateVal_eq_wireVal, show n + (i - n) = i by omega,
        ← earlier_getD C (le_of_lt hk) (pairInput u v) hilt]
      exact hbits i hi
    have hmono : IsMonoGate (gateAt C (i - n)) := by
      rw [gateAt_eq (by omega : i - n < C.gates.length)]
      exact monoGate_of_mem hC (List.getElem_mem (by omega))
    rcases hmono with hand | hor
    · exfalso
      have hbad := ho.2.2.2 (i - n) (by omega)
        (inCone_of_reads hk (by omega) (by rw [show n + (i - n) = i by omega]; exact hi))
        hand
      rw [hbad] at hval
      exact absurd hval (by simp)
    · exact hor

/-! ### The row's named lemma IS the star profile, as an equivalence

`HasStarProfile` of `PEqualNP.EdgeOwnership` is the row's own conclusion.  Below, the body
of `junkOwnsNoDisjointPair` for a circuit and the star profile of that circuit are the same
statement, for any `Monotone2` circuit of a triangle-free, 4-cycle-free graph.  Neither
minimality nor `circuitFun n C = graphFun G ∅` is needed for the equivalence; they only
enter when the lemma is quantified over all least circuits. -/

/-- No AND gate of `C` owns two disjoint edges of `G`. -/
def NoDisjointOwned (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ (j : ℕ) (u v u' v' : Fin n), G.Adj u v → G.Adj u' v' → Owns n C j u v →
    Owns n C j u' v' → (u = u' ∨ u = v' ∨ v = u' ∨ v = v')

/-- Owning no two disjoint edges is the star profile, in a triangle-free graph. -/
theorem noDisjointOwned_iff_starProfile {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit)
    (htri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) :
    NoDisjointOwned n G C ↔ HasStarProfile n G C := by
  constructor
  · intro h j _ _
    rcases star_of_pairwise_meet htri (fun x y => G.Adj x y ∧ Owns n C j x y)
      (fun _ _ hx => hx.1) (fun _ _ hx => ⟨hx.1.symm, owns_comm hx.2⟩)
      (fun x y x' y' h1 h2 => h j x y x' y' h1.1 h2.1 h1.2 h2.2) with hnone | ⟨c, hc⟩
    · exact Or.inl fun x y hxy ho => hnone x y ⟨hxy, ho⟩
    · exact Or.inr ⟨c, fun x y hxy ho => hc x y ⟨hxy, ho⟩⟩
  · intro h j x y x' y' hxy hxy' ho ho'
    rcases h j ho.1 ho.2.1 with hnone | ⟨c, hc⟩
    · exact absurd ho (hnone x y hxy)
    · rcases hc x y hxy ho with h1 | h1 <;> rcases hc x' y' hxy' ho' with h2 | h2
      · exact Or.inl (h1.trans h2.symm)
      · exact Or.inr (Or.inl (h1.trans h2.symm))
      · exact Or.inr (Or.inr (Or.inl (h1.trans h2.symm)))
      · exact Or.inr (Or.inr (Or.inr (h1.trans h2.symm)))

/-- The body of `junkOwnsNoDisjointPair` for one circuit: a junk AND gate owning two
disjoint edges would be below `f_G`. -/
def JunkLemmaBody (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : Prop :=
  ∀ (j : ℕ) (u v u' v' : Fin n), G.Adj u v → G.Adj u' v' → Owns n C j u v →
    Owns n C j u' v' → ¬ (u = u' ∨ u = v' ∨ v = u' ∨ v = v') →
    ∀ y : Fin n → Bool, gateVal n C j y = true → graphFun G ∅ y = true

/-- The body of the lemma says no more and no less than that no gate owns two disjoint
edges: the hypothesis and the conclusion of the lemma cannot both hold. -/
theorem lemmaBody_iff_noDisjointOwned {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : Monotone2 C) (hnf : NoFourCycle G) :
    JunkLemmaBody n G C ↔ NoDisjointOwned n G C := by
  constructor
  · intro h j x y x' y' hxy hxy' ho ho'
    by_contra hdis
    obtain ⟨z, hz, hzF⟩ := owns_disjoint_dirty G C hC hnf hxy hxy' ho ho' hdis
    rw [h j x y x' y' hxy hxy' ho ho' hdis z hz] at hzF
    exact absurd hzF (by simp)
  · intro h j x y x' y' hxy hxy' ho ho' hdis
    exact absurd (h j x y x' y' hxy hxy' ho ho') hdis

/-- THE OBSTACLE, named: for a `Monotone2` circuit of a triangle-free, 4-cycle-free graph
the body of `junkOwnsNoDisjointPair` is EQUIVALENT to the star profile of that circuit.  So
the lemma is not a weaker stepping stone towards the row's conclusion; it is that
conclusion. -/
theorem lemmaBody_iff_starProfile {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : Monotone2 C)
    (htri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) (hnf : NoFourCycle G) :
    JunkLemmaBody n G C ↔ HasStarProfile n G C :=
  (lemmaBody_iff_noDisjointOwned G C hC hnf).trans
    (noDisjointOwned_iff_starProfile G C htri)

/-- The lemma the row is short of, verbatim. -/
def JunkOwnsNoDisjointPair : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → NoFourCycle G →
    IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
    ∀ (j : ℕ) (u v u' v' : Fin n), G.Adj u v → G.Adj u' v' →
      Owns n C j u v → Owns n C j u' v' →
      ¬ (u = u' ∨ u = v' ∨ v = u' ∨ v = v') →
      ∀ y : Fin n → Bool, gateVal n C j y = true → graphFun G ∅ y = true

/-- The star profile of every least monotone circuit of a triangle-free, 4-cycle-free
graph: the full conclusion of the row, for all graphs at once. -/
def LeastStarProfile : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → NoFourCycle G →
    IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ → HasStarProfile n G C

/-- THE MAIN RESULT of this file: the one lemma the star-profile row is short of is
EQUIVALENT to the star profile for all least monotone circuits.  Whatever proves it proves
the whole row, so no weaker statement is hiding inside it; and since the dirty direction
above needs no minimality, the force must come from `IsMinimalMonoCircuit`. -/
theorem junkLemma_iff_leastStarProfile : JunkOwnsNoDisjointPair ↔ LeastStarProfile := by
  constructor
  · intro h n G inst C htri hnf hmin hF
    exact (lemmaBody_iff_starProfile G C hmin.1 htri hnf).mp
      (fun j x y x' y' hxy hxy' ho ho' hdis => h n G C htri hnf hmin hF j x y x' y'
        hxy hxy' ho ho' hdis)
  · intro h n G inst C htri hnf hmin hF
    exact (lemmaBody_iff_starProfile G C hmin.1 htri hnf).mpr
      (h n G C htri hnf hmin hF)

/-! ### The lemma fails ONE GATE above the minimum: there is no slack

`tightG` is the tree with edges `01, 02, 03, 14`: triangle-free and 4-cycle-free.  `tightC`
is a `Monotone2` circuit of SIX gates computing its edge function whose gate `4` is an AND
gate OWNING the two disjoint edges `02` and `14`; by `owns_disjoint_dirty` that gate is not
below `f_G` (it is true at the input `1_24`, where `f_G` is false), so the body of the row's
lemma is FALSE for `tightC`, and so is the star profile.

That is as it must be, since `tightC` is not least - but only just.  Exact synthesis over the
full `Monotone2` model (SAT, cadical) gives FIVE as the least size for this graph, with the
witness `(x0 and (x2 or x3)) or (x1 and (x0 or x4))`, and six is the least size at which a
circuit for `f_G` with a gate owning two disjoint edges exists.  The same one-gate gap was
measured for 6 of the 11 six-vertex graphs and for 2 of the 4 five-vertex ones.  The least
size is a synthesis result, not a kernel-checked one; the circuit below, and the failure of
the star at its gate `4`, are kernel-checked.  So whatever argument proves the lemma has to
be exact to a single gate: no counting with room to spare can reach it, which is the obstacle
this file is reporting. -/

/-- The tree `1 - 0 - 2`, `0 - 3`, `1 - 4` on `Fin 5`. -/
def tightG : SimpleGraph (Fin 5) := edgeGraph 5 [(0, 1), (0, 2), (0, 3), (1, 4)]

instance tightG_dec : DecidableRel tightG.Adj :=
  inferInstanceAs (DecidableRel (edgeGraph 5 [(0, 1), (0, 2), (0, 3), (1, 4)]).Adj)

/-- Six gates for the edge function of `tightG`, one more than the least size, whose gate `4`
owns two disjoint edges.  It is `(x0 or x1) and (x0 or x4) and (x1 or x2 or x3)`, where the
middle and last factors are the owning gate. -/
def tightC : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [1, 7]⟩,
    ⟨GateOp.and, [6, 8]⟩, ⟨GateOp.and, [5, 9]⟩], 10⟩

theorem tightG_triangleFree :
    ∀ a b c : Fin 5, tightG.Adj a b → tightG.Adj b c → ¬ tightG.Adj c a := by decide

theorem tightG_noFourCycle : NoFourCycle tightG := by decide

theorem tightC_mono : Monotone2 tightC := by
  intro g hg
  fin_cases hg <;> exact ⟨by simp, by simp⟩

theorem tightC_computes :
    ∀ x : Fin 5 → Bool, circuitFun 5 tightC x = graphFun tightG ∅ x := by decide

/-- Gate `4` of `tightC` owns the two DISJOINT edges `02` and `14`. -/
theorem tightC_ownsDisjoint :
    tightG.Adj 0 2 ∧ tightG.Adj 1 4 ∧ Owns 5 tightC 4 0 2 ∧ Owns 5 tightC 4 1 4 ∧
      ¬ ((0 : Fin 5) = 1 ∨ (0 : Fin 5) = 4 ∨ (2 : Fin 5) = 1 ∨ (2 : Fin 5) = 4) := by
  decide

/-- Gate `4` is true at `1_24`, where `f_G` is false: it is junk, as `owns_disjoint_dirty`
says it must be. -/
theorem tightC_dirty :
    gateVal 5 tightC 4 (pairInput 2 4) = true ∧ graphFun tightG ∅ (pairInput 2 4) = false := by
  decide

/-- So `tightC` has no star profile. -/
theorem tightC_notStar : ¬ HasStarProfile 5 tightG tightC := by decide

/-- And the body of the row's lemma is false for it, one gate above the least size. -/
theorem tightC_lemmaBody_false : ¬ JunkLemmaBody 5 tightG tightC := fun h =>
  tightC_notStar ((lemmaBody_iff_starProfile tightG tightC tightC_mono tightG_triangleFree
    tightG_noFourCycle).mp h)

end PEqualNP.Outside.L_meta_zzjunk
