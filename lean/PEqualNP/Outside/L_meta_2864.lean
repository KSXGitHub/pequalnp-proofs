import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2864

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem getD_snoc (w : List Bool) (v : Bool) (j : ℕ) :
    (w ++ [v]).getD j false =
      if j < w.length then w.getD j false else if j = w.length then v else false := by
  by_cases h1 : j < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1, h1]
  · by_cases h2 : j = w.length
    · subst h2; simp [List.getD_eq_getElem?_getD]
    · have : w.length + 1 ≤ j ∨ j = w.length := by omega
      rcases this with h | h
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : w.length ≤ j)]
        rw [List.getElem?_eq_none (by simp; omega)]; simp [h1, h2]
      · exact absurd h h2

theorem foldl_mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    ∀ w w' : List Bool, w.length = w'.length →
      (∀ j, w.getD j false = true → w'.getD j false = true) →
      ∀ j, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD j false = true →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD j false = true := by
  induction gs with
  | nil => intro w w' _ h j; exact h j
  | cons g gs ih =>
    intro w w' hl hm j
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) _ _ (by simp [hl])
    intro k hk
    rw [getD_snoc] at hk ⊢
    rw [← hl]
    split_ifs at hk ⊢ with h1 h2
    · exact hm k hk
    · have hop := hg g (List.mem_cons_self)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with h | h
      · simp only [h, GateOp.eval, List.all_map, Function.comp_apply, id, List.all_eq_true] at hk ⊢
        exact fun a ha => hm a (hk a ha)
      · simp only [h, GateOp.eval, List.any_map, Function.comp_apply, id, List.any_eq_true] at hk ⊢
        obtain ⟨a, ha, he⟩ := hk
        exact ⟨a, ha, hm a he⟩

def W (C : Circuit) (n k : ℕ) (x y : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x ++ List.ofFn y)).getD k false

theorem input_mono {n : ℕ} {x x' y y' : Fin n → Bool}
    (hx : ∀ i, x i = true → x' i = true) (hy : ∀ i, y i = true → y' i = true) :
    ∀ j, (List.ofFn x ++ List.ofFn y).getD j false = true →
      (List.ofFn x' ++ List.ofFn y').getD j false = true := by
  intro j hj
  simp only [List.getD_eq_getElem?_getD] at hj ⊢
  by_cases h : j < n
  · rw [List.getElem?_append_left (by simpa using h)] at hj ⊢
    simp only [List.getElem?_ofFn, h, dite_eq_left] at hj ⊢
    exact hx _ hj
  · rw [List.getElem?_append_right (by simpa using h)] at hj ⊢
    simp only [List.getElem?_ofFn, List.length_ofFn] at hj ⊢
    by_cases h2 : j - n < n
    · simp only [h2, dite_eq_left] at hj ⊢
      exact hy _ hj
    · simp [h2] at hj

theorem W_mono {C : Circuit} (hC : PEqualNP.MetaComplexity.Monotone2 C) (n k : ℕ)
    {x x' y y' : Fin n → Bool}
    (hx : ∀ i, x i = true → x' i = true) (hy : ∀ i, y i = true → y' i = true) :
    W C n k x y = true → W C n k x' y' = true := by
  intro h
  unfold W Circuit.wires at h ⊢
  exact foldl_mono C.gates (fun g hg => (hC g hg).1) _ _ (by simp) (input_mono hx hy) k h

section comb

variable {n : ℕ} (F G : (Fin n → Bool) → (Fin n → Bool) → Bool)

def Mono (F : (Fin n → Bool) → (Fin n → Bool) → Bool) : Prop :=
  ∀ x x' y y' : Fin n → Bool, (∀ i, x i = true → x' i = true) → (∀ i, y i = true → y' i = true) →
    F x y = true → F x' y' = true

theorem indepL {F : (Fin n → Bool) → (Fin n → Bool) → Bool} (hF : Mono F)
    (h : ∀ p, F p (fun _ => false) = F p (fun _ => true)) : ∀ p l, F p l = F p (fun _ => false) := by
  intro p l
  rw [Bool.eq_iff_iff]
  constructor
  · intro hl
    have h1 : F p (fun _ => true) = true := hF p p l _ (fun _ => id) (fun _ _ => rfl) hl
    rw [← h] at h1; exact h1
  · intro h0
    exact hF p p _ l (fun _ => id) (fun i hi => by simp at hi) h0

theorem indepP {F : (Fin n → Bool) → (Fin n → Bool) → Bool} (hF : Mono F)
    (h : ∀ l, F (fun _ => false) l = F (fun _ => true) l) : ∀ p l, F p l = F (fun _ => false) l := by
  intro p l
  rw [Bool.eq_iff_iff]
  constructor
  · intro hl
    have h1 : F (fun _ => true) l = true := hF p _ l l (fun _ _ => rfl) (fun _ => id) hl
    rw [← h] at h1; exact h1
  · intro h0
    exact hF _ p l l (fun i hi => by simp at hi) (fun _ => id) h0

theorem const_and {F G : (Fin n → Bool) → (Fin n → Bool) → Bool} (hF : Mono F)
    (h1 : ∀ p, F p (fun _ => false) = F p (fun _ => true))
    (h2 : ∀ l, F (fun _ => false) l = F (fun _ => true) l) :
    (∀ p l, (F p l && G p l) = F p l) ∨ (∀ p l, (F p l && G p l) = G p l) := by
  have hc : ∀ p l, F p l = F (fun _ => false) (fun _ => false) := by
    intro p l
    rw [indepL hF h1 p l, indepP hF h2 p (fun _ => false)]
  cases hv : F (fun _ => false) (fun _ => false)
  · left; intro p l; have := hc p l; rw [hv] at this; simp [this]
  · right; intro p l; have := hc p l; rw [hv] at this; simp [this]

theorem comb {F G : (Fin n → Bool) → (Fin n → Bool) → Bool} (hF : Mono F) (hG : Mono G)
    (hA : ¬((∃ p, F p (fun _ => false) ≠ F p (fun _ => true)) ∧
      (∃ p, G p (fun _ => false) ≠ G p (fun _ => true))))
    (hB : ¬((∃ l, F (fun _ => false) l ≠ F (fun _ => true) l) ∧
      (∃ l, G (fun _ => false) l ≠ G (fun _ => true) l))) :
    ((∀ p l, (F p l && G p l) = F p l) ∨ (∀ p l, (F p l && G p l) = G p l)) ∨
    ∃ (f g : (Fin n → Bool) → Bool), ∀ p l, (F p l && G p l) = (f p && g l) := by
  have nA : ∀ {H : (Fin n → Bool) → (Fin n → Bool) → Bool}, Mono H →
      ¬(∃ p, H p (fun _ => false) ≠ H p (fun _ => true)) → ∀ p l, H p l = H p (fun _ => false) := by
    intro H hH h
    push Not at h
    exact indepL hH h
  have nB : ∀ {H : (Fin n → Bool) → (Fin n → Bool) → Bool}, Mono H →
      ¬(∃ l, H (fun _ => false) l ≠ H (fun _ => true) l) → ∀ p l, H p l = H (fun _ => false) l := by
    intro H hH h
    push Not at h
    exact indepP hH h
  have cst : ∀ {H K : (Fin n → Bool) → (Fin n → Bool) → Bool}, Mono H →
      ¬(∃ p, H p (fun _ => false) ≠ H p (fun _ => true)) →
      ¬(∃ l, H (fun _ => false) l ≠ H (fun _ => true) l) →
      (∀ p l, (H p l && K p l) = H p l) ∨ (∀ p l, (H p l && K p l) = K p l) := by
    intro H K hH h1 h2
    push Not at h1 h2
    exact const_and hH h1 h2
  have cstG : ¬(∃ p, G p (fun _ => false) ≠ G p (fun _ => true)) →
      ¬(∃ l, G (fun _ => false) l ≠ G (fun _ => true) l) →
      ((∀ p l, (F p l && G p l) = F p l) ∨ (∀ p l, (F p l && G p l) = G p l)) := by
    intro h1 h2
    rcases cst (K := F) hG h1 h2 with h | h
    · right; intro p l; rw [Bool.and_comm]; exact h p l
    · left; intro p l; rw [Bool.and_comm]; exact h p l
  by_cases aF : ∃ p, F p (fun _ => false) ≠ F p (fun _ => true)
  · by_cases aG : ∃ p, G p (fun _ => false) ≠ G p (fun _ => true)
    · exact absurd ⟨aF, aG⟩ hA
    · by_cases bG : ∃ l, G (fun _ => false) l ≠ G (fun _ => true) l
      · have bF : ¬∃ l, F (fun _ => false) l ≠ F (fun _ => true) l := fun h => hB ⟨h, bG⟩
        right
        refine ⟨fun p => G p (fun _ => false), fun l => F (fun _ => false) l, ?_⟩
        intro p l
        rw [nB hF bF p l, nA hG aG p l, Bool.and_comm]
      · exact Or.inl (cstG aG bG)
  · by_cases bF : ∃ l, F (fun _ => false) l ≠ F (fun _ => true) l
    · by_cases bG : ∃ l, G (fun _ => false) l ≠ G (fun _ => true) l
      · exact absurd ⟨bF, bG⟩ hB
      · by_cases aG : ∃ p, G p (fun _ => false) ≠ G p (fun _ => true)
        · right
          refine ⟨fun p => F p (fun _ => false), fun l => G (fun _ => false) l, ?_⟩
          intro p l
          rw [nA hF aF p l, nB hG bG p l]
        · exact Or.inl (cstG aG bG)
    · exact Or.inl (cst hF aF bF)

end comb

end PEqualNP.Outside.L_meta_2864

theorem PEqualNP.Outside.L_meta_2864 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (0 : ℕ) < x1 →     (∀ (x7 x8 : Fin x2), x7 ≠ x8 → ∃! x10 : Fin x2, x3 x7 x10 ∧ x3 x8 x10) →       PEqualNP.MetaComplexity.Monotone2 x5 →         (∀ (x9 : Fin (x2 + x2) → Bool), Fintype.card { x10 : Fin x2 // x9 (Fin.natAdd x2 x10) = Bool.true } ≤ x1 → (¬∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧ x9 (Fin.castAdd x2 x11) = Bool.true ∧ x9 (Fin.natAdd x2 x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x9 = Bool.false) →           ∀ (x10 x11 : ℕ),             ¬((∀ x12 ∈ [x10, x11], ∃ (x14 : Fin x2 → Bool), (x5.wires (List.ofFn x14 ++ List.replicate x2 Bool.false)).getD x12 Bool.false ≠ (x5.wires (List.ofFn x14 ++ List.replicate x2 Bool.true)).getD x12 Bool.false) ∨ ∀ x12 ∈ [x10, x11], ∃ (x14 : Fin x2 → Bool), (x5.wires (List.replicate x2 Bool.false ++ List.ofFn x14)).getD x12 Bool.false ≠ (x5.wires (List.replicate x2 Bool.true ++ List.ofFn x14)).getD x12 Bool.false) →               have x13 : ℕ → (Fin x2 → Bool) → (Fin x2 → Bool) → Bool := fun (x13 : ℕ) (x14 x15 : Fin x2 → Bool) => (x5.wires (List.ofFn x14 ++ List.ofFn x15)).getD x13 Bool.false;               have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);               (∃ x15 ∈ [x10, x11], ∀ (x16 x17 : Fin x2 → Bool), (x13 x10 x16 x17 && x13 x11 x16 x17) = x13 x15 x16 x17) ∨ ∃ (x15 : (Fin x2 → Bool) → Bool) (x16 : (Fin x2 → Bool) → Bool), (∀ (x17 x18 : Fin x2 → Bool), (x13 x10 x17 x18 && x13 x11 x17 x18) = (x15 x17 && x16 x18)) ∧ ((∀ (x17 x18 : Fin x2), (x15 (x14 x17) && x16 (x14 x18)) = Bool.true → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x20 : Fin (x2 + x2)) => Decidable.decide (x20 = Fin.castAdd x2 x17 ∨ x20 = Fin.natAdd x2 x18)) = Bool.true) → ∀ (x18 x19 x20 x21 : Fin x2), (x15 (x14 x18) && x16 (x14 x20)) = Bool.true → (x15 (x14 x19) && x16 (x14 x21)) = Bool.true → x18 = x19 ∨ x20 = x21) := by
  intro x1 x2 x3 x4 C hx1 huniq hmono hsound a b hyp
  dsimp only
  have hM : ∀ k, PEqualNP.Outside.L_meta_2864.Mono (PEqualNP.Outside.L_meta_2864.W C x2 k) :=
    fun k x x' y y' hx hy => PEqualNP.Outside.L_meta_2864.W_mono hmono x2 k hx hy
  have hyp1 := fun h => hyp (Or.inl h)
  have hyp2 := fun h => hyp (Or.inr h)
  have hA : ¬((∃ p, PEqualNP.Outside.L_meta_2864.W C x2 a p (fun _ => false) ≠
        PEqualNP.Outside.L_meta_2864.W C x2 a p (fun _ => true)) ∧
      (∃ p, PEqualNP.Outside.L_meta_2864.W C x2 b p (fun _ => false) ≠
        PEqualNP.Outside.L_meta_2864.W C x2 b p (fun _ => true))) := by
    rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
    apply hyp1
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact ⟨p, by simpa [PEqualNP.Outside.L_meta_2864.W, List.ofFn_const] using hp⟩
    · exact ⟨q, by simpa [PEqualNP.Outside.L_meta_2864.W, List.ofFn_const] using hq⟩
  have hB : ¬((∃ l, PEqualNP.Outside.L_meta_2864.W C x2 a (fun _ => false) l ≠
        PEqualNP.Outside.L_meta_2864.W C x2 a (fun _ => true) l) ∧
      (∃ l, PEqualNP.Outside.L_meta_2864.W C x2 b (fun _ => false) l ≠
        PEqualNP.Outside.L_meta_2864.W C x2 b (fun _ => true) l)) := by
    rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
    apply hyp2
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact ⟨p, by simpa [PEqualNP.Outside.L_meta_2864.W, List.ofFn_const] using hp⟩
    · exact ⟨q, by simpa [PEqualNP.Outside.L_meta_2864.W, List.ofFn_const] using hq⟩
  rcases PEqualNP.Outside.L_meta_2864.comb (hM a) (hM b) hA hB with (h | h) | ⟨f, g, hfg⟩
  · left
    exact ⟨a, by simp, fun x y => h x y⟩
  · left
    exact ⟨b, by simp, fun x y => h x y⟩
  · right
    refine ⟨f, g, fun x y => hfg x y, ?_⟩
    intro hacc x18 x19 x20 x21 h1 h2
    have key : ∀ u v : Fin x2, (f (fun y => decide (y = u)) && g (fun y => decide (y = v))) = true →
        x3 u v := by
      intro u v huv
      have hc := hacc u v huv
      by_contra hn
      have hcard : Fintype.card { l : Fin x2 //
          (fun x20 : Fin (x2 + x2) => decide (x20 = Fin.castAdd x2 u ∨ x20 = Fin.natAdd x2 v))
            (Fin.natAdd x2 l) = Bool.true } ≤ x1 := by
        have : Fintype.card { l : Fin x2 //
          (fun x20 : Fin (x2 + x2) => decide (x20 = Fin.castAdd x2 u ∨ x20 = Fin.natAdd x2 v))
            (Fin.natAdd x2 l) = Bool.true } ≤ 1 := by
          rw [Fintype.card_le_one_iff]
          rintro ⟨l, hl⟩ ⟨l', hl'⟩
          simp only [decide_eq_true_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] at hl hl'
          have e : l = l' := Fin.ext (by have := l.2; have := l'.2; omega)
          subst e
          rfl
        omega
      have hnot : ¬∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧
          (fun x20 : Fin (x2 + x2) => decide (x20 = Fin.castAdd x2 u ∨ x20 = Fin.natAdd x2 v))
            (Fin.castAdd x2 x11) = Bool.true ∧
          (fun x20 : Fin (x2 + x2) => decide (x20 = Fin.castAdd x2 u ∨ x20 = Fin.natAdd x2 v))
            (Fin.natAdd x2 x12) = Bool.true := by
        rintro ⟨p, l, hpl, e1, e2⟩
        simp only [decide_eq_true_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] at e1 e2
        have hp : p = u := by
          apply Fin.ext
          have := p.2
          omega
        have hl : l = v := by
          apply Fin.ext
          have := l.2
          omega
        subst hp; subst hl
        exact hn hpl
      have := hsound (fun x20 : Fin (x2 + x2) => decide (x20 = Fin.castAdd x2 u ∨ x20 = Fin.natAdd x2 v)) hcard hnot
      rw [this] at hc
      exact absurd hc (by simp)
    by_contra hne
    push Not at hne
    obtain ⟨hne1, hne2⟩ := hne
    simp only [Bool.and_eq_true] at h1 h2
    have k1 := key x18 x20 (by simp [h1.1, h1.2])
    have k2 := key x19 x21 (by simp [h2.1, h2.2])
    have k3 := key x18 x21 (by simp [h1.1, h2.2])
    have k4 := key x19 x20 (by simp [h2.1, h1.2])
    obtain ⟨l, _, hu⟩ := huniq x18 x19 hne1
    exact hne2 ((hu x20 ⟨k1, k4⟩).trans (hu x21 ⟨k3, k2⟩).symm)
