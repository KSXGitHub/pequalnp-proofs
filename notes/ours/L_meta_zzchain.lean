import PEqualNP.Defs
import PEqualNP.Outside.L_meta_8305
import PEqualNP.Outside.R_meta_2658_412
import PEqualNP.Outside.L_meta_1602

/-!
SCRATCH / AUDIT FILE (not for submission: it imports Outside lemmas).

How big is `repairMany`?  This file kernel-checks the answer: assuming `repairMany` ALONE
(everything else in the chain is merged and complete) one gets, for EVERY C4-free graph
and EVERY Monotone2 circuit computing its edge function, the lower bound

    C.size + 1 ≥ |E(G)| + (vertex cover number of G).

So `repairMany` is not a stepping stone towards the desk's lower bound: it is equivalent to
the universally quantified version of that lower bound.  For the PG(2,4) incidence graph of
`R_meta_4328_874` (105 edges, cover 21) it gives size ≥ 125, which is exactly the bound
that decomposition is assembling graph-specifically through `single` and `pair`.

Chain: `L_meta_8305` (= repairFew, merged) and `repairMany` feed `R_meta_2658_412` (merged),
whose junk-free normal form feeds `L_meta_1602.pairCleanBound` (merged).
-/

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.NotPremium

/-- From `repairMany` alone: the |E| + tau - 1 lower bound for ALL Monotone2 circuits over
ALL C4-free graphs. -/
theorem universal_lower_bound_of_repairMany
    (repairMany : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → Monotone2 C → circuitFun n C = graphFun G ∅ → (junk G C).Nonempty →
      (∀ j ∈ junk G C, ∃ a b u v, G.Adj a b ∧ G.Adj u v ∧ pairInput a b ≠ pairInput u v ∧
        circuitFun n {C with gates := replaceByConst C.gates j false} (pairInput a b) = false ∧
        circuitFun n {C with gates := replaceByConst C.gates j false} (pairInput u v) = false) →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
        (junk G D).card < (junk G C).card) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], NoFourCycle G →
      (∃ a b : Fin n, G.Adj a b) → ∀ C : Circuit, Monotone2 C →
      circuitFun n C = graphFun G ∅ →
      ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
        G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  intro n G inst hnf hedge C hC hF
  -- the two spellings of C4-freeness used downstream
  have hcycle4 : ∀ p q r s : Fin n, p ≠ r → q ≠ s →
      ¬ (G.Adj p q ∧ G.Adj q r ∧ G.Adj r s ∧ G.Adj s p) := by
    intro p q r s hpr hqs ⟨h1, h2, h3, h4⟩
    have hmem : ({q, s} : Finset (Fin n)) ⊆
        Finset.univ.filter fun w => G.Adj p w ∧ G.Adj r w := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · simp [h1, h2.symm]
      · simp [h4.symm, h3]
    have hcard := Finset.card_le_card hmem
    rw [Finset.card_pair hqs] at hcard
    exact absurd (le_trans hcard (hnf p r hpr)) (by omega)
  have hlong : ∀ x5 x6 x7 x8 : Fin n, x5 ≠ x6 → x5 ≠ x7 → x5 ≠ x8 → x6 ≠ x7 → x6 ≠ x8 →
      x7 ≠ x8 → G.Adj x5 x6 → G.Adj x6 x7 → G.Adj x7 x8 → ¬ G.Adj x8 x5 := by
    intro a b c d _ hac _ hbc hbd _ hab hbc' hcd had
    exact hcycle4 a b c d hac hbd ⟨hab, hbc', hcd, had⟩
  have hiff : ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    intro x
    have h : circuitFun n C x = graphFun G ∅ x := by rw [hF]
    change C.eval (List.ofFn x) = graphFun G ∅ x at h
    rw [h]
    simp [graphFun]
  -- the junk-free normal form, from repairFew (merged) and repairMany
  obtain ⟨D, hD, hDiff, hDsize, hDclean⟩ :=
    PEqualNP.Outside.R_meta_2658_412
      (fun m H i E j => @PEqualNP.Outside.L_meta_8305 m H i E j) repairMany
      n G C hedge hlong hC hiff
  have hDF : circuitFun n D = graphFun G ∅ := by
    funext x
    have h := hDiff x
    change (circuitFun n D x = true) ↔ _ at h
    refine Bool.eq_iff_iff.mpr (h.trans ?_)
    simp [graphFun]
  -- feed the clean lower bound
  have hcleanPairs : ∀ k : ℕ, k < D.gates.length →
      (gateAt D k).op = GateOp.and → ∀ e w : Fin n, ¬ G.Adj e w →
      gateVal n D k (pairInput e w) = false := by
    intro k hk hop e w hew
    rcases hval : gateVal n D k (pairInput e w) with _ | _
    · rfl
    · exfalso
      have hsome : D.gates[k]? = some D.gates[k] := List.getElem?_eq_getElem hk
      have hopg : (D.gates[k]).op = GateOp.and := by
        rwa [show gateAt D k = D.gates[k] by
          simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]] at hop
      obtain ⟨p, q, hpq, hp, hq⟩ := hDclean k D.gates[k] hsome hopg (pairInput e w) hval
      simp only [pairInput, decide_eq_true_eq] at hp hq
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
      · exact absurd rfl (G.ne_of_adj hpq)
      · exact hew hpq
      · exact hew hpq.symm
      · exact absurd rfl (G.ne_of_adj hpq)
  obtain ⟨T, hTcover, hTbound⟩ :=
    PEqualNP.Outside.L_meta_1602
      (fun m H i h4 gates out hmono heval hcl =>
        PEqualNP.Outside.L_meta_1602.pairCleanBound m H h4 gates out hmono heval
          (fun i' x _ hop hv => hcl i' x hop hv))
      n G hcycle4 D hD hDF hcleanPairs
  exact ⟨T, hTcover, le_trans hTbound (by omega)⟩
