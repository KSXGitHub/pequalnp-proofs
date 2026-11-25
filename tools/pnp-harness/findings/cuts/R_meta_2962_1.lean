import Mathlib
import PEqualNP.Defs

-- A cut of the core-cover bound into its two independent halves.
--
-- Write D for the edges accepted by some maximal core,
-- D = (maximalCores G C).biUnion (gammaE G C), and U for the gates in the cones of
-- the maximal cores, U = (maximalCores G C).biUnion (coneSet n C).
--
-- starCentresCoverCoreEdges is the graph half. On a 4-cycle-free bipartite G the
-- edges a maximal core accepts form a biclique, and a 4-cycle-free biclique is a
-- STAR: one vertex of the core meets every edge the core accepts. Adjoining one
-- such centre per maximal core to a minimum cover of G - D gives a vertex cover of
-- G, because an edge of G is either in D, and then met by its core's centre, or
-- survives in G - D, and then met by T'. Minimality of T turns that cover into
-- tau(G) <= mc + tau(G - D).
--
-- coneGatesPayForCoreEdges is the circuit half, and is the one hard fact here: a
-- maximal core accepting m edges needs m gates in its cone (an OR tree over the m
-- leaves of its star, plus the core itself: the m + k - 1 count at k = 1), and
-- 4-cycle-freeness stops two maximal cores from sharing those gates, since a gate
-- feeding two distinct star centres with two or more leaves would give the two
-- centres two common neighbours. Summing over the maximal cores gives |D| <= |U|.
-- This is exactly the open point of the sketch (cores that share gates).
--
-- The posted inequality is then the sum of the two, by associativity.
theorem PEqualNP.Outside.R_meta_2962_1
    (starCentresCoverCoreEdges : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → PEqualNP.MetaComplexity.NestedCover.IsMinCover G T → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → T.card ≤ (PEqualNP.Core.maximalCores G C).card + T'.card)
    (coneGatesPayForCoreEdges : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card ≤ ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → PEqualNP.MetaComplexity.NestedCover.IsMinCover G T → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤ ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card + (PEqualNP.Core.maximalCores G C).card + T'.card := by
  intro n G inst C s T T' hcol hc4 hao hfun hfix hT hT'
  exact le_trans
    (Nat.add_le_add
      (coneGatesPayForCoreEdges n G C s hcol hc4 hao hfun hfix)
      (starCentresCoverCoreEdges n G C s T T' hcol hc4 hao hfun hfix hT hT'))
    (le_of_eq (Nat.add_assoc _ _ _).symm)
