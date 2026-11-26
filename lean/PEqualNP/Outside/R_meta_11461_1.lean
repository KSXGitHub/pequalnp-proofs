import Mathlib
import PEqualNP.Defs

-- A reduction of the double re-read step to ONE local condition on the output gate.
--
-- WHAT THE LAST CLAUSE OF THE STEP SAYS. A labelling x4 of the wires by 0, 1, 2 with
-- x4 (14 + j) at most x4 a + x4 b at an AND gate and at most the min of x4 a and x4 b at
-- an OR gate is a min-plus (tropical) evaluation from above: the greatest such labelling
-- gives each wire the least, over the proof trees of that wire (one branch at an OR, both
-- at an AND), of the total weight of the leaves, where the weight of an input is its own
-- label. With x4 0 = 0 and x4 7 at most 1 and every other input free (so 2), the demand
-- 2 at most x4 output says: every proof tree of the output either uses an input other
-- than point 0 and line 0, or reads line 0 twice. Since the circuit must accept the
-- incident pair (point 0, line 0), whose only true inputs are the wires 0 and 7, it has a
-- proof tree with all leaves in those two wires, and that tree is forced to read one of
-- them twice. Hence the name: a double re-read.
--
-- WHY THE OUTPUT HAS TO BE AN AND GATE. The min rule at an OR gate caps the gate by each
-- operand, so an OR-topped circuit reaches 2 only if every leaf of its OR tree does; the
-- cost-27 star covers (the seven line stars and the seven point stars, which an exhaustive
-- search elsewhere shows to be the only covers of cost 27) are OR trees over terms of the
-- form AND(one input wire, an OR chain over the other side), and such a term is capped by
-- x4 0 + x4 7, at most 1. So no cost-27 cover satisfies the clause, and any witness must
-- top out at an AND whose two operands each already carry label 1.
--
-- THE HYPOTHESIS. That observation is turned around here into the only unproved input:
-- a circuit of at most 27 gates in the model of the step, accepting every incidence and
-- rejecting the seven shifts of each of the seven maximal rejected masks, whose output
-- wire is an AND gate both of whose operand wires read FALSE on the one-point input (only
-- the wire 0 true) and FALSE on the one-line input (only the wire 7 true). Nothing about
-- labellings survives in it: the extra demand is two circuit evaluations, decidable on
-- any candidate and cheap to add to a search. It is the honest shape of the condition,
-- not a restatement of it: it speaks only of the output gate and of two inputs, whereas
-- the clause quantifies over all labellings and all gates, and it is consistent (the
-- circuit must accept the pair (point 0, line 0), so each operand is true on the two-hot
-- input and false on each half of it, which is exactly a wire that needs both).
--
-- TWO REMARKS ON ITS STRENGTH. Every gate of the model is an AND or an OR, so a circuit of
-- the model is monotone and the one-hot input is the SMALLEST input on which the wire 0
-- reads true; asking an operand to read false there is therefore the weakest demand of its
-- kind, weaker than asking it on any other input carrying the wire 0. And the hypothesis
-- is sufficient without being necessary: the AND at the output could also be paid for by
-- an operand of label 2 beside one of label 0, in which case the double read sits lower
-- down and recurs. Pinning it at the output is the localisation this reduction buys, and
-- the hand analysis above says an output AND is unavoidable in any case.
--
-- WHAT IS PROVED HERE. That the hypothesis gives the clause, for both values of the
-- Boolean, with no further assumption. The labelling is built explicitly: label the
-- output wire 2, label every other wire 1 if it reads false on the chosen one-hot input
-- and 0 if it reads true. The distinguished input reads true, so it gets 0; the other one
-- gets 0 or 1; the output gets 2; at the output gate the two operands read false, so they
-- carry 1 each and 1 + 1 = 2 pays for the AND; at any other gate the label is 0 unless
-- the gate reads false, and a gate that reads false is an AND with a false operand (label
-- at least 1, so the sum is at least 1) or an OR with both operands false (both labels at
-- least 1, so the min is at least 1). The set of wires that read false on a one-hot input
-- is, in the min-plus reading above, exactly the set of wires of label at least 1, which
-- is why one evaluation of the circuit replaces the whole labelling.
--
-- The ingredients about the wire fold (a fold result extends its start, a gate wire holds
-- the operation applied to the operand wires of the SAME final list, reading a labelling
-- list back) are proved inline, since only this one theorem may be declared.

theorem PEqualNP.Outside.R_meta_11461_1
    (topAndOnTwoFalseOperands :
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (j u v : ℕ)
          (g : PEqualNP.CircuitLowerBounds.Gate),
        C.size ≤ (27 : ℕ) ∧     (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), C.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧       (∀ (x2 x3 : Fin (7 : ℕ)), x2 = x3 ∨ x2 = x3 + (1 : Fin (7 : ℕ)) ∨ x2 = x3 + (3 : Fin (7 : ℕ)) → C.eval (List.ofFn fun (x5 : Fin (14 : ℕ)) => Decidable.decide (x5 = Fin.castAdd (7 : ℕ) x2 ∨ x5 = Fin.natAdd (7 : ℕ) x3)) = Bool.true) ∧         (∀ x2 ∈ [(127 : ℕ), (244 : ℕ), (480 : ℕ), (720 : ℕ), (1188 : ℕ), (3008 : ℕ), (16256 : ℕ)], ∀ (x4 : Fin (7 : ℕ)), C.eval (List.ofFn fun (x5 : Fin ((7 : ℕ) + (7 : ℕ))) => Fin.addCases (fun (x6 : Fin (7 : ℕ)) => x2.testBit ↑(x6 + x4)) (fun (x6 : Fin (7 : ℕ)) => x2.testBit ((7 : ℕ) + ↑(x6 + x4))) x5) = Bool.false) ∧
        C.output = (14 : ℕ) + j ∧ C.gates[j]? = Option.some g ∧
        g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ g.inputs = [u, v] ∧
        ∀ w ∈ [u, v], ∀ i ∈ [(0 : ℕ), (7 : ℕ)],
          PEqualNP.ReadTwo.wval C (fun (k : Fin (14 : ℕ)) => Decidable.decide ((k : ℕ) = i)) w
            = Bool.false) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) ∧     (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧       (∀ (x2 x3 : Fin (7 : ℕ)), x2 = x3 ∨ x2 = x3 + (1 : Fin (7 : ℕ)) ∨ x2 = x3 + (3 : Fin (7 : ℕ)) → x1.eval (List.ofFn fun (x5 : Fin (14 : ℕ)) => Decidable.decide (x5 = Fin.castAdd (7 : ℕ) x2 ∨ x5 = Fin.natAdd (7 : ℕ) x3)) = Bool.true) ∧         (∀ x2 ∈ [(127 : ℕ), (244 : ℕ), (480 : ℕ), (720 : ℕ), (1188 : ℕ), (3008 : ℕ), (16256 : ℕ)], ∀ (x4 : Fin (7 : ℕ)), x1.eval (List.ofFn fun (x5 : Fin ((7 : ℕ) + (7 : ℕ))) => Fin.addCases (fun (x6 : Fin (7 : ℕ)) => x2.testBit ↑(x6 + x4)) (fun (x6 : Fin (7 : ℕ)) => x2.testBit ((7 : ℕ) + ↑(x6 + x4))) x5) = Bool.false) ∧           ∀ (x2 : Bool),             ∃ (x3 : List (Fin (3 : ℕ))),               x3.length = (14 : ℕ) + x1.size ∧                 have x4 : ℕ → ℕ := fun (x4 : ℕ) => ↑(x3.getD x4 (0 : Fin (3 : ℕ)));                 x4 (if x2 = Bool.true then (0 : ℕ) else (7 : ℕ)) = (0 : ℕ) ∧ x4 (if x2 = Bool.true then (7 : ℕ) else (0 : ℕ)) ≤ (1 : ℕ) ∧ (2 : ℕ) ≤ x4 x1.output ∧ ∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 x8 : ℕ), x1.gates[x5]? = Option.some x6 → x6.inputs = [x7, x8] → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and → x4 ((14 : ℕ) + x5) ≤ x4 x7 + x4 x8) ∧ (x6.op = PEqualNP.CircuitLowerBounds.GateOp.or → x4 ((14 : ℕ) + x5) ≤ Min.min (x4 x7) (x4 x8)) := by
  obtain ⟨C, jj, uu, vv, gg, hsize, hmodel, hinc, hmask, hout, hgj, hggop, hggin, hff⟩ :=
    topAndOnTwoFalseOperands
  -- the size is the number of gates, and the wire list is the fold of the gates
  have hsz : C.size = C.gates.length := rfl
  have hwir : ∀ x : List Bool, C.wires x
      = List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
        C.gates := fun _ => rfl
  -- a fold result extends its start
  have hpre : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w0 : List Bool),
      ∃ r : List Bool,
        List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0 gs
          = w0 ++ r ∧ r.length = gs.length := by
    intro gs w0
    induction gs generalizing w0 with
    | nil => exact ⟨[], by simp, by simp⟩
    | cons g gs ih =>
      obtain ⟨r, hr, hrl⟩ := ih (w0 ++ [g.op.eval (g.inputs.map fun i => w0.getD i false)])
      refine ⟨g.op.eval (g.inputs.map fun i => w0.getD i false) :: r, ?_, by simp [hrl]⟩
      simp only [List.foldl_cons]
      rw [hr]
      simp
  have hleft : ∀ (l l' : List Bool) (i : ℕ), i < l.length →
      (l ++ l').getD i false = l.getD i false := by
    intro l l' i h
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  have hjun : ∀ (l : List Bool) (b : Bool) (r : List Bool),
      (l ++ b :: r).getD l.length false = b := by
    intro l b r
    simp [List.getD_eq_getElem?_getD]
  -- the wire of a gate holds the operation applied to its operand wires
  have hgate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w0 : List Bool) (j : ℕ)
      (g : PEqualNP.CircuitLowerBounds.Gate), gs[j]? = Option.some g →
      (∀ i ∈ g.inputs, i < w0.length + j) →
      (List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0
          gs).getD (w0.length + j) false
        = g.op.eval (g.inputs.map fun i =>
            (List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0
              gs).getD i false) := by
    intro gs
    induction gs with
    | nil => intro w0 j g hj _; simp at hj
    | cons g0 gs ih =>
      intro w0 j g hj hb
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        obtain ⟨r, hr, _⟩ :=
          hpre gs (w0 ++ [g0.op.eval (g0.inputs.map fun i => w0.getD i false)])
        have hbig :
            List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0
                (g0 :: gs)
              = w0 ++ (g0.op.eval (g0.inputs.map fun i => w0.getD i false) :: r) := by
          simp only [List.foldl_cons]
          rw [hr]
          simp
        rw [hbig, Nat.add_zero, hjun]
        rw [List.map_congr_left (fun a ha => hleft _ _ _ (by
          have h := hb a ha
          linarith))]
      | succ j =>
        rw [List.getElem?_cons_succ] at hj
        have hlen :
            (w0 ++ [g0.op.eval (g0.inputs.map fun i => w0.getD i false)]).length
              = w0.length + 1 := by simp
        have key := ih (w0 ++ [g0.op.eval (g0.inputs.map fun i => w0.getD i false)]) j g hj (by
          intro i hi
          have h := hb i hi
          rw [hlen]
          linarith)
        rw [hlen] at key
        simp only [List.foldl_cons]
        rw [show w0.length + (j + 1) = w0.length + 1 + j from by ring]
        exact key
  -- reading an input list and a labelling list back
  have hinp : ∀ (N : ℕ) (f : Fin N → Bool) (n : ℕ) (h : n < N),
      (List.ofFn f).getD n false = f ⟨n, h⟩ := by
    intro N f n h
    simp [List.getD_eq_getElem?_getD, h]
  have hread : ∀ (N : ℕ) (ff : ℕ → Fin (3 : ℕ)) (n : ℕ), n < N →
      (List.ofFn (fun (k : Fin N) => ff (k : ℕ))).getD n (0 : Fin (3 : ℕ)) = ff n := by
    intro N ff n h
    simp [List.getD_eq_getElem?_getD, h]
  have hbfalse : ∀ b : Bool, ¬(b = Bool.true) → b = Bool.false := by
    intro b h
    cases b
    · rfl
    · exact absurd rfl h
  -- the two operations on two operands
  have handev : ∀ a b : Bool,
      PEqualNP.CircuitLowerBounds.GateOp.and.eval [a, b] = (a && b) := by
    intro a b; cases a <;> cases b <;> rfl
  have horev : ∀ a b : Bool,
      PEqualNP.CircuitLowerBounds.GateOp.or.eval [a, b] = (a || b) := by
    intro a b; cases a <;> cases b <;> rfl
  have hnoc : PEqualNP.CircuitLowerBounds.GateOp.and
      ≠ PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro h; exact PEqualNP.CircuitLowerBounds.GateOp.noConfusion h
  -- the output wire is a gate wire
  have hjjlt : jj < C.gates.length := by
    by_contra hcon
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hcon)] at hgj
    simp at hgj
  have houtlt : C.output < (14 : ℕ) + C.size := by
    rw [hout, hsz]
    linarith
  -- ONE case of the last clause: the input wire i reads true, the other one is q
  have key : ∀ i q : ℕ, i < (14 : ℕ) → q < (14 : ℕ) →
      (∀ w ∈ [uu, vv],
        PEqualNP.ReadTwo.wval C (fun (k : Fin (14 : ℕ)) => Decidable.decide ((k : ℕ) = i)) w
          = Bool.false) →
      ∃ (x3 : List (Fin (3 : ℕ))), x3.length = (14 : ℕ) + C.size ∧
        ((x3.getD i (0 : Fin (3 : ℕ))) : ℕ) = (0 : ℕ) ∧
        ((x3.getD q (0 : Fin (3 : ℕ))) : ℕ) ≤ (1 : ℕ) ∧
        (2 : ℕ) ≤ ((x3.getD C.output (0 : Fin (3 : ℕ))) : ℕ) ∧
        ∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 x8 : ℕ),
          C.gates[x5]? = Option.some x6 → x6.inputs = [x7, x8] →
          (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and →
            ((x3.getD ((14 : ℕ) + x5) (0 : Fin (3 : ℕ))) : ℕ)
              ≤ ((x3.getD x7 (0 : Fin (3 : ℕ))) : ℕ)
                + ((x3.getD x8 (0 : Fin (3 : ℕ))) : ℕ)) ∧
          (x6.op = PEqualNP.CircuitLowerBounds.GateOp.or →
            ((x3.getD ((14 : ℕ) + x5) (0 : Fin (3 : ℕ))) : ℕ)
              ≤ Min.min ((x3.getD x7 (0 : Fin (3 : ℕ))) : ℕ)
                  ((x3.getD x8 (0 : Fin (3 : ℕ))) : ℕ)) := by
    intro i q hi hq hfal
    have hiout : ¬(i = C.output) := by
      intro hc
      rw [hout] at hc
      linarith
    have hqout : ¬(q = C.output) := by
      intro hc
      rw [hout] at hc
      linarith
    have hilt : i < (14 : ℕ) + C.size := by linarith
    have hqlt : q < (14 : ℕ) + C.size := by linarith
    -- the one-hot input, kept only through the three facts used below
    obtain ⟨z, hzlen, hzi, hzuv⟩ : ∃ z : List Bool, z.length = (14 : ℕ) ∧
        (C.wires z).getD i false = Bool.true ∧
        ∀ w ∈ [uu, vv], (C.wires z).getD w false = Bool.false := by
      refine ⟨List.ofFn (fun (k : Fin (14 : ℕ)) => Decidable.decide ((k : ℕ) = i)), by simp,
        ?_, hfal⟩
      obtain ⟨r, hr, _⟩ :=
        hpre C.gates (List.ofFn (fun (k : Fin (14 : ℕ)) => Decidable.decide ((k : ℕ) = i)))
      have hA := hleft (List.ofFn (fun (k : Fin (14 : ℕ)) => Decidable.decide ((k : ℕ) = i))) r i
        (by simpa using hi)
      have hB := hinp (14 : ℕ) (fun (k : Fin (14 : ℕ)) => Decidable.decide ((k : ℕ) = i)) i hi
      rw [hwir, hr, hA, hB]
      simp
    -- the labelling: 2 at the output wire, 1 at a wire that reads false, 0 at the rest
    obtain ⟨lab, hlablen, hlabT, hlabF, hlabO⟩ : ∃ lab : List (Fin (3 : ℕ)),
        lab.length = (14 : ℕ) + C.size ∧
        (∀ n : ℕ, n < (14 : ℕ) + C.size → ¬(n = C.output) →
          (C.wires z).getD n false = Bool.true →
          ((lab.getD n (0 : Fin (3 : ℕ))) : ℕ) = (0 : ℕ)) ∧
        (∀ n : ℕ, n < (14 : ℕ) + C.size → ¬(n = C.output) →
          (C.wires z).getD n false = Bool.false →
          ((lab.getD n (0 : Fin (3 : ℕ))) : ℕ) = (1 : ℕ)) ∧
        ((lab.getD C.output (0 : Fin (3 : ℕ))) : ℕ) = (2 : ℕ) := by
      obtain ⟨ff, hf0, hf1, hf2⟩ : ∃ ff : ℕ → Fin (3 : ℕ),
          (∀ n : ℕ, ¬(n = C.output) → (C.wires z).getD n false = Bool.true →
            ((ff n : Fin (3 : ℕ)) : ℕ) = (0 : ℕ)) ∧
          (∀ n : ℕ, ¬(n = C.output) → (C.wires z).getD n false = Bool.false →
            ((ff n : Fin (3 : ℕ)) : ℕ) = (1 : ℕ)) ∧
          ((ff C.output : Fin (3 : ℕ)) : ℕ) = (2 : ℕ) := by
        refine ⟨fun m => if m = C.output then (2 : Fin (3 : ℕ))
          else if (C.wires z).getD m false = Bool.true then (0 : Fin (3 : ℕ))
            else (1 : Fin (3 : ℕ)), ?_, ?_, ?_⟩
        · intro n hne ht
          have h : Fin.val (if n = C.output then (2 : Fin (3 : ℕ))
              else if (C.wires z).getD n false = Bool.true then (0 : Fin (3 : ℕ))
                else (1 : Fin (3 : ℕ))) = (0 : ℕ) := by
            rw [ht]
            simp [hne]
          exact h
        · intro n hne hf
          have h : Fin.val (if n = C.output then (2 : Fin (3 : ℕ))
              else if (C.wires z).getD n false = Bool.true then (0 : Fin (3 : ℕ))
                else (1 : Fin (3 : ℕ))) = (1 : ℕ) := by
            rw [hf]
            simp [hne]
          exact h
        · simp
      refine ⟨List.ofFn (fun (k : Fin ((14 : ℕ) + C.size)) => ff (k : ℕ)), by simp, ?_, ?_, ?_⟩
      · intro n hn hne ht
        rw [hread ((14 : ℕ) + C.size) ff n hn]
        exact hf0 n hne ht
      · intro n hn hne hf
        rw [hread ((14 : ℕ) + C.size) ff n hn]
        exact hf1 n hne hf
      · rw [hread ((14 : ℕ) + C.size) ff C.output houtlt]
        exact hf2
    -- a wire that reads false carries at least 1
    have hlow : ∀ n : ℕ, n < (14 : ℕ) + C.size → (C.wires z).getD n false = Bool.false →
        (1 : ℕ) ≤ ((lab.getD n (0 : Fin (3 : ℕ))) : ℕ) := by
      intro n hn hf
      by_cases hc : n = C.output
      · have h2 : ((lab.getD n (0 : Fin (3 : ℕ))) : ℕ) = (2 : ℕ) := by
          rw [hc]; exact hlabO
        linarith
      · have h2 := hlabF n hn hc hf
        linarith
    refine ⟨lab, hlablen, ?_, ?_, ?_, ?_⟩
    · exact hlabT i hilt hiout hzi
    · by_cases hqt : (C.wires z).getD q false = Bool.true
      · have h2 := hlabT q hqlt hqout hqt
        linarith
      · have h2 := hlabF q hqlt hqout (hbfalse _ hqt)
        linarith
    · linarith
    · intro x5 x6 x7 x8 h5 h6
      obtain ⟨hopc, a0, b0, hin0, hne0, ha0, hb0⟩ := hmodel x5 x6 h5
      have hpair : x7 = a0 ∧ x8 = b0 := by
        have hl : [x7, x8] = [a0, b0] := by rw [← h6, hin0]
        simpa using hl
      obtain ⟨rfl, rfl⟩ := hpair
      have h5lt : x5 < C.gates.length := by
        by_contra hcon
        rw [List.getElem?_eq_none (Nat.le_of_not_lt hcon)] at h5
        simp at h5
      have h5s : x5 < C.size := by rw [hsz]; exact h5lt
      have hx7lt : x7 < (14 : ℕ) + C.size := by linarith
      have hx8lt : x8 < (14 : ℕ) + C.size := by linarith
      have hglt : (14 : ℕ) + x5 < (14 : ℕ) + C.size := by linarith
      -- the gate wire holds the operation applied to the two operand wires
      have hgv : (C.wires z).getD ((14 : ℕ) + x5) false
          = x6.op.eval [(C.wires z).getD x7 false, (C.wires z).getD x8 false] := by
        have hbd : ∀ ii ∈ x6.inputs, ii < z.length + x5 := by
          rw [h6, hzlen]
          intro ii hii
          simp at hii
          rcases hii with h | h
          · rw [h]; exact ha0
          · rw [h]; exact hb0
        have hmain := hgate C.gates z x5 x6 h5 hbd
        rw [hzlen] at hmain
        rw [hwir z, hmain, h6]
        simp
      by_cases hco : (14 : ℕ) + x5 = C.output
      · -- the output gate: the AND of the hypothesis, paid for by 1 + 1
        have hx5jj : x5 = jj := by
          rw [hout] at hco
          exact Nat.add_left_cancel hco
        have hgj' : C.gates[x5]? = Option.some gg := by rw [hx5jj]; exact hgj
        have hx6 : x6 = gg := by simpa using h5.symm.trans hgj'
        have hopand : x6.op = PEqualNP.CircuitLowerBounds.GateOp.and := by
          rw [hx6]; exact hggop
        have hinuv : [x7, x8] = [uu, vv] := by rw [← h6, hx6]; exact hggin
        have h7u : x7 = uu ∧ x8 = vv := by simpa using hinuv
        have h1 : (1 : ℕ) ≤ ((lab.getD x7 (0 : Fin (3 : ℕ))) : ℕ) := by
          refine hlow x7 hx7lt ?_
          rw [h7u.1]
          exact hzuv uu (by simp)
        have h2 : (1 : ℕ) ≤ ((lab.getD x8 (0 : Fin (3 : ℕ))) : ℕ) := by
          refine hlow x8 hx8lt ?_
          rw [h7u.2]
          exact hzuv vv (by simp)
        have hvo : ((lab.getD ((14 : ℕ) + x5) (0 : Fin (3 : ℕ))) : ℕ) = (2 : ℕ) := by
          rw [hco]; exact hlabO
        refine ⟨fun _ => by linarith, fun hor => absurd (hopand.symm.trans hor) hnoc⟩
      · by_cases hw : (C.wires z).getD ((14 : ℕ) + x5) false = Bool.true
        · -- the gate reads true, so it carries 0 and nothing is owed
          have hv := hlabT ((14 : ℕ) + x5) hglt hco hw
          refine ⟨fun _ => by linarith, fun _ => ?_⟩
          rw [hv]
          exact Nat.zero_le _
        · -- the gate reads false, so it carries 1 and an operand pays for it
          have hwf := hbfalse _ hw
          have hv := hlabF ((14 : ℕ) + x5) hglt hco hwf
          rcases hopc with hA | hO
          · rw [hgv, hA, handev] at hwf
            refine ⟨fun _ => ?_, fun hor => absurd (hA.symm.trans hor) hnoc⟩
            have hone : (C.wires z).getD x7 false = Bool.false
                ∨ (C.wires z).getD x8 false = Bool.false := by
              cases h7 : (C.wires z).getD x7 false
              · exact Or.inl rfl
              · cases h8 : (C.wires z).getD x8 false
                · exact Or.inr rfl
                · rw [h7, h8] at hwf; exact absurd hwf (by simp)
            rcases hone with h | h
            · have h3 := hlow x7 hx7lt h
              linarith
            · have h3 := hlow x8 hx8lt h
              linarith
          · rw [hgv, hO, horev] at hwf
            refine ⟨fun hand => absurd (hO.symm.trans hand) (fun h => hnoc h.symm),
              fun _ => ?_⟩
            have h7 : (C.wires z).getD x7 false = Bool.false := by
              cases h : (C.wires z).getD x7 false
              · rfl
              · rw [h] at hwf; exact absurd hwf (by simp)
            have h8 : (C.wires z).getD x8 false = Bool.false := by
              cases h : (C.wires z).getD x8 false
              · rfl
              · rw [h] at hwf; exact absurd hwf (by simp)
            have h3 := hlow x7 hx7lt h7
            have h4 := hlow x8 hx8lt h8
            rw [hv]
            exact le_min h3 h4
  refine ⟨C, hsize, hmodel, hinc, hmask, ?_⟩
  intro x2
  cases x2 with
  | false =>
    exact key (7 : ℕ) (0 : ℕ) (by decide) (by decide) (fun w hw => hff w hw 7 (by simp))
  | true =>
    exact key (0 : ℕ) (7 : ℕ) (by decide) (by decide) (fun w hw => hff w hw 0 (by simp))
