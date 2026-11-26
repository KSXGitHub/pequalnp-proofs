r"""Emit lean/PEqualNP/Outside/L_meta_4873.lean from a found circuit.

Usage: python3 mklean.py gates.json
where gates.json = {"gates": [["or",0,1], ...], "output_index": k}
The circuit is re-verified over all 16384 rows before anything is written.
"""
from __future__ import annotations

import json
import sys

import inc

STMT = (
    'have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) '
    '=> x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); '
    'have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => '
    '∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), x1 x3 x4 ∧ '
    'x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true; '
    '∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),   '
    'x3.size ≤ (27 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (14 : ℕ) x3 ∧       '
    '(∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧         x3.output = (14 : ℕ) + x4 ∧           '
    'x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, '
    'inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧             '
    '(∀ (x7 x8 : Fin (7 : ℕ)), x1 x7 x8 → x3.eval (List.ofFn fun (x10 : Fin (14 : ℕ)) => '
    'Decidable.decide (x10 = Fin.castAdd (7 : ℕ) x7 ∨ x10 = Fin.natAdd (7 : ℕ) x8)) = Bool.true) '
    '∧               (∀ (x7 : Fin (14 : ℕ) → Bool), Maximal (fun (x8 : Fin (14 : ℕ) → Bool) '
    '=> ¬x2 x8) x7 → x3.eval (List.ofFn x7) = Bool.false) ∧                 '
    '∀ x7 ∈ [(0 : Fin (14 : ℕ)), (7 : Fin (14 : ℕ))],                   '
    'have x9 : Fin (14 : ℕ) → Bool := fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = x7); '
    'PEqualNP.BlindGate.wireValue x3 (14 : ℕ) x9 x5 = Bool.false ∧ '
    'PEqualNP.BlindGate.wireValue x3 (14 : ℕ) x9 x6 = Bool.false'
)

TEMPLATE = r'''import PEqualNP.Library.Helpers.ReplayCol

open PEqualNP.CircuitLowerBounds PEqualNP.Library.Helpers.ReplayCol

namespace PEqualNP.Outside.L_meta_4873_aux

/-- The circuit: %(ngates)d AND/OR gates of fan-in two, each reading two distinct earlier
wires; gate `j` is wire `14 + j`; the output gate %(outidx)d is an AND of wires %(b)d and %(c)d. -/
def C : Circuit :=
  ⟨
%(glist)s, %(outwire)d⟩

/-- Fano incidence: point `p` lies on line `q` when `p - q` is in the difference set {0,1,3}. -/
def F : (Fin (14 : ℕ) → Bool) → Bool := fun v =>
  Decidable.decide (∃ p q : Fin 7, (p = q ∨ p = q + 1 ∨ p = q + 3) ∧
    v (Fin.castAdd 7 p) = true ∧ v (Fin.natAdd 7 q) = true)

set_option maxHeartbeats 1000000 in
/-- `C` computes `F` on every one of the 16384 inputs, replayed by bitmask columns. -/
theorem computes : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = F x :=
  colReplay_sound (by decide +kernel)

theorem maximal (x : Fin 14 → Bool)
    (hx : Maximal (fun v : Fin 14 → Bool => ¬ ∃ p q : Fin 7,
      (p = q ∨ p = q + 1 ∨ p = q + 3) ∧
      v (Fin.castAdd 7 p) = true ∧ v (Fin.natAdd 7 q) = true) x) :
    C.eval (List.ofFn x) = false := by
  rw [computes x]
  exact decide_eq_false hx.1

theorem minterms : ∀ p q : Fin 7, (p = q ∨ p = q + 1 ∨ p = q + 3) →
    C.eval (List.ofFn fun i : Fin 14 =>
      Decidable.decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 q)) = true := by
  have h : ∀ p q : Fin 7, (p = q ∨ p = q + 1 ∨ p = q + 3) →
      F (fun i : Fin 14 =>
        Decidable.decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 q)) = true := by decide
  intro p q hpq
  rw [computes]
  exact h p q hpq

theorem size_le : C.size ≤ 27 := by decide

theorem ao2 : PEqualNP.TopForm.IsAO2 14 C := by decide +kernel

theorem nodup : ∀ g ∈ C.gates, g.inputs.Nodup := by decide +kernel

theorem out_eq : C.output = 14 + %(outidx)d := by decide

theorem gate_eq : C.gates[%(outidx)d]? =
    Option.some { op := GateOp.and, inputs := [%(b)d, %(c)d] : Gate } := by rfl

theorem blind : ∀ i ∈ [(0 : Fin 14), (7 : Fin 14)],
    PEqualNP.BlindGate.wireValue C 14 (fun j : Fin 14 => Decidable.decide (j = i)) %(b)d
        = false ∧
      PEqualNP.BlindGate.wireValue C 14 (fun j : Fin 14 => Decidable.decide (j = i)) %(c)d
        = false := by decide +kernel

end PEqualNP.Outside.L_meta_4873_aux

theorem PEqualNP.Outside.L_meta_4873 : %(stmt)s :=
  ⟨PEqualNP.Outside.L_meta_4873_aux.C, %(outidx)d, %(b)d, %(c)d,
    PEqualNP.Outside.L_meta_4873_aux.size_le, PEqualNP.Outside.L_meta_4873_aux.ao2,
    PEqualNP.Outside.L_meta_4873_aux.nodup, PEqualNP.Outside.L_meta_4873_aux.out_eq,
    PEqualNP.Outside.L_meta_4873_aux.gate_eq, PEqualNP.Outside.L_meta_4873_aux.minterms,
    PEqualNP.Outside.L_meta_4873_aux.maximal, PEqualNP.Outside.L_meta_4873_aux.blind⟩
'''


def main() -> int:
    rec = json.load(open(sys.argv[1]))
    gates = [(op, int(a), int(b)) for (op, a, b) in rec['gates']]
    k = int(rec['output_index'])
    S = inc.FANO
    out = 14 + k
    chk = S.check(gates, out, [1, 1 << 7])
    assert chk['mismatches'] == 0, chk
    assert chk['output_op'] == 'and' and chk['nodup'] and chk['readsback'], chk
    import os
    assert len(gates) <= int(os.environ.get(chr(83)+chr(90), 27)), len(gates)
    blind = chk['blind']
    assert isinstance(blind, dict)
    assert all(v == (False, False) for v in blind.values()), chk
    b, c = gates[k][1], gates[k][2]
    pieces = ['⟨GateOp.%s, [%d, %d]⟩' % g for g in gates]
    lines, cur = [], '    ['
    for p in pieces:
        if len(cur) + len(p) + 2 > 98:
            lines.append(cur.rstrip())
            cur = '     '
        cur += p + ', '
    lines.append(cur.rstrip().rstrip(',') + ']')
    src = TEMPLATE % {
        'ngates': len(gates), 'outidx': k, 'outwire': out, 'b': b, 'c': c,
        'glist': '\n'.join(lines), 'stmt': STMT,
    }
    assert '"' not in src, 'double quotes are refused by the format rules'
    path = '/home/user/pequalnp-proofs/lean/PEqualNP/Outside/L_meta_4873.lean'
    with open(path, 'w') as fh:
        fh.write(src)
    print('written', path, 'gates', len(gates), 'output gate', k, 'operands', b, c)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
