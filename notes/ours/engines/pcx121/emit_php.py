#!/usr/bin/env python3
"""Emit the Lean file for a PHP m n Res(+) certificate.

The checker is the one already on main in lean/PEqualNP/Outside/L_pcx_183.lean
(`chkL`, `chkL_sound`, `wkB`, `wkB_sound`, `axBPHP`, `axBPHP_sound`): a Bool
function on a list of (line, justification) whose soundness theorem produces an
`IsLinDerivation`, so the Lean side is a list literal plus `decide +kernel`.
It is copied here into this file's own namespace (each proof is a NEW file; a
file on main is never edited).

usage: emit_lean.py CERT.json OUT.lean MODULENAME BOUND
"""

from __future__ import annotations

import json
import pathlib
import sys

HEAD = r"""import Mathlib
import PEqualNP.Defs

namespace %(ns)s

open PEqualNP.ProofComplexity

theorem memD {α : Type} (l : List α) (d : α) (i : ℕ) (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

def ext {V : Type} [DecidableEq V] (a : V → Bool) (v : V) (b : Bool) : V → Bool :=
  fun w => if w = v then b else a w

def allA {V : Type} [DecidableEq V] : List V → List (V → Bool)
  | [] => [fun _ => false]
  | v :: vs => (allA vs).flatMap (fun a => [ext a v false, ext a v true])

theorem allA_cover {V : Type} [DecidableEq V] :
    ∀ (vs : List V) (a : V → Bool), ∃ b ∈ allA vs, ∀ v ∈ vs, b v = a v
  | [], a => ⟨fun _ => false, by simp [allA], by simp⟩
  | v :: vs, a => by
    obtain ⟨b, hb, hba⟩ := allA_cover vs a
    refine ⟨ext b v (a v), ?_, ?_⟩
    · simp only [allA, List.mem_flatMap]
      exact ⟨b, hb, by cases a v <;> simp⟩
    · intro w hw
      simp only [ext]
      split_ifs with hwv
      · rw [hwv]
      · exact hba w (by simpa [hwv] using hw)

def satB {V : Type} (a : V → Bool) (C : LinClause V) : Bool :=
  decide (∃ q ∈ C, decide (Odd (q.1.filter (fun v => a v = true)).card) = q.2)

theorem satB_iff {V : Type} (a : V → Bool) (C : LinClause V) :
    satB a C = true ↔ LinClauseSat a C := by
  unfold satB LinClauseSat LinEqSat
  simp only [decide_eq_true_eq]
  refine exists_congr fun q => and_congr_right fun _ => ?_
  rcases q with ⟨f, b⟩
  cases b <;> simp

theorem sat_congr {V : Type} (a b : V → Bool) (C : LinClause V) (vs : List V)
    (hv : ∀ q ∈ C, ∀ v ∈ q.1, v ∈ vs) (hab : ∀ v ∈ vs, b v = a v) :
    LinClauseSat b C ↔ LinClauseSat a C := by
  unfold LinClauseSat LinEqSat
  refine exists_congr fun q => and_congr_right fun hq => ?_
  rw [Finset.filter_congr (fun v hv' => by rw [hab v (hv q hq v hv')])]

def wkB {V : Type} [DecidableEq V] (vs : List V) (C D : LinClause V) : Bool :=
  decide (∀ q ∈ C, ∀ v ∈ q.1, v ∈ vs) && decide (∀ q ∈ D, ∀ v ∈ q.1, v ∈ vs) &&
    (allA vs).all (fun a => !satB a C || satB a D)

theorem wkB_sound {V : Type} [DecidableEq V] (vs : List V) (C D : LinClause V)
    (h : wkB vs C D = true) : ∀ a : V → Bool, LinClauseSat a C → LinClauseSat a D := by
  simp only [wkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hC, hD⟩, hall⟩ := h
  intro a ha
  obtain ⟨b, hb, hba⟩ := allA_cover vs a
  have hh := hall b hb
  rw [← sat_congr a b D vs hD hba]
  rw [← sat_congr a b C vs hC hba, ← satB_iff] at ha
  rw [← satB_iff]
  simpa [ha] using hh

inductive Step (V : Type) where
  | ax : Clause V → Step V
  | rs : ℕ → ℕ → Finset V → Step V
  | wk : ℕ → List V → Step V

def chkL {V : Type} [DecidableEq V] (ax : Clause V → Bool) :
    List (LinClause V × Step V) → Bool
  | [] => true
  | (R, .ax C) :: t => ax C && decide (linOfClause C = R) && chkL ax t
  | (R, .rs i j f) :: t =>
      decide (i < t.length) && decide (j < t.length) &&
      decide ((f, false) ∈ (t.map Prod.fst).getD i ∅ ∧ (f, true) ∈ (t.map Prod.fst).getD j ∅ ∧
        R = ((t.map Prod.fst).getD i ∅).erase (f, false) ∪ ((t.map Prod.fst).getD j ∅).erase (f, true)) &&
      chkL ax t
  | (R, .wk i vs) :: t => decide (i < t.length) && wkB vs ((t.map Prod.fst).getD i ∅) R && chkL ax t

theorem chkL_sound {V : Type} [DecidableEq V] (F : Set (Clause V)) (ax : Clause V → Bool)
    (hax : ∀ C, ax C = true → C ∈ F) :
    ∀ l, chkL ax l = true → IsLinDerivation ((fun C => linOfClause C) '' F) (l.map Prod.fst)
  | [], _ => IsLinDerivation.nil
  | (R, .ax C) :: t, h => by
    simp only [chkL, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, ht⟩ := h
    exact IsLinDerivation.ax (chkL_sound F ax hax t ht) ⟨C, hax C h1, h2⟩
  | (R, .rs i j f) :: t, h => by
    simp only [chkL, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi, hj⟩, h1, h2, h3⟩, ht⟩ := h
    exact IsLinDerivation.res (chkL_sound F ax hax t ht) (memD _ _ _ (by simpa using hi))
      (memD _ _ _ (by simpa using hj)) ⟨f, h1, h2, h3⟩
  | (R, .wk i vs) :: t, h => by
    simp only [chkL, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi, h1⟩, ht⟩ := h
    exact IsLinDerivation.weak (chkL_sound F ax hax t ht) (memD _ _ _ (by simpa using hi))
      (wkB_sound vs _ R h1)

def axPHP (m n : ℕ) (C : Clause (Fin m × Fin n)) : Bool :=
  decide (∃ i : Fin m, C = Finset.univ.image (fun j : Fin n => ((i, j), true))) ||
  decide (∃ i : Fin m, ∃ i' : Fin m, ∃ j : Fin n, i ≠ i' ∧ C = {((i, j), false), ((i', j), false)})

theorem axPHP_sound (m n : ℕ) : ∀ C, axPHP m n C = true → C ∈ PHP m n := by
  intro C h
  simp only [axPHP, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨i, hi⟩ | ⟨i, i', j, hne, hC⟩
  · exact Or.inl ⟨i, hi⟩
  · exact Or.inr ⟨i, i', j, hne, hC⟩

def cert : List (LinClause (Fin %(M)d × Fin %(N)d) × Step (Fin %(M)d × Fin %(N)d)) := [
"""

TAIL = r"""

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hc : chkL (axPHP %(M)d %(N)d) cert = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem hm : (∅ : LinClause (Fin %(M)d × Fin %(N)d)) ∈ cert.map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
theorem hl : (cert.map Prod.fst).length ≤ %(bound)d := by decide +kernel

end %(ns)s

theorem %(thm)s : ∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin %(M)d × Fin %(N)d)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.PHP %(M)d %(N)d) π ∧ π.length ≤ %(bound)d := by
  exact ⟨%(ns)s.cert.map Prod.fst, ⟨%(ns)s.chkL_sound _ (%(ns)s.axPHP %(M)d %(N)d) (%(ns)s.axPHP_sound %(M)d %(N)d) _ %(ns)s.hc, %(ns)s.hm⟩, %(ns)s.hl⟩
"""


def form(raw: list[list[int]]) -> str:
    vs = sorted((int(a), int(b)) for a, b in raw)
    return "{" + ", ".join(f"({i}, {b})" for i, b in vs) + "}"


def lin(eqs: list) -> str:
    if not eqs:
        return "∅"
    parts = [f"({form(e[0])}, {str(bool(e[1])).lower()})" for e in eqs]
    return "{" + ", ".join(parts) + "}"


def plain(eqs: list) -> str:
    """The ordinary clause whose linOfClause is this line (all forms singleton)."""
    parts = []
    for e in eqs:
        vs = e[0]
        assert len(vs) == 1, "an axiom line must have singleton forms only"
        i, b = int(vs[0][0]), int(vs[0][1])
        parts.append(f"(({i}, {b}), {str(bool(e[1])).lower()})")
    return "{" + ", ".join(parts) + "}"


def main() -> None:
    cert_path, out_path, module, bound = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
    d = json.loads(pathlib.Path(cert_path).read_text())
    assert d["formula"] == "php"
    lines = d["lines"]
    n = len(lines)
    assert n <= bound, f"certificate has {n} lines, bound is {bound}"
    ns = module + "_aux"
    body: list[str] = []
    for k, ln in enumerate(lines):
        lc = lin(ln["eqs"])
        if ln["rule"] == "ax":
            step = f".ax {plain(ln['eqs'])}"
        elif ln["rule"] == "res":
            i = int(ln["C"]) - k - 1          # premise holding (f, false)
            j = int(ln["D"]) - k - 1          # premise holding (f, true)
            assert i >= 0 and j >= 0
            step = f".rs {i} {j} {form(ln['form'])}"
        else:
            i = int(ln["C"]) - k - 1
            vs = sorted({(int(a), int(b)) for e in lines[int(ln["C"])]["eqs"]
                         for a, b in e[0]}
                        | {(int(a), int(b)) for e in ln["eqs"] for a, b in e[0]})
            vlist = "[" + ", ".join(f"({a}, {b})" for a, b in vs) + "]"
            step = f".wk {i} {vlist}"
        comma = "," if k + 1 < n else "]"
        body.append(f"  ({lc}, {step}){comma}")
    sub = {"ns": ns, "thm": module, "bound": bound,
           "M": int(d["m"]), "N": int(d["n"])}
    text = HEAD % sub + "\n".join(body) + TAIL % sub
    assert '"' not in text, "no double quotes are allowed in the file"
    assert "#" not in text
    pathlib.Path(out_path).write_text(text, encoding="utf-8")
    print(f"wrote {out_path}: {n} lines, bound {bound}, "
          f"{len(text.encode())} bytes")


if __name__ == "__main__":
    main()
