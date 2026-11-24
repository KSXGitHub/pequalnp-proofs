#!/usr/bin/env bash
# Hunt for a COUNTEREXAMPLE automatically. Zero model tokens; a few seconds per attempt.
#
# These steps are hypotheses of machine-made cuts, and a cut can produce a statement that is
# simply FALSE. We proved one that way already (L-meta-3628): its conclusion quantified over
# every smaller circuit under a gate budget, and the EMPTY circuit met the budget while being
# constant, contradicting a non-constancy hypothesis the step itself supplied. A counterexample
# is worth as much as a proof here, so it is worth probing for one on every step, for free.
#
# Each template tries to prove the NEGATION of the posted statement, spliced in verbatim by
# mkrefute.py, so a CHECK_OK here refutes the real statement and not a paraphrase of it.
#
#   usage: autorefute.sh <STEP>
# On success it leaves the proving scratch file in place and prints REFUTED.
set -uo pipefail
S="$(cd "$(dirname "$0")" && pwd)"; REPO=/home/user/pequalnp-proofs
gid="${1:?a step id}"
D="PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, PEqualNP.CircuitLowerBounds.Circuit.size, PEqualNP.CircuitLowerBounds.GateOp.eval, PEqualNP.MetaComplexity.circuitFun, PEqualNP.MetaComplexity.FanInTwo, List.countP, List.countP.go"

# The degenerate objects that have actually broken a step of this family, plus the plain closers.
# An out-of-range output wire reads false, so the empty circuit with a large output computes the
# constant false function; with output 0 it computes input wire 0 instead.
TACTICS=(
  "decide"
  "intro h <;> simp_all [$D]"
  "intro h <;> exact absurd h (by decide)"
  "intro h <;> aesop"
  "intro h <;> omega"
  "intro h <;> simp_all [$D] <;> omega"
  "intro h <;> exact absurd (h ⟨[], 0⟩) (by simp_all [$D])"
  "intro h <;> exact absurd (h ⟨[], 5⟩) (by simp_all [$D])"
  "intro h <;> exact absurd (h ⟨[], 9⟩) (by simp_all [$D])"
  "intro h <;> have := h ⟨[], 0⟩ <;> simp_all [$D]"
  "intro h <;> have := h ⟨[], 5⟩ <;> simp_all [$D]"
  "intro h <;> have := h ⟨[], 9⟩ <;> simp_all [$D]"
  "intro h <;> have := h ⟨[], 13⟩ <;> simp_all [$D]"
  "intro h <;> have := h ⟨[], 25⟩ <;> simp_all [$D]"
  "intro h <;> have := h 0 <;> simp_all [$D]"
  "intro h <;> have := h 1 <;> simp_all [$D]"
  "intro h <;> have := h 0 0 <;> simp_all [$D]"
  "intro h <;> have := h ⟨[], 0⟩ <;> have := h ⟨[], 5⟩ <;> simp_all [$D]"
  "intro h <;> specialize h ⟨[], 5⟩ <;> simp_all [$D] <;> omega"
  "intro h <;> simp only [$D] at h <;> aesop"
  "intro h <;> exfalso <;> simp_all [$D] <;> decide"
)
tmp="$S/.refute.$gid.txt"
printf 'trying %d refutation templates on %s\n' "${#TACTICS[@]}" "$gid"
for t in "${TACTICS[@]}"; do
  printf '  %s\n' "$t" > "$tmp"
  f="$("$S"/mkrefute.py "$gid" "$tmp" 2>/dev/null)" || { echo "  (mkrefute failed)"; continue; }
  out="$("$S"/check.sh "$f" 2>&1)"
  if printf '%s' "$out" | grep -q '^CHECK_OK'; then
    echo "REFUTED $gid by: $t"
    echo "  the proving file is left at: $f"
    rm -f "$tmp"; exit 0
  fi
  printf '    no: %s\n' "$(printf '%s' "$out" | grep -oE 'error: .{0,50}' | head -1)"
done
# nothing worked: do not leave a broken scratch file lying around
rm -f "$tmp" "$REPO"/lean/PEqualNP/Outside/zz_refute_"$(printf '%s' "$gid" | tr 'a-z-' 'a-z_')".lean 2>/dev/null
echo "NO_REFUTATION_FOUND $gid"
exit 1
