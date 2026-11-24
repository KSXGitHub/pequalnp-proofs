#!/usr/bin/env bash
# Try a battery of one-line tactic proofs on a step. Costs no model tokens, a few seconds each.
# Any step this closes is a free win; otherwise it tells us the step needs a real attempt.
# usage: autotry.sh <STEP>
set -uo pipefail
S="$(cd "$(dirname "$0")" && pwd)"; REPO=/home/user/pequalnp-proofs
gid="${1:?a step id}"
read -r file module < <(python3 -I -c '
import json,sys; g=json.load(open(sys.argv[1]))["gap"]; print(g["file"], g["module"])' "$S/steps/$gid.json")
stmt="$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["gap"]["statement"])' "$S/steps/$gid.json")"
imports="$(python3 -I -c '
import json,sys
g=json.load(open(sys.argv[1]))["gap"]
print("".join("import %s\n" % m for m in (g.get("imports") or [])), end="")' "$S/steps/$gid.json")"
TACTICS=(
  "decide" "rfl" "trivial" "simp" "simp_all" "omega" "norm_num" "tauto" "aesop"
  "intros <;> simp_all" "intros <;> omega" "intros <;> decide" "intros <;> norm_num"
  "intros <;> aesop" "intros <;> tauto" "intros <;> rfl" "intros <;> trivial"
  "simp_all <;> omega" "simp_all <;> decide" "norm_num <;> omega"
  "intro h <;> simp_all <;> omega" "intros <;> simp_all <;> omega"
  "intros <;> exfalso <;> simp_all" "intros <;> exfalso <;> omega"
  "intros <;> first | omega | decide | simp_all | aesop"
  "intros <;> constructor <;> simp_all"
  "intros <;> simp_all <;> aesop"
  "intros <;> omega_nat" "intros <;> positivity" "intros <;> norm_num <;> aesop"
)
tmp="$REPO/lean/PEqualNP/Outside/zz_auto_${gid//-/_}.lean"
cp -f "$REPO/$file" "$S/done/.$gid.bak" 2>/dev/null || true
printf 'trying %d one-liners on %s\n' "${#TACTICS[@]}" "$gid"
for t in "${TACTICS[@]}"; do
  printf 'import Mathlib\n%s\nset_option maxHeartbeats 1000000 in\ntheorem %s : %s := by\n  %s\n' \
    "$imports" "$module" "$stmt" "$t" > "$tmp"
  out="$(cd "$REPO" && timeout 180 env PATH="$HOME/.elan/bin:$PATH" LEAN_PATH="$(cat "$S/leanpath.txt")" \
         lean "lean/PEqualNP/Outside/zz_auto_${gid//-/_}.lean" 2>&1)"; rc=$?
  if [ $rc -eq 0 ] && ! printf '%s' "$out" | grep -qE "declaration uses .?sorry"; then
    echo "SOLVED by: $t"
    printf 'import Mathlib\n%s\ntheorem %s : %s := by\n  %s\n' "$imports" "$module" "$stmt" "$t" > "$REPO/$file"
    rm -f "$tmp"; exit 0
  fi
  printf '  no: %-46s %s\n' "$t" "$(printf '%s' "$out" | grep -oE 'error: [^\n]{0,60}' | head -1)"
done
rm -f "$tmp"
echo "AUTOTRY_EXHAUSTED $gid - needs a real attempt"
exit 1
