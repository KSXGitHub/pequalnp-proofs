#!/usr/bin/env bash
# What declarations does this file actually ADD to the Lean environment?
#
# This exists because the upstream checker counts environment declarations, not syntax, and our
# linter only read the documented format rules. A reduction file that contained exactly one
# `theorem` was refused with:
#     REJECTED (reduce-extra): ... declares more than its theorem:
#     [PEqualNP.TopForm.centreless.congr_simp, ..., PEqualNP.CircuitLowerBounds.Circuit.size.eq_1]
# Those were AUTO-GENERATED: `X.eq_1` is an equation lemma emitted when a tactic unfolds a
# definition (simp/rw/unfold on a project definition), and `X.congr_simp` is a congruence lemma
# emitted when simp is asked to rewrite with a definition. Nothing in the source shows them.
#
#   usage: decls.sh lean/PEqualNP/Outside/R_meta_5266_1.lean
#
# For an R_ reduction file: SUCCESS is exactly one name, the theorem itself.
# For an L_ direct proof: every added name should sit inside the module's own namespace;
# anything landing in another namespace (a .eq_1 or .congr_simp on a project definition) is a
# risk, since the rules say only the one theorem stands outside the module's namespace block.
set -uo pipefail
S="$(cd "$(dirname "$0")" && pwd)"; REPO=/home/user/pequalnp-proofs
f="${1:?a file under lean/PEqualNP/Outside/}"
[ -f "$REPO/$f" ] || { echo "no such file: $f"; exit 2; }
base="$(basename "$f" .lean)"
probe="lean/PEqualNP/Outside/zz_decls_${base}.lean"
# the probe lists env.constants.map₂, which holds exactly what THIS file added
{ cat "$REPO/$f"
  printf '\n\nopen Lean Elab Command in\n'
  printf '#eval show CommandElabM Unit from do\n'
  printf '  let env <- getEnv\n'
  printf '  for (n, _) in env.constants.map2.toList do\n'
  printf '    logInfo m!"DECL {n}"\n'
} | sed 's/map2/map₂/; s/<- getEnv/← getEnv/' > "$REPO/$probe"
out="$("$S"/check.sh "$probe" 2>&1)"
rm -f "$REPO/$probe"
names="$(printf '%s' "$out" | grep -oE 'DECL [^ ]+' | sed 's/^DECL //' | sort -u)"
if [ -z "$names" ]; then
  echo "PROBE FAILED - could not list declarations. Raw tail:"
  printf '%s\n' "$out" | tail -15
  exit 2
fi
n="$(printf '%s\n' "$names" | grep -c .)"
echo "declarations this file adds: $n"
printf '%s\n' "$names" | sed 's/^/  /'
case "$base" in
  R_*) if [ "$n" -eq 1 ]; then echo "DECLS_OK (reduction: exactly one declaration)"; else
         echo "DECLS_FAIL (reduction: must add exactly ONE declaration, found $n)"; exit 1; fi ;;
  L_*) ns="PEqualNP.Outside.$base"
       stray="$(printf '%s\n' "$names" | grep -v "^$ns" || true)"
       if [ -z "$stray" ]; then echo "DECLS_OK (all inside $ns)"; else
         echo "DECLS_WARN - these land outside the module namespace:"; printf '%s\n' "$stray" | sed 's/^/    /'
         echo "  Auto-generated lemmas on project definitions are the usual cause; they come from"
         echo "  passing a DEFINITION to simp/rw/unfold. Use a rfl-typed have, or show/change."
       fi ;;
esac
