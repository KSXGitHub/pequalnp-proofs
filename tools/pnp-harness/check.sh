#!/usr/bin/env bash
# Type-check ONE proof file without taking lake's build lock, so several workers can
# check at once. At most 2 checks run together (RAM is 15G, each check can want several).
#   usage: check.sh lean/PEqualNP/Outside/L_meta_1234.lean
set -uo pipefail
S="$(cd "$(dirname "$0")" && pwd)"
REPO=/home/user/pequalnp-proofs
export PATH="$HOME/.elan/bin:$PATH"
LEAN_PATH="$(cat "$S/leanpath.txt")"; export LEAN_PATH
f="${1:?a file}"
[ -f "$REPO/$f" ] || { echo "CHECK_ERROR no such file: $f"; exit 2; }
slot=""
for i in 1 2; do
  exec {fd}>"$S/logs/build.$i.lock"
  if flock -n $fd; then slot=$i; break; fi
  eval "exec ${fd}>&-"
done
if [ -z "$slot" ]; then
  exec {fd}>"$S/logs/build.1.lock"; flock -w 2400 $fd || { echo CHECK_ERROR lock timeout; exit 2; }
  slot=1
fi
cd "$REPO" || exit 2
start=$(date +%s)
out="$(timeout 2100 lean -D maxHeartbeats=1000000 "$f" 2>&1)"; rc=$?
el=$(( $(date +%s) - start ))
echo "--- lean exit=$rc in ${el}s (slot $slot) ---"
[ $rc -eq 124 ] && echo "CHECK_TIMEOUT after ${el}s"
printf '%s\n' "$out" | head -120
if [ $rc -eq 0 ]; then
  if printf '%s' "$out" | grep -qE "declaration uses .?sorry" || grep -qE '\bsorry(Ax)?\b' "$REPO/$f"; then
    echo "CHECK_FAIL: file still contains sorry"
  else
    echo "CHECK_OK: $f type-checks with no errors and no sorry"
  fi
else
  echo "CHECK_FAIL: lean reported errors (above)"
fi
