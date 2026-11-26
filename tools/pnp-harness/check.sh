#!/usr/bin/env bash
# Type-check ONE proof file without taking lake's build lock, so several workers can
# check at once. At most 2 checks run together (RAM is 15G, each check can want several).
#   usage: check.sh lean/PEqualNP/Outside/L_meta_1234.lean
set -uo pipefail
S="$(cd "$(dirname "$0")" && pwd)"
REPO=/home/user/pequalnp-proofs
export PATH="$HOME/.elan/bin:$PATH"
# REGENERATE leanpath.txt AND logs/ IF THEY ARE MISSING, because they do go
# missing and the failure is silent and confusing.
#
# Both are gitignored - leanpath.txt holds absolute container paths, logs/ holds
# flock files - so neither is tracked. And submit.py cuts the artifact branch
# with `git checkout -B <gid> upstream/main`, which REMOVES tools/pnp-harness/
# from the working tree because upstream/main does not carry it. Returning to
# main restores the TRACKED files and nothing else, so the first submission of a
# session deleted leanpath.txt permanently. Every later check then died on
# `cat: leanpath.txt: No such file or directory` followed by
# `lean: No such file or directory` - which reads like a broken toolchain, not a
# missing cache, and cost real time to diagnose.
mkdir -p "$S/logs"
if [ ! -s "$S/leanpath.txt" ]; then
  echo "check.sh: leanpath.txt missing, regenerating from lake (one-off, ~20s)" >&2
  (cd "$REPO/lean" && timeout 300 lake env printenv LEAN_PATH) > "$S/leanpath.txt" 2>/dev/null
  [ -s "$S/leanpath.txt" ] || { echo "CHECK_ERROR cannot build LEAN_PATH"; exit 2; }
fi
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
