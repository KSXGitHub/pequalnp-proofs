#!/usr/bin/env bash
# Gate + push ONE proof file as its own branch. Prints the branch to open a pull request from.
# Refuses unless the desk still has the step open, the linter passes and lean accepts the file.
set -uo pipefail
S="$(cd "$(dirname "$0")" && pwd)"; REPO=/home/user/pequalnp-proofs
gid="${1:?a step id}"
file="$(python3 -I -c 'import json,sys;print(json.load(open(sys.argv[1]))["gap"]["file"])' "$S/steps/$gid.json")"
cd "$REPO"
echo "== 1. is the step still open? =="
st="$(curl -fsS -m 15 -G https://pequalnp.com/desk/step --data-urlencode "gap=$gid" 2>/dev/null)" || st=""
if [ -n "$st" ]; then
  s="$(printf '%s' "$st" | python3 -I -c 'import json,sys;print(json.load(sys.stdin).get("state",""))' 2>/dev/null)"
  echo "   desk says: ${s:-unknown}"
  case "$s" in open|leased|"") ;; *) echo "ABORT: step is $s - do not spend a run on it"; exit 3;; esac
fi
echo "== 2. format rules =="
"$S"/lint.py "$gid" || { echo "ABORT: lint failed"; exit 1; }
echo "== 3. lean accepts it? =="
out="$("$S"/check.sh "$file" 2>&1)"; printf '%s\n' "$out" | tail -4
printf '%s' "$out" | grep -q '^CHECK_OK' || { echo "ABORT: lean did not accept the file"; exit 1; }
echo "== 4. one branch, one commit, one file =="
git checkout -q main 2>/dev/null || true
git branch -D "$gid" -q 2>/dev/null || true
git checkout -q -b "$gid"
git add -f -- "$file"
staged="$(git diff --cached --name-only)"
[ "$staged" = "$file" ] || { echo "ABORT: staged files are not exactly one file: $staged"; git reset -q; git checkout -q main; exit 1; }
git commit -q -F - <<MSG
$gid

Co-Authored-By: Claude Opus 5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01WciZtTf3SkGtfE4r3rxdjL
MSG
for i in 1 2 3 4; do git push -q -u origin "$gid" && break || { echo "   push retry $i"; sleep $((i*5)); }; done
cp -f "$file" "$S/done/$(basename "$file")" 2>/dev/null || true
echo "== 5. pushed =="
git log --oneline -1
echo "   files changed vs main: $(git diff --name-only main...HEAD | tr '\n' ' ')"
git checkout -q main
echo "BRANCH_READY $gid"
