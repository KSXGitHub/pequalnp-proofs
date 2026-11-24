#!/usr/bin/env bash
# Open the pull request for every verified artifact branch on the fork — and refuse to open one
# for anything else.
#
# Run this where `gh` is signed in AS YOU (`gh auth status`). No clone, no local state needed.
# Idempotent: it skips branches that already have a pull request, so re-running is always safe.
#
#   bash open-prs.sh --dry    # show what it would do, change nothing  (DO THIS FIRST)
#   bash open-prs.sh          # open the queued pull requests
#
# Why this exists: the agent can push branches to the fork but cannot open pull requests
# upstream. A cross-fork pull request POSTs to the BASE repo, the Claude GitHub App is not
# installed on open-goat/pequalnp-proofs (a third party's), and this container's proxy
# intercepts api.github.com AND github.com for that repo by allowlist, so no credential helps.
#
# THE SAFETY RULES BELOW EXIST BECAUSE WE GOT THIS WRONG ONCE. A pull request was opened from
# the working branch by mistake, carried 24 harness files, and was refused on file count with
# the fixed sentence `one file per pull request, so send each step as its own pull request` -
# before the Lean was ever read. So this script never trusts a branch NAME. It verifies, against
# the real upstream base, that the branch adds EXACTLY ONE file under lean/PEqualNP/Outside/.
set -uo pipefail

FORK=KSXGitHub/pequalnp-proofs
UPSTREAM=open-goat/pequalnp-proofs
DRY=0
[ "${1:-}" = "--dry" ] && DRY=1

command -v gh >/dev/null || { echo "missing: gh (https://cli.github.com)" >&2; exit 1; }
gh auth status >/dev/null 2>&1 || { echo "gh is not signed in. Run: gh auth login" >&2; exit 1; }
me="$(gh api user --jq .login)"
echo "signed in as $me | fork $FORK | upstream $UPSTREAM"
[ "$DRY" = "1" ] && echo "(dry run: nothing will be created)"
echo

branches="$(gh api "repos/$FORK/branches" --paginate --jq '.[].name' | sort)"
opened=0; skipped=0; refused=0; failed=0

while IFS= read -r b; do
  [ -n "$b" ] || continue
  case "$b" in main|master|claude/*) continue ;; esac

  files="$(gh api "repos/$UPSTREAM/compare/main...$me:$b" --jq '.files[] | [.status,.filename] | @tsv' 2>/dev/null)"
  if [ -z "$files" ]; then
    printf 'REFUSE %-20s adds nothing against upstream (stale branch, or no commits)\n' "$b"
    refused=$((refused+1)); continue
  fi
  n="$(printf '%s\n' "$files" | grep -c .)"
  status="$(printf '%s\n' "$files" | head -1 | cut -f1)"
  name="$(printf '%s\n' "$files" | head -1 | cut -f2)"

  if [ "$n" -ne 1 ]; then
    printf 'REFUSE %-20s touches %s files, must be exactly 1\n' "$b" "$n"
    printf '%s\n' "$files" | sed 's/^/           /' | head -6
    refused=$((refused+1)); continue
  fi
  if [ "$status" != "added" ]; then
    printf 'REFUSE %-20s %s is %s, must be added\n' "$b" "$name" "$status"
    refused=$((refused+1)); continue
  fi
  case "$name" in
    lean/PEqualNP/Outside/L_*.lean|lean/PEqualNP/Outside/R_*.lean) ;;
    *) printf 'REFUSE %-20s %s is not a proof file under lean/PEqualNP/Outside/\n' "$b" "$name"
       refused=$((refused+1)); continue ;;
  esac

  existing="$(gh pr list --repo "$UPSTREAM" --head "$b" --state all --json number,state \
              --jq '.[] | "#\(.number) \(.state)"' 2>/dev/null | tr '\n' ' ')"
  if [ -n "$existing" ]; then
    printf 'SKIP   %-20s already has: %s\n' "$b" "$existing"
    skipped=$((skipped+1)); continue
  fi

  if [ "$DRY" = "1" ]; then
    printf 'WOULD  %-20s adds %s\n' "$b" "$name"; continue
  fi
  if url="$(gh pr create --repo "$UPSTREAM" --head "$me:$b" --base main \
              --title "$b" --body "" 2>&1)"; then
    printf 'OPENED %-20s %s\n' "$b" "$url"; opened=$((opened+1))
  else
    printf 'FAILED %-20s %s\n' "$b" "$url"; failed=$((failed+1))
  fi
done <<< "$branches"

echo
echo "opened $opened | skipped $skipped | refused $refused | failed $failed"
echo "A refused branch is NOT a problem with a proof - it means the branch is not shaped like one"
echo "added proof file, so sending it would be refused upstream anyway."
