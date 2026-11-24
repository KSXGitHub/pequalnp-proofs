#!/usr/bin/env bash
# Open the pull request for every verified artifact branch sitting on the fork.
#
# Run this on a machine where `gh` is signed in AS YOU (`gh auth status`). It needs no clone and
# no local state: it discovers the branches from the fork, skips any that already have a pull
# request upstream, and opens the rest. Safe to re-run - it never opens a duplicate.
#
#   bash open-prs.sh          # open every queued pull request
#   bash open-prs.sh --dry    # list what it would do, change nothing
#
# Why this exists: the agent that produced these branches cannot open the pull requests itself.
# A cross-fork pull request POSTs to the BASE repository, and the Claude GitHub App is not
# installed on open-goat/pequalnp-proofs, which belongs to a third party, so the API answers
# 403 Resource not accessible by integration. Pushing to the fork works; opening upstream does
# not. This script closes that last step with your own credentials, on your own machine.
set -uo pipefail

FORK=KSXGitHub/pequalnp-proofs
UPSTREAM=open-goat/pequalnp-proofs
DRY=0
[ "${1:-}" = "--dry" ] && DRY=1

command -v gh >/dev/null || { echo "missing: gh (https://cli.github.com)" >&2; exit 1; }
gh auth status >/dev/null 2>&1 || { echo "gh is not signed in. Run: gh auth login" >&2; exit 1; }

me="$(gh api user --jq .login)"
echo "signed in as: $me"
echo "fork:         $FORK"
echo "upstream:     $UPSTREAM"
echo

# Artifact branches are named after the step: L-<prog>-<n> for a direct proof, R-<prog>-<n>-<k>
# for a reduction. Anything else on the fork (main, the working branch) is not an artifact.
branches="$(gh api "repos/$FORK/branches" --paginate --jq '.[].name' \
            | grep -E '^[LR]-[a-z]+-[0-9]+(-[0-9]+)?$' | sort)"

[ -n "$branches" ] || { echo "no artifact branches on the fork; nothing to do"; exit 0; }

opened=0; skipped=0; failed=0
while IFS= read -r b; do
  [ -n "$b" ] || continue
  # Already open or merged from this head? Then leave it alone.
  existing="$(gh pr list --repo "$UPSTREAM" --head "$b" --state all \
              --json number,state,url --jq '.[] | [.number,.state,.url] | @tsv' 2>/dev/null)"
  if [ -n "$existing" ]; then
    printf 'SKIP   %-22s already has a pull request: %s\n' "$b" "$existing"
    skipped=$((skipped+1)); continue
  fi
  # What one file does it add? Shown so you can eyeball it before it goes out.
  file="$(gh api "repos/$UPSTREAM/compare/main...$me:$b" --jq '.files[].filename' 2>/dev/null | tr '\n' ' ')"
  if [ "$DRY" = "1" ]; then
    printf 'WOULD  %-22s adds: %s\n' "$b" "${file:-<could not read>}"
    continue
  fi
  body="$(printf '**Gap id** (from the desk): %s\n\n**The one file this adds**: %s\n\n**Agent used** (keep exactly one line):\n- Claude Code\n' \
          "$(printf '%s' "$b" | sed -E 's/^R-([a-z]+)-([0-9]+)-[0-9]+$/L-\1-\2/; s/^L-/L-/')" "${file% }")"
  if url="$(gh pr create --repo "$UPSTREAM" --head "$me:$b" --base main --title "$b" --body "$body" 2>&1)"; then
    printf 'OPENED %-22s %s\n' "$b" "$url"
    opened=$((opened+1))
  else
    printf 'FAILED %-22s %s\n' "$b" "$url"
    failed=$((failed+1))
  fi
done <<< "$branches"

echo
echo "opened $opened, skipped $skipped, failed $failed"
echo "Each pull request is checked automatically within minutes; the verdict is posted on it as a"
echo "comment: ACCEPTED, REJECTED or FAULT. A FAULT says nothing about the proof and is re-checked."
