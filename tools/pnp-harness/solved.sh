#!/usr/bin/env bash
# Did a battery (or a worker) actually close a step? Decided from the FILE, not from stdout.
set -uo pipefail
S="$(cd "$(dirname "$0")" && pwd)"; REPO=/home/user/pequalnp-proofs
for gid in "$@"; do
  f="$(python3 -I -c 'import json,sys;print(json.load(open(sys.argv[1]))["gap"]["file"])' "$S/steps/$gid.json" 2>/dev/null)"
  if [ -z "$f" ] || [ ! -f "$REPO/$f" ]; then echo "$gid: no file"; continue; fi
  if grep -qE '\bsorry\b' "$REPO/$f"; then echo "$gid: still sorry (open)"
  else echo "$gid: NO SORRY - candidate proof, verify with lint.py + check.sh"; fi
done
