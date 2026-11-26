#!/usr/bin/env bash
# Did a battery (or a worker) actually close a step? Decided from the FILE, not from stdout.
set -uo pipefail
# Resolve the SYMLINK before taking the directory. $P/<script>.sh are symlinks into this
# directory, and bash sets $0 to the path used to invoke the script, not its target - so a
# plain `dirname "$0"` gave the SCRATCHPAD for every symlinked call and this directory for
# every direct one. That split the harness state in two: live/, steps/, dead/ and done/
# existed twice, the poller beat only its own copy, and leases drawn by hand expired
# unbeaten and unlogged while 166 step statements sat in the other copy unnoticed.
S="$(cd "$(dirname "$(readlink -f "$0")")" && pwd)"; REPO=/home/user/pequalnp-proofs
for gid in "$@"; do
  f="$(python3 -I -c 'import json,sys;print(json.load(open(sys.argv[1]))["gap"]["file"])' "$S/steps/$gid.json" 2>/dev/null)"
  if [ -z "$f" ] || [ ! -f "$REPO/$f" ]; then echo "$gid: no file"; continue; fi
  if grep -qE '\bsorry\b' "$REPO/$f"; then echo "$gid: still sorry (open)"
  else echo "$gid: NO SORRY - candidate proof, verify with lint.py + check.sh"; fi
done
