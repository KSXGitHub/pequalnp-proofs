#!/usr/bin/env bash
# Screen every held lease in one pass: points, slots, graph.
# The fast reject is SLOTS FULL - a reduction there is never read.
set -uo pipefail
# Resolve the SYMLINK before taking the directory. $P/<script>.sh are symlinks into this
# directory, and bash sets $0 to the path used to invoke the script, not its target - so a
# plain `dirname "$0"` gave the SCRATCHPAD for every symlinked call and this directory for
# every direct one. That split the harness state in two: live/, steps/, dead/ and done/
# existed twice, the poller beat only its own copy, and leases drawn by hand expired
# unbeaten and unlogged while 166 step statements sat in the other copy unnoticed.
S="$(cd "$(dirname "$(readlink -f "$0")")" && pwd)"
for f in "$S"/live/*.lease; do
  [ -e "$f" ] || continue
  g="$(basename "$f" .lease)"
  pts="$(python3 -c "
import json,sys
try:
    d=json.load(open('$S/steps/$g.json'))
    t=d.get('lease',{}).get('terms',{})
    gp=d.get('gap',{})
    print(t.get('points','?'), t.get('kind','?'), t.get('level','?'), 'live=%s'%gp.get('reductions_live'), 'w=%s'%gp.get('weight'))
except Exception as e:
    print('?',e)
" 2>/dev/null)"
  el="$("$S"/eligible.py "$g" 2>&1 | head -1)"
  gr="$("$S"/pointsets.py "$g" 2>&1 | grep -E 'THIS IS|no all-2-bit|nothing to decode' | head -1)"
  printf '%-16s %-34s %s\n' "$g" "$pts" "${gr:-(no graph)}"
  printf '%-16s   %s\n' '' "$el"
done
