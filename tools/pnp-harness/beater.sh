#!/usr/bin/env bash
set -uo pipefail
DESK=https://pequalnp.com/desk
# Resolve the SYMLINK before taking the directory. $P/<script>.sh are symlinks into this
# directory, and bash sets $0 to the path used to invoke the script, not its target - so a
# plain `dirname "$0"` gave the SCRATCHPAD for every symlinked call and this directory for
# every direct one. That split the harness state in two: live/, steps/, dead/ and done/
# existed twice, the poller beat only its own copy, and leases drawn by hand expired
# unbeaten and unlogged while 166 step statements sat in the other copy unnoticed.
S="$(cd "$(dirname "$(readlink -f "$0")")" && pwd)"
while true; do
  for f in "$S"/live/*.lease; do
    [ -e "$f" ] || continue
    gid="$(basename "$f" .lease)"; lease="$(cat "$f")"
    code="$(curl -s -m 20 -o /dev/null -w '%{http_code}' -X POST "$DESK/beat?lease=$lease")"
    ts="$(date -u +%H:%M:%S)"
    if [ "$code" = "410" ]; then
      echo "$ts DEAD $gid (410 - settled or withdrawn elsewhere)" >> "$S/logs/beater.log"
      mv "$f" "$S/dead/$gid.lease" 2>/dev/null || true
    elif [ "$code" != "200" ]; then
      echo "$ts WARN $gid beat http=$code" >> "$S/logs/beater.log"
    fi
  done
  sleep 480
done
