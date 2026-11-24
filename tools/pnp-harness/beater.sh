#!/usr/bin/env bash
set -uo pipefail
DESK=https://pequalnp.com/desk
S="$(cd "$(dirname "$0")" && pwd)"
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
