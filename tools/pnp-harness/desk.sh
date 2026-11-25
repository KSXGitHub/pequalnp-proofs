#!/usr/bin/env bash
# Desk client for pequalnp.com. State lives beside this script.
set -uo pipefail
DESK=https://pequalnp.com/desk
S="$(cd "$(dirname "$0")" && pwd)"
HANDLE=KSXGitHub
case "${1:-}" in
next)
  shift; q="handle=$HANDLE"
  for a in "$@"; do case "$a" in --hard) q="$q&hard=1";; --another) q="$q&another=1";; esac; done
  ans="$(curl -fsS -m 30 "$DESK/next?$q")" || { echo "DESK_REFUSED"; exit 1; }
  printf '%s' "$ans" | python3 -I -c '
import json,sys,os,re
S=sys.argv[1]
d=json.load(sys.stdin)
g=d.get("gap")
# RECORD THE CAPACITY THE DESK REPORTS, whether or not a step came with it. An
# answer can carry `capacity` and `capacity_note` ("You hold 1 of 2 steps. 2
# grows as your proofs are checked."). join.txt says five may be held; the desk
# capped us at TWO, and asking past the cap is what produced the 429s that cost
# eight leases. poll.sh reads this file instead of guessing.
cap=d.get("capacity")
if isinstance(cap,int) and cap>0:
    open(os.path.join(S,"capacity"),"w").write(str(cap))
    note=d.get("capacity_note")
    if note: open(os.path.join(S,"capacity_note"),"w").write(str(note))
if not g:
    print("NO_STEP:", d.get("note") or d.get("error") or "all held"); sys.exit(0)
gid=g["id"]
json.dump(d, open(os.path.join(S,"steps",gid+".json"),"w"), indent=1)
open(os.path.join(S,"live",gid+".lease"),"w").write(d["lease"]["id"])
print("GOT", gid, "cap", cap if cap else "?")
' "$S"
  ;;
beat)   curl -fsS -m 20 -X POST "$DESK/beat?lease=$(cat "$S/live/$2.lease")" >/dev/null && echo OK || echo FAIL ;;
state)  curl -fsS -m 20 -G "$DESK/step" --data-urlencode "gap=$2" ;;
release)
  L="$S/live/$2.lease"; [ -f "$L" ] || { echo "no live lease for $2"; exit 1; }
  q="lease=$(cat "$L")&reason=$3"; [ -n "${4:-}" ] && q="$q&program=$4"
  # Do the bookkeeping BEFORE printing. Writing the reply straight to stdout means a caller
  # that pipes us into `head` closes the pipe mid-reply, we take SIGPIPE, and the `mv` never
  # runs: the desk has released the step while the local lease file still says we hold it.
  # That happened. Capture first, move the file, print last.
  ans="$(curl -sS -m 20 -X POST "$DESK/release?$q")"
  mv "$L" "$S/dead/$2.lease" 2>/dev/null || true
  printf '%s\n' "$ans"
  ;;
*) echo "usage: desk.sh next|beat|state|release" ;;
esac
