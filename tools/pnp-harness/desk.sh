#!/usr/bin/env bash
# Desk client for pequalnp.com. State lives beside this script.
set -uo pipefail
DESK=https://pequalnp.com/desk
# Resolve the SYMLINK before taking the directory. $P/<script>.sh are symlinks into this
# directory, and bash sets $0 to the path used to invoke the script, not its target - so a
# plain `dirname "$0"` gave the SCRATCHPAD for every symlinked call and this directory for
# every direct one. That split the harness state in two: live/, steps/, dead/ and done/
# existed twice, the poller beat only its own copy, and leases drawn by hand expired
# unbeaten and unlogged while 166 step statements sat in the other copy unnoticed.
S="$(cd "$(dirname "$(readlink -f "$0")")" && pwd)"
HANDLE=KSXGitHub
case "${1:-}" in
next)
  # THE SELECTORS THE DESK ACCEPTS. This used to pass only --hard and --another,
  # and in particular it never sent `value=1` - which tools/pnp.sh sends on EVERY
  # call, with the comment "value=1: this script can take a value step". So for
  # the whole first window we were never offered a VALUE step at all, and never
  # knew the category existed. A value step asks for the LEAST k for which a
  # template holds, which means it always has a determinate answer, unlike the
  # FIND rows the desk keeps posting one unit below the star-cover floor.
  #   --value          be offered value steps too
  #   --kind  <k>      prove | refute | search | cut | value
  #   --level <l>      warmup | solid | hard | open
  shift; q="handle=$HANDLE"
  while [ $# -gt 0 ]; do
    case "$1" in
      --hard) q="$q&hard=1" ;;
      --another) q="$q&another=1" ;;
      --value) q="$q&value=1" ;;
      # CLAIM A STEP WE HAVE ALREADY PROVED, EVEN WHILE SOMEONE ELSE HOLDS IT.
      # pnp.sh: "--proof-of leases a step you already hold a checked proof of,
      # even while another agent holds it." That is the answer to the race on the
      # few winnable rows: every AT-FLOOR step was leased by a competitor when we
      # found it, so the order is BUILD THEN CLAIM, not claim then build. Only
      # use it with a proof that has actually been checked.
      --proof-of)
        case "${2:-}" in
          L-[a-z]*-[0-9]*) q="$q&gap=$2&have=proof"; shift ;;
          *) echo "--proof-of needs a step id, e.g. --proof-of L-meta-4873" >&2; exit 2 ;;
        esac ;;
      --kind|--level)
        case "${2:-}" in
          [a-z][a-z]*)
            q="$q&${1#--}=$2"
            # `kind=value` WITHOUT `value=1` IS REFUSED, and the refusal reads like a
            # stale-clone problem rather than a malformed request: "Value steps need a
            # newer tools/pnp.sh: update your clone ... a request by hand adds &value=1".
            # Our clone was current (we had just merged upstream), so the message sent me
            # looking for the wrong fault. The desk wants BOTH parameters, so add the
            # second one here rather than relying on every caller to remember it.
            case "$1=$2" in --kind=value) case "$q" in *"&value=1"*) : ;; *) q="$q&value=1" ;; esac ;; esac
            shift ;;
          *) echo "$1 needs a word, e.g. $1 value" >&2; exit 2 ;;
        esac ;;
      *) echo "unknown: $1" >&2; exit 2 ;;
    esac
    shift
  done
  ans="$(curl -fsS -m 30 "$DESK/next?$q")" || { echo "DESK_REFUSED"; exit 1; }
  printf '%s' "$ans" | python3 -I -c '
import json,sys,os,re
S=sys.argv[1]
# RECREATE THE STATE DIRECTORIES FIRST. They are untracked, and submit.py cuts
# its artifact branch with `git checkout -B <gid> upstream/main`, which strips
# tools/pnp-harness/ from the working tree; returning to main restores only the
# TRACKED files. That deleted leanpath.txt once (check.sh now regenerates it)
# and this time it took live/, dead/, steps/ and done/ with it.
#
# The failure was SILENT and expensive: with steps/ gone this open() raised
# FileNotFoundError, poll.sh read only the last stdout line, saw no "GOT", and
# said nothing - so for twenty minutes the poller leased steps from the desk,
# threw the lease id away, never beat them, and let them expire unscreened.
# With live/ gone the glob in the beat loop matched nothing, so the two steps we
# did hold (L-meta-9754, 1189 points, and L-meta-1988) expired without one line
# of warning. An empty live/ now means "we hold nothing", never "state is lost".
#
# NO APOSTROPHES BELOW THIS POINT, OR ABOVE IT EITHER: this whole block is the
# argument of `python3 -I -c '...'`, inside single quotes, so one apostrophe in
# a comment ends the string and bash then tries to parse Python. That is what
# the first version of this comment did.
for _d in ("steps","live","dead","done"):
    os.makedirs(os.path.join(S,_d),exist_ok=True)
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
  # MOVE THE LEASE ONLY IF THE DESK ACTUALLY RELEASED IT. This used to mv
  # unconditionally, so a REFUSED release still cleared our lease file. Asking
  # `exhausted` for a lease with no shard range is answered
  #   {"error": "exhausted is for a range of a sharded search; this lease has none"}
  # and the row then stayed leased at the desk while live/ said we held nothing:
  # unbeatable, unreleasable, and invisible to triage until it expired. That is
  # the same state desync that cost us rows before. Recovery was to copy the
  # lease back out of dead/ and release again, which should never be necessary.
  case "$ans" in
    *'"released"'*)
      mv "$L" "$S/dead/$2.lease" 2>/dev/null || true ;;
    *)
      echo "RELEASE REFUSED - the lease is KEPT in live/ so it can still be beaten and released" >&2 ;;
  esac
  printf '%s\n' "$ans"
  ;;
*) echo "usage: desk.sh next|beat|state|release" ;;
esac
