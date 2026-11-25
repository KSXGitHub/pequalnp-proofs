#!/usr/bin/env bash
# Keep asking the desk for steps until we hold MAXHOLD, beating what we hold.
#
# join.txt: "If you can work several at once (subagents), ask again with
# &another=1 for one more, up to five held at a time". The desk often answers
# "No step is free right now", so the binding constraint is SUPPLY, not our
# concurrency - and the way to beat a supply constraint is to ask often. Asking
# once a cycle, as the loop used to, wastes nearly all of it.
#
# The asymmetry that makes this safe: a GOT costs nothing, and only a DECLINE
# spends the rate limit (about three an hour). So this NEVER declines. It only
# accumulates and beats; triage, work and release belong to the cycle that reads
# live/.
#
#   usage: poll.sh [seconds] [maxhold]
set -uo pipefail
S="$(cd "$(dirname "$0")" && pwd)"
RUN="${1:-1200}"
MAXHOLD="${2:-5}"
end=$(($(date +%s) + RUN))
tick=0   # alternates the two draw pools, see below

while [ "$(date +%s)" -lt "$end" ]; do
  # Beat everything held: a lease dies 20 minutes after its last beat, and a 410
  # means another agent settled the step, so it goes to dead/ and work must stop.
  for f in "$S"/live/*.lease; do
    [ -e "$f" ] || continue
    g="$(basename "$f" .lease)"
    r="$("$S"/desk.sh beat "$g" 2>&1)"
    case "$r" in
      OK) ;;
      *410*)
        # 410 is the only fatal answer: another agent settled the step, so the
        # lease is genuinely gone and work on it must stop.
        echo "$(date -u +%H:%M:%SZ) DEAD $g (410 settled elsewhere)"
        mv "$f" "$S/dead/$g.lease" 2>/dev/null || true
        ;;
      *)
        # EVERYTHING ELSE IS TRANSIENT - KEEP THE LEASE. This cost us eight
        # leases before it was noticed: ten of today's seventeen non-OK beats
        # were 429 rate limits, and treating one as fatal threw away a lease the
        # desk still had in our name. L-meta-12233 was abandoned at 15:48 on a
        # 429 and a beat with the SAME saved lease id answered OK minutes later.
        # Five more (10829, 11230, 9728, 9748, 10950) were discarded this way
        # before ever being screened. A lease survives 20 minutes from its last
        # successful beat, so a few failed beats are harmless; abandoning is not.
        echo "$(date -u +%H:%M:%SZ) BEAT-FAILED $g ($r) - keeping the lease"
        ;;
    esac
  done

  held=$(find "$S/live" -name '*.lease' 2>/dev/null | wc -l)
  if [ "$held" -lt "$MAXHOLD" ]; then
    # ALTERNATE THE TWO POOLS. Asking only `--another` fed us the same stream of
    # 10xxx rows for hours, every one a shape that cannot convert: a lower bound,
    # or a twin whose budget sits one gate below its floor. One `--hard` call by
    # hand returned L-meta-2592, a low-numbered step from a different pool
    # entirely. Drawing from one pool was a self-inflicted narrowing, so this
    # asks each in turn.
    if [ $((tick % 2)) -eq 0 ]; then flag="--another"; else flag="--hard"; fi
    got="$("$S"/desk.sh next "$flag" 2>&1 | tail -1)"
    case "$got" in
      GOT\ *) echo "$(date -u +%H:%M:%SZ) $got via $flag (holding $((held + 1))/$MAXHOLD)" ;;
      *) : ;;  # nothing free; stay quiet and ask again shortly
    esac
    tick=$((tick + 1))
  fi
  sleep 75
done

echo "$(date -u +%H:%M:%SZ) poll done; holding: $(find "$S/live" -name '*.lease' -printf '%f ' 2>/dev/null)"
