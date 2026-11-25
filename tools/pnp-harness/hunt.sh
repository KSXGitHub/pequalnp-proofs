#!/usr/bin/env bash
# Draw a batch, triage each in seconds, KEEP THE BEST and hand back the rest.
#
# Why rank rather than gate: the desk rate-limits to about three declines an hour
# ("no step is free that you have not already looked at and handed back in the last
# hour"), so refusing everything mediocre just buys idleness. Draw the batch, work
# the best of it, release the others at once so other participants can have them.
#
# BUDGET ARITHMETIC, learned by running out: the desk allows about THREE declines an
# hour, and a batch of n costs n-1 of them (we keep one, hand back the rest). So a
# batch of 3 nearly exhausts the hour and leaves no room to decline a contested step.
# Default to 2 - one decline per batch - and raise it only when the budget is fresh.
#
#   usage: hunt.sh [batch]
set -uo pipefail
S="$(cd "$(dirname "$0")" && pwd)"
N="${1:-2}"
declare -a ids=() scores=()
for _ in $(seq 1 "$N"); do
  got="$("$S"/desk.sh next --another 2>&1 | tail -1)"
  case "$got" in GOT\ *) gid="${got#GOT }" ;; *) printf 'desk: %s\n' "$got"; break ;; esac
  st="$("$S"/desk.sh state "$gid" 2>/dev/null | python3 -I -c 'import json,sys
try: print(json.load(sys.stdin).get("state",""))
except Exception: print("")')"
  if [ "$st" = "pr_open" ]; then
    printf 'CONTESTED %s - handing back\n' "$gid"
    "$S"/desk.sh release "$gid" out_of_time >/dev/null 2>&1; continue
  fi
  sc="$("$S"/triage.py "$gid" 2>/dev/null | head -1 | sed -n 's/.*score=\(-\?[0-9]*\).*/\1/p')"
  [ -n "$sc" ] || sc=-999
  printf '  drew %-16s score %s\n' "$gid" "$sc"
  ids+=("$gid"); scores+=("$sc")
done
[ "${#ids[@]}" -gt 0 ] || { echo "nothing drawn"; exit 1; }
bi=0
for i in "${!ids[@]}"; do [ "${scores[$i]}" -gt "${scores[$bi]}" ] && bi=$i; done
for i in "${!ids[@]}"; do
  [ "$i" -eq "$bi" ] && continue
  "$S"/desk.sh release "${ids[$i]}" out_of_time >/dev/null 2>&1
  printf '  released %s\n' "${ids[$i]}"
done
printf '\n>>> BEST OF BATCH: %s (score %s)\n' "${ids[$bi]}" "${scores[$bi]}"
"$S"/triage.py "${ids[$bi]}"
