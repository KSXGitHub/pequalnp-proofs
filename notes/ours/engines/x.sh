#!/usr/bin/env bash
# ONE privileged entry point for every worker job, so the permission surface is a
# single fixed command shape instead of a new one per command.
#
# WHY. Every distinct Bash command string is a distinct thing to approve. Workers
# had been writing their own code with shell heredocs - `cat > f <<EOF` to create
# and, worse, `python3 - <<EOF` with a body that rewrites a source file in place -
# so each step produced a command that had never been seen before. Some matched an
# existing rule and ran silently; the rest raised a box and stopped the worker
# dead until a human answered. The work was never the problem: the shape was.
#
# THE RULE FOR WORKERS, in two lines:
#   1. Create and change .py files with the Write and Edit TOOLS, never with a
#      shell heredoc and never with sed, python -c or a redirect.
#   2. Run them only as `x.sh <job> [args...]`, which is this one shape.
#
# Everything this runs lives in jobs/ as an ordinary editable file, so changing
# what a job does needs no new approval - the same single shape still runs it.
# That is the same arrangement as the git hooks, which are each a short call
# outward to an editable script for exactly this reason.
set -uo pipefail
S="$(cd "$(dirname "$(readlink -f "$0")")" && pwd)"
J="$S/jobs"
case "${1:-}" in
  ""|-h|--help|list)
    echo "usage: x.sh <job> [args...]      jobs live in $J as <job>.py"
    echo
    echo "available:"
    ls -1 "$J" 2>/dev/null | sed -n 's/^\(.*\)\.py$/  \1/p' || echo "  (none yet)"
    echo
    echo "Write or Edit jobs/<job>.py with the file TOOLS, then run it through here."
    exit 0 ;;
esac
job="$1"; shift
# Reject anything that is not a plain job name, so this entry point cannot be
# turned into a way to run an arbitrary path or a shell fragment.
case "$job" in
  *[!a-zA-Z0-9_-]*) echo "x.sh: job names are letters, digits, underscore and hyphen only" >&2; exit 2 ;;
esac
f="$J/$job.py"
[ -f "$f" ] || { echo "x.sh: no such job: $f (write it with the Write tool first)" >&2; exit 2; }
# -I so a planted module beside the data cannot be imported, and a timeout so a
# runaway search cannot hold a slot for ever. PNP_TIMEOUT overrides the default.
exec timeout "${PNP_TIMEOUT:-900}" python3 -I "$f" "$@"
