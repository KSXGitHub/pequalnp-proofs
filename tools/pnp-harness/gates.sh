#!/usr/bin/env bash
# Every harness gate, in one command that EXITS NON-ZERO when anything fails.
#
# This exists because I pushed with failing gates four times in one session. The
# cause was always the same shape: running a gate inside a pipeline ending in
# `tail`, which discards the tool's exit code, so `set -e` saw success. Call this
# before every push and read its last line.
set -uo pipefail
cd "$(dirname "$0")" || exit 2
export PATH="$HOME/.local/bin:$PATH"
fail=0
run() {
  local name="$1"; shift
  if "$@" >/tmp/gate.$$ 2>&1; then
    printf '  ok    %s\n' "$name"
  else
    printf '  FAIL  %s\n' "$name"; sed 's/^/        /' /tmp/gate.$$ | tail -15; fail=1
  fi
  rm -f /tmp/gate.$$
}
run "unittest"     python3 -m unittest discover -s tests -q
run "mypy strict"  python3 -m mypy --strict lib read_verdict.py tests triage.py adapt.py reduce.py search
run "ruff check"   ruff check .
run "ruff format"  ruff format --check .
for f in *.sh; do [ -e "$f" ] && run "shellcheck $f" shellcheck -S warning "$f"; done
if [ "$fail" -eq 0 ]; then echo "ALL GATES GREEN"; else echo "GATES FAILED"; fi
exit "$fail"
