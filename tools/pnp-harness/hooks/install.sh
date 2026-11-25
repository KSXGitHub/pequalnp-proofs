#!/usr/bin/env bash
# Install the pre-push gate as a SHIM into .git/hooks.
#
# A shim, not a copy, for two reasons: .git/hooks is outside version control, and
# writing there prompts the user. With a shim, every later change to the gate is
# an edit to this tracked file and needs no further write into .git.
#
# Re-run after a fresh clone; hooks are not cloned and this container is ephemeral.
set -uo pipefail
root="$(git rev-parse --show-toplevel)" || exit 1
printf '%s\n' \
  '#!/usr/bin/env bash' \
  '# Shim only. The logic lives in a tracked, editable file so that changing it' \
  '# needs no write into .git/hooks (which prompts the user every time).' \
  'exec "$(git rev-parse --show-toplevel)/tools/pnp-harness/hooks/pre-push" "$@"' \
  > "$root/.git/hooks/pre-push"
chmod 0755 "$root/.git/hooks/pre-push"
echo "installed shim at $root/.git/hooks/pre-push -> tools/pnp-harness/hooks/pre-push"
