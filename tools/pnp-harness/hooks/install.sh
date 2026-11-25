#!/usr/bin/env bash
# Install the pre-push gate hook into this checkout. Hooks are not version
# controlled, and this container is ephemeral, so re-run after a fresh clone.
set -uo pipefail
root="$(git rev-parse --show-toplevel)" || exit 1
install -m 0755 "$root/tools/pnp-harness/hooks/pre-push" "$root/.git/hooks/pre-push"
echo "installed $root/.git/hooks/pre-push"
