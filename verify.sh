#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd -P)"
export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH"
export PYTHONDONTWRITEBYTECODE=1
python3 -c 'import sys; assert sys.version_info >= (3,11), "Python 3.11+ is required"'
if [[ "${1:-}" == "--check-only" ]]; then
  exec python3 "$ROOT/scripts/verify_github.py" "$@"
fi
if ! command -v elan >/dev/null 2>&1; then
  INSTALLER="$(mktemp)"
  trap 'rm -f "$INSTALLER"' EXIT
  curl --fail --show-error --location --proto '=https' --tlsv1.2 \
    https://elan.lean-lang.org/elan-init.sh --output "$INSTALLER"
  sh "$INSTALLER" -y --default-toolchain none
  rm -f "$INSTALLER"
  trap - EXIT
fi
elan toolchain install leanprover/lean4:v4.19.0
exec python3 "$ROOT/scripts/verify_github.py" "$@"
