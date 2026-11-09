#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
# Supply a pinned Lean 4.35.0 environment and a source/dependency-verified
# progress snapshot in LEAN_PATH. This script never downloads dependencies.
OUT=${1:-"$HERE/replay-lib"}
mkdir -p "$OUT"
export LEAN_PATH="$OUT:${LEAN_PATH:-}"
lean --version | grep -F 'version 4.35.0'
while IFS= read -r module; do
  printf 'KERNEL_CHECK %s\n' "$module"
  lean -j1 -M6144 -Ddebug.skipKernelTC=false -R "$HERE" \
    "$HERE/$module.lean" -o "$OUT/$module.olean"
  printf 'STRICT_PASS %s\n' "$module"
done < "$HERE/MODULE_ORDER.txt"
lean -j1 -M6144 -Ddebug.skipKernelTC=false -R "$HERE" "$HERE/Audit.lean"
