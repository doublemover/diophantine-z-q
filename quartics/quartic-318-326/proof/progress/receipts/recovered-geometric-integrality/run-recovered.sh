#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
export LEAN_PATH="$HERE:${LEAN_PATH:?checkpoint must supply restored dependency path}"
while read -r m; do
  echo "STRICT_REBUILD $m $(date -u +%FT%TZ)"
  timeout 180 lean -Ddebug.skipKernelTC=false -R "$HERE" -o "$HERE/$m.olean" "$HERE/$m.lean"
done < "$HERE/module-order.txt"
timeout 180 lean -Ddebug.skipKernelTC=false -R "$HERE" "$HERE/Audit.lean"
