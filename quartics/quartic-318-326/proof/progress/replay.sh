#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
cd "$HERE"
python3 verify_manifest.py
mkdir -p .lake/build/lib/lean
export LEAN_PATH="$HERE/.lake/build/lib/lean:${LEAN_PATH:-}"
if [[ ${1:-} != --audit-only ]]; then
  while read -r module; do
    printf 'KERNEL_CHECK %s\n' "$module"
    lake env lean -R "$HERE" -Ddebug.skipKernelTC=false "$module.lean" -o ".lake/build/lib/lean/$module.olean"
  done < <(python3 -c 'import json;print("\n".join(json.load(open("module-order.json"))))')
fi
lake env lean -R "$HERE" -Ddebug.skipKernelTC=false CheckpointAudit.lean
