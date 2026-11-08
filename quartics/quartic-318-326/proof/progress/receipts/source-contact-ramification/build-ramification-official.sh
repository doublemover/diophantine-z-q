#!/usr/bin/env bash
set -euo pipefail
ROOT=/workspace/scratch/2cb21e4e0864
exec 9>"$ROOT/compile-coordination/heavy.lock"
flock 9
echo "ACQUIRED $(date -u +%FT%TZ) contact official ramification dependencies"
trap 'echo "RELEASED $(date -u +%FT%TZ) contact official ramification dependencies"' EXIT
source "$ROOT/recovery-contact-0358/completed-character-work/env.sh"
O="$ROOT/recovery-contact-0358/valuation-official-overlay"
export LEAN_PATH="$O:$LEAN_PATH"
M="$RECOVERED_PROJECT/.lake/packages/mathlib"
cd "$M"
while read -r module; do
  rel="${module//.//}"
  echo "START $module $(date -u +%FT%TZ)"
  timeout 120 lean -Ddebug.skipKernelTC=false -j1 -M6144 -o "$O/$rel.olean" "$rel.lean"
  echo "MODULE $module exit=0 $(date -u +%FT%TZ)"
done < "$O/ramification-official-order.txt"
echo OFFICIAL_RAMIFICATION_DEPENDENCIES_PASS
