#!/usr/bin/env bash
set -euo pipefail
ROOT=/workspace/scratch/2cb21e4e0864
exec 9>"$ROOT/compile-coordination/heavy.lock"; flock 9
echo "ACQUIRED $(date -u +%FT%TZ) contact120"
trap 'echo "RELEASED $(date -u +%FT%TZ) contact120"' EXIT
source "$ROOT/recovery-contact-0358/completed-character-work/env.sh"
export LEAN_PATH="$ROOT/recovery-contact-0358/valuation-official-overlay:$ROOT/checkpoint-global-sign-action/lib:$LEAN_PATH"
cd "$ROOT/recovery-contact-0358/completed-character-work"
for module in SourceContactRamification318; do
  echo "START $module $(date -u +%FT%TZ)"
  timeout 120 lean -Ddebug.skipKernelTC=false -j1 -M6144 -o "$module.olean" "$module.lean"
  echo "MODULE $module exit=0 $(date -u +%FT%TZ)"
done
