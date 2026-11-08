#!/usr/bin/env bash
set -uo pipefail
n="$1"; shift
root=/workspace/scratch/2cb21e4e0864
work=$root/recovery-contact-0358/completed-character-work
exec 9>"$root/compile-coordination/heavy.lock"
flock 9
exec >"$work/check-$n.log" 2>&1
echo "ACQUIRED $(date -u +%FT%TZ) contact$n"
trap 'echo "RELEASED $(date -u +%FT%TZ) contact$n"' EXIT
source "$work/env.sh"
export LEAN_PATH="$root/recovery-contact-0358/valuation-official-overlay:$root/checkpoint-global-sign-action/lib:$LEAN_PATH"
cd "$work"
for m in "$@"; do
  echo "START $m $(date -u +%FT%TZ)"
  timeout 120 lean -Ddebug.skipKernelTC=false -j1 -M6144 -o "$m.olean" "$m.lean"
  s=$?; echo "MODULE $m exit=$s $(date -u +%FT%TZ)"
  if [ "$s" != 0 ]; then exit "$s"; fi
done
