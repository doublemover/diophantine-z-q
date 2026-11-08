#!/usr/bin/env bash
set -euo pipefail
root=/workspace/scratch/2cb21e4e0864
work=$root/recovery-modular-0358/global-differential-scalars-work
source "$root/recovery-hodge-0358/character-differential-work/env.sh"
export LEAN_PATH="$work/lib:$LEAN_PATH"
exec 9>"$root/compile-coordination/heavy.lock"
flock 9
printf 'ACQUIRED %s\n' "$(date -u +%FT%TZ)"
trap 'printf "RELEASED %s\n" "$(date -u +%FT%TZ)"' EXIT
cd "$work"
for m in "$@"; do
 printf 'CHECK %s\n' "$m"
 timeout -k 5 90 lean -Ddebug.skipKernelTC=false -j1 -M 6144 -o "$work/lib/$m.olean" "$work/$m.lean"
 printf 'RESULT %s 0\n' "$m"
done
