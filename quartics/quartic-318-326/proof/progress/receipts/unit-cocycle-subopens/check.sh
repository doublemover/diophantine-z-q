#!/usr/bin/env bash
set -euo pipefail
root=/workspace/scratch/2cb21e4e0864
work=$root/recovery-modular-0358/unit-cocycle-subopens-work
source "$root/recovery-toolchain/proof-environment.sh"
export LEAN_PATH="$work/lib:$root/checkpoint-unit-cocycles/lib:$LEAN_PATH"
exec 9>"$root/compile-coordination/heavy.lock"
flock 9
printf 'ACQUIRED %s\n' "$(date -u +%FT%TZ)"
trap 'printf "RELEASED %s\n" "$(date -u +%FT%TZ)"' EXIT
cd "$work"
for m in "$@"; do
 printf 'CHECK %s\n' "$m"
 timeout -k 5 60 lean -Ddebug.skipKernelTC=false -j1 -M 4096 -o "$work/lib/$m.olean" "$work/$m.lean"
 printf 'RESULT %s 0\n' "$m"
done
