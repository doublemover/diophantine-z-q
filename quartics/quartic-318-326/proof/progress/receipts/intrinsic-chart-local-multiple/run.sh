#!/bin/bash
set -uo pipefail
root=/workspace/scratch/2cb21e4e0864
work=$root/recovery-contact-0358/chart-local-multiple-work
n="$1";shift
exec 9>"$root/compile-coordination/heavy.lock";flock 9
exec >"$work/check-$n.log" 2>&1
echo "ACQUIRED $(date -u +%FT%TZ) chart-local-multiple$n"
trap 'echo "RELEASED $(date -u +%FT%TZ) chart-local-multiple$n"' EXIT
source "$work/env.sh"
cd "$work"
for m in "$@"; do
 echo "START $m $(date -u +%FT%TZ)"
 timeout "${BOUND_SECONDS:-120}" lean -Ddebug.skipKernelTC=false -j1 -M6144 -o "lib/$m.olean" "$m.lean"
 s=$?;echo "MODULE $m exit=$s $(date -u +%FT%TZ)"
 if [ "$s" != 0 ]; then exit "$s";fi
done
