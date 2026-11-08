#!/usr/bin/env bash
set -euo pipefail
ROOT=/workspace/scratch/2cb21e4e0864
cd "$ROOT"
exec 9>compile-coordination/heavy.lock
flock 9
date -u +ACQUIRED:%FT%TZ
trap 'date -u +RELEASED:%FT%TZ' EXIT
source recovery-toolchain/proof-environment.sh
export LEAN_PATH="$ROOT/resumed-completed-addition:$LEAN_PATH"
cd resumed-completed-addition
for name in "$@"; do
  echo "CHECK:$name"
  timeout 120 lean -M 6144 -j 1 -Ddebug.skipKernelTC=false -o "$name.olean" "$name.lean" 2>&1 | tee "$name.log"
done
