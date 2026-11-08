#!/usr/bin/env bash
set -euo pipefail
ROOT=/workspace/scratch/2cb21e4e0864
cd "$ROOT"
exec 9>compile-coordination/heavy.lock
flock 9
date -u +ACQUIRED:%FT%TZ
trap 'date -u +RELEASED:%FT%TZ' EXIT
source recovery-geometric-0358/fifth-character-work/env.sh
export LEAN_PATH="$ROOT/checkpoint-line-class-product-work:$ROOT/checkpoint-cocycle-refinement-work:$ROOT/checkpoint-line-classes-work:$ROOT/checkpoint-cocycle-lines-work:$ROOT/resumed-completed-addition:$ROOT/checkpoint-open-affine-pushforward:$LEAN_PATH"
cd checkpoint-line-class-product-work
for n in "$@";do
 echo "CHECK:$n"
 timeout 60 lean -M 6144 -j 1 -Ddebug.skipKernelTC=false -o "$n.olean" "$n.lean"
done
