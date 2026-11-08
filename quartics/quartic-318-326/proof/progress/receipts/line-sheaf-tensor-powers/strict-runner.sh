#!/usr/bin/env bash
set -euo pipefail
ROOT=/workspace/scratch/2cb21e4e0864
cd "$ROOT"
exec 9>compile-coordination/heavy.lock
flock 9
date -u +ACQUIRED:%FT%TZ
trap 'date -u +RELEASED:%FT%TZ' EXIT
source recovery-geometric-0358/fifth-character-work/env.sh
FIFTH_PATH="$LEAN_PATH"
source recovery-contact-0358/completed-character-work/env.sh
export LEAN_PATH="$LEAN_PATH:$FIFTH_PATH"
export LEAN_PATH="$ROOT/checkpoint-fifth-normal-basis/lib:$ROOT/resumed-completed-addition/official-rank-overlay:$ROOT/resumed-completed-addition:$ROOT/recovery-geometric-0358/fifth-character-work:$LEAN_PATH"
export LEAN_PATH="$ROOT/checkpoint-cocycle-lines-work:$ROOT/recovery-modular-0358/unit-cocycle-subopens-work/lib:$LEAN_PATH"
PRE_HODGE_PATH="$LEAN_PATH"
source "$ROOT/recovery-hodge-0358/fifth-global-ratio-work/env.sh"
export LEAN_PATH="$LEAN_PATH:$PRE_HODGE_PATH"
export LEAN_PATH="$ROOT/resumed-completed-addition:$ROOT/checkpoint-cocycle-refinement-work:$ROOT/checkpoint-cocycle-lines-work:$ROOT/recovery-hodge-0358/intrinsic-tensor-normalization/lib:$ROOT/recovery-hodge-0358/lib:$LEAN_PATH"
export LEAN_PATH="$ROOT/checkpoint-line-class-product-work:$ROOT/checkpoint-line-classes-work:$LEAN_PATH"
export LEAN_PATH="$ROOT/checkpoint-line-class-group-work:$ROOT/checkpoint-line-class-inverse-work:$ROOT/recovery-contact-0358/line-inverse-work/lib:$LEAN_PATH"
cd resumed-completed-addition
for name in "$@";do
 echo "CHECK:$name"
 timeout "${PROOF_TIMEOUT:-120}" lean -M 6144 -j 1 -Ddebug.skipKernelTC=false -o "$name.olean" "$name.lean" 2>&1 | tee "$name.log"
done
