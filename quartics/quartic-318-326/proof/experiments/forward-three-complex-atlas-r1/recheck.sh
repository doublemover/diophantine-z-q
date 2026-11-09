#!/bin/bash
set -euo pipefail
source /workspace/shared/lean-tooling/env.sh
p="$QUARTIC_PROOF_ROOT/quartics/quartic-318-326/proof/experiments/forward-three-complex-atlas-r1"
r=/workspace/shared/analytic-complex-atlas-r1
out="$r/final-lib"
mkdir -p "$out" "$p/checks"
export LEAN_PATH="$out:$LEAN_PATH"
for m in $(python -c 'import json;print(" ".join(json.load(open("/workspace/shared/analytic-complex-atlas-r1/order.json"))))') ExperimentAudit;do
 flock /workspace/shared/lean-tooling/lean-check.lock bash -c 'echo LEAN_CHECK_LOCK_ACQUIRED $(date -u +%FT%TZ) "$3"; timeout 180 lean -j1 -M6144 -Ddebug.skipKernelTC=false -R "$1" -o "$2/$3.olean" "$1/$3.lean"' _ "$p" "$out" "$m" > "$p/checks/$m.log" 2>&1
 cat "$p/checks/$m.log"
 sleep 1
done
