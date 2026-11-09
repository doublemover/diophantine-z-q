#!/bin/bash
set -euo pipefail
source /workspace/shared/lean-tooling/env.sh
r=/workspace/shared/height-integer-generic-fiber-review-analytic
p="$QUARTIC_PROOF_ROOT/quartics/quartic-318-326/proof/experiments/height-integer-generic-fiber-r1"
export LEAN_PATH="$r/lib:$LEAN_PATH"
for m in $(python -c 'import json,sys;print(" ".join(json.load(open(sys.argv[1]))["order"]))' "$p/intake.json") ReviewAudit;do
 flock /workspace/shared/lean-tooling/lean-check.lock bash -c 'echo LEAN_CHECK_LOCK_ACQUIRED $(date -u +%FT%TZ) "$3"; timeout 180 lean -j1 -M6144 -Ddebug.skipKernelTC=false -R "$1" -o "$2/$3.olean" "$1/$3.lean"' _ "$r/sources" "$r/lib" "$m" > "$p/independent-review-analytic/logs/$m.log" 2>&1
 cat "$p/independent-review-analytic/logs/$m.log"
done
