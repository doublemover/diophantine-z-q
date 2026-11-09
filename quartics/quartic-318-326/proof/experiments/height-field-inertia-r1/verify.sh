#!/usr/bin/env bash
set -euo pipefail
packet=$(cd "$(dirname "$0")" && pwd)
out=${1:?Provide an absolute empty output directory}
case "$out" in /*) ;; *) echo 'Output path must be absolute' >&2; exit 2;; esac
mkdir "$out"
export LEAN_PATH="$out:${LEAN_PATH:?Set the verified predecessor and pinned upstream LEAN_PATH}"
checker=${LEAN_CHECKER:-lean}
for module in RationalFourRootFiber318 FourRootPointTorsor318 RationalContactPoint318 FourRootPointUniversal318 RationalFourRootSplitting318 IntegralSquareInertia318 RationalFourRootInertia318 ContactIntegerRadicands318 ContactFieldRamification318; do
  "$checker" -j1 -M 6144 -Ddebug.skipKernelTC=false -R "$packet" \
    -o "$out/$module.olean" "$packet/$module.lean" 2>&1 | tee "$out/$module.log"
done
"$checker" -j1 -M 6144 -Ddebug.skipKernelTC=false -R "$packet/verification" \
  "$packet/verification/ExperimentAudit.lean" 2>&1 | tee "$out/ExperimentAudit.log"
grep -Eq 'EXPERIMENT_AUDIT_PASS declarations=[0-9]+ modules=9' "$out/ExperimentAudit.log"
