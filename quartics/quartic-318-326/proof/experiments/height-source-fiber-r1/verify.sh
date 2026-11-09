#!/usr/bin/env bash
set -euo pipefail
packet=$(cd "$(dirname "$0")" && pwd)
out=${1:?Provide an absolute empty output directory}
case "$out" in /*) ;; *) echo 'Output path must be absolute' >&2; exit 2;; esac
mkdir "$out"
export LEAN_PATH="$out:${LEAN_PATH:?Set the verified predecessor and pinned upstream LEAN_PATH}"
for module in RationalFourRootFiber318 FourRootPointTorsor318 RationalContactPoint318; do
  lean -j1 -M 6144 -Ddebug.skipKernelTC=false -R "$packet" \
    -o "$out/$module.olean" "$packet/$module.lean" | tee "$out/$module.log"
done
lean -j1 -M 6144 -Ddebug.skipKernelTC=false -R "$packet/verification" \
  "$packet/verification/ExperimentAudit.lean" | tee "$out/ExperimentAudit.log"
grep -q 'EXPERIMENT_AUDIT_PASS declarations=43 modules=3' "$out/ExperimentAudit.log"
