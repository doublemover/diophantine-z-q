#!/usr/bin/env bash
set -euo pipefail
packet=$(cd "$(dirname "$0")" && pwd)
out=${1:?Provide an absolute empty output directory}
case "$out" in /*) ;; *) echo 'Output path must be absolute' >&2; exit 2;; esac
mkdir "$out"
export LEAN_PATH="$out:${LEAN_PATH:?Source the pinned verified compiler environment first}"
while IFS= read -r module; do
  lean-checked -R "$packet" -o "$out/$module.olean" "$packet/$module.lean" 2>&1 | tee "$out/$module.log"
  sleep 1
done < "$packet/verification/MODULE_ORDER.txt"
lean-checked -R "$packet/verification" "$packet/verification/ExperimentAudit.lean" 2>&1 | tee "$out/ExperimentAudit.log"
grep -q 'EXPERIMENT_AUDIT_PASS declarations=.* modules=9' "$out/ExperimentAudit.log"
