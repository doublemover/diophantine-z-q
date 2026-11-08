#!/usr/bin/env bash
set -euo pipefail
ROOT=/workspace/scratch/2cb21e4e0864
HERE="$ROOT/recovery-modular-0358"
PROGRESS="$ROOT/diophantine-z-q/quartics/quartic-318-326/proof/progress"
source "$ROOT/recovery-toolchain/proof-environment.sh"
cd "$HERE"
export LEAN_PATH="$HERE${LEAN_PATH:+:$LEAN_PATH}"
modules=(UniformPeriodBounds318 ThirdPeriodSummands318 ThirdPeriodNormalConvergence318 ThirdArithmeticHolomorphic318 ModularArithmeticCoordinates318 ModularCoordinateProper318 ArithmeticPointTopology318)
result=0
declare -A failed
for m in "${modules[@]}"; do
  blocked=0
  while read -r dep; do
    if [[ -f "$HERE/$dep.lean" && ( ${failed[$dep]:-0} -eq 1 || ! -f "$HERE/$dep.olean" || "$HERE/$dep.lean" -nt "$HERE/$dep.olean" ) ]]; then
      echo "SKIP $m: predecessor $dep has no current successful build"
      blocked=1
    fi
  done < <(sed -n -E 's/^(public )?import ([A-Za-z0-9_.]+).*$/\2/p' "$HERE/$m.lean")
  if [[ $blocked -eq 1 ]]; then result=1; failed[$m]=1; continue; fi
  echo "START $m $(date -u +%FT%TZ)"
  if ! lean -Ddebug.skipKernelTC=false -o "$HERE/$m.olean" "$HERE/$m.lean" > "$HERE/$m.log" 2>&1; then
    echo "FAIL $m $(date -u +%FT%TZ)"; cat "$HERE/$m.log"; result=1; failed[$m]=1; continue
  fi
  echo "PASS $m $(date -u +%FT%TZ)"
done

if [[ "$result" -eq 0 ]]; then
  lean -Ddebug.skipKernelTC=false "$HERE/RecoveryCoreAudit.lean" > "$HERE/RecoveryCoreAudit.log" 2>&1 || { cat "$HERE/RecoveryCoreAudit.log"; exit 1; }
  cat "$HERE/RecoveryCoreAudit.log"
fi
exit "$result"
