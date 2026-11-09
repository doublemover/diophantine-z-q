#!/usr/bin/env bash
set -euo pipefail
source /workspace/shared/lean-tooling/env.sh
p=quartics/quartic-318-326/proof/experiments/forward-real-oval-group-r1
out="$PWD/build/forward-real-oval-group-r1"
export LEAN_PATH="$out:$PWD/build/forward-real-oval-cover-r1:$PWD/build/forward-real-guard-ambient-r1:$PWD/build/forward-real-guard-selection-r1:$PWD/build/forward-coherent-multiple-charts-r1:$PWD/build/forward-real-guard-witness-r1:$LEAN_PATH"
mkdir -p "$out" "$p/validation"
for m in RealQuarticAssociativityPolynomial318 RealQuarticSumU318 RealQuarticSumAnalytic318 RealQuarticAssociativity318 RealQuarticGroup318 RealQuarticTopologicalGroup318; do
  lean-checked -R "$p" -o "$out/$m.olean" "$p/$m.lean" > "$p/validation/$m.log" 2>&1
done
lean-checked -R "$p" "$p/AuditRealOvalGroup.lean" > "$p/validation/AuditRealOvalGroup.log" 2>&1
