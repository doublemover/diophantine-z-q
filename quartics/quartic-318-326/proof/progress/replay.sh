#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
cd "$HERE"
python3 verify_manifest.py
mkdir -p .lake/build/lib/lean
export LEAN_PATH="$HERE/.lake/build/lib/lean:${LEAN_PATH:-}"
if [[ ${1:-} != --audit-only ]]; then
  MATHLIB=.lake/packages/mathlib
  for OFFICIAL in Mathlib/RingTheory/Smooth/IntegralClosure \
    Mathlib/CategoryTheory/Limits/Final/Type \
    Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree \
    Mathlib/Algebra/Category/ModuleCat/Differentials/Basic \
    Mathlib/Algebra/Category/ModuleCat/Presheaf/OfCommRing \
    Mathlib/Algebra/Category/ModuleCat/Differentials/Presheaf; do
    if [[ ! -f "$MATHLIB/.lake/build/lib/lean/$OFFICIAL.olean" ]]; then
      mkdir -p "$MATHLIB/.lake/build/lib/lean/$(dirname "$OFFICIAL")"
      lake env lean -R "$MATHLIB" -Ddebug.skipKernelTC=false "$MATHLIB/$OFFICIAL.lean" \
        -o "$MATHLIB/.lake/build/lib/lean/$OFFICIAL.olean"
    fi
  done
  while read -r module; do
    printf 'KERNEL_CHECK %s\n' "$module"
    lake env lean -R "$HERE" -Ddebug.skipKernelTC=false "$module.lean" -o ".lake/build/lib/lean/$module.olean"
  done < <(python3 -c 'import json;print("\n".join(json.load(open("module-order.json"))))')
fi
lake env lean -R "$HERE" -Ddebug.skipKernelTC=false CheckpointAudit.lean
