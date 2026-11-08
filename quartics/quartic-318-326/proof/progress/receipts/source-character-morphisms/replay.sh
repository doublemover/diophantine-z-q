#!/usr/bin/env bash
set -euo pipefail
ROOT=/workspace/scratch/2cb21e4e0864
REC="$ROOT/recovery-contact-0358"
HERE="$REC/source-character-work"
exec 9>"$ROOT/compile-coordination/heavy.lock"
flock 9
printf 'ACQUIRED=%s\n' "$(date -u +%FT%TZ)" | tee "$HERE/replay-status.log"
trap 'printf "RELEASED=%s\n" "$(date -u +%FT%TZ)" | tee -a "$HERE/replay-status.log"' EXIT
python3 -c 'import json; assert json.load(open("/workspace/scratch/2cb21e4e0864/recovery-toolchain/published-recovery-result.json"))["status"] == "PASS"'
source "$ROOT/recovery-toolchain/proof-environment.sh"
mkdir -p "$HERE/build"
rm -f "$HERE"/build/SourceCharacter{Algebra,Affine,Global}318.olean
export LEAN_PATH="$HERE/build:$REC/build:$LEAN_PATH"
cd "$RECOVERED_PROJECT"
for m in SourceCharacterAlgebra318 SourceCharacterAffine318 SourceCharacterGlobal318; do
  printf 'MODULE=%s\n' "$m"
  timeout 180s lean -Ddebug.skipKernelTC=false -R "$HERE" -o "$HERE/build/$m.olean" "$HERE/$m.lean"
done
timeout 180s lean -Ddebug.skipKernelTC=false "$HERE/Audit.lean"
