#!/usr/bin/env bash
set -euo pipefail
ROOT=/workspace/scratch/2cb21e4e0864
HERE="$ROOT/recovery-contact-0358"
exec 9>"$ROOT/compile-coordination/heavy.lock"
flock 9
printf 'ACQUIRED=%s\n' "$(date -u +%FT%TZ)" | tee "$HERE/replay-status.log"
trap 'printf "RELEASED=%s\n" "$(date -u +%FT%TZ)" | tee -a "$HERE/replay-status.log"' EXIT
python3 -c 'import json; assert json.load(open("/workspace/scratch/2cb21e4e0864/recovery-toolchain/published-recovery-result.json"))["status"] == "PASS"'
source "$ROOT/recovery-toolchain/proof-environment.sh"
mkdir -p "$HERE/build"
export LEAN_PATH="$HERE/build:$LEAN_PATH"
cd "$RECOVERED_PROJECT"
while IFS= read -r f; do
  m=$(basename "$f" .lean)
  printf 'MODULE=%s\n' "$m"
  timeout 180s lean -Ddebug.skipKernelTC=false -R "$(dirname "$HERE/$f")" -o "$HERE/build/$m.olean" "$HERE/$f"
done < "$HERE/module-order.txt"
timeout 180s lean -Ddebug.skipKernelTC=false -R "$HERE" "$HERE/Audit.lean"
