#!/usr/bin/env bash
# Caller supplies the exact verified predecessor/upstream LEAN_PATH.
# No existing project artifact is taken as an independent proof certificate.
set -euo pipefail
PACKET=$(cd "$(dirname "$0")" && pwd)
: "${LEAN_PATH:?Set LEAN_PATH to the verified pinned predecessor/upstream libraries}"
: "${OUT:?Set OUT to a new output directory}"
test ! -e "$OUT"
mkdir -p "$OUT/lib" "$OUT/logs"
OUT=$(cd "$OUT" && pwd)
cd "$PACKET"
sha256sum --check SOURCE_SHA256SUMS
export LEAN_PATH="$OUT/lib:$LEAN_PATH"
while read -r module; do
  lean -j1 -M 6144 -Ddebug.skipKernelTC=false -R "$PACKET" \
    -o "$OUT/lib/$module.olean" "$PACKET/$module.lean" > "$OUT/logs/$module.log" 2>&1
done < MODULE_ORDER.txt
lean -j1 -M 6144 -Ddebug.skipKernelTC=false -R "$PACKET/validation" \
  "$PACKET/validation/ExperimentAudit.lean" > "$OUT/logs/ExperimentAudit.log" 2>&1
cat "$OUT/logs/ExperimentAudit.log"
