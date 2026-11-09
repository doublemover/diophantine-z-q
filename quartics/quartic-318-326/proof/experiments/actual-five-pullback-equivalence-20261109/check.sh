#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
# Supply pinned Lean 4.35.0 and the verified baseline in LEAN_PATH.
# The accepted basis source and object bytes are checked before import.
# No dependency installation occurs here.
OUT=${1:-"$HERE/replay-lib"}
BASIS="$HERE/../recovered-five-basis-20261109"
BASIS_LIB=${BASIS_LIB:-"$BASIS/replay-lib"}
mkdir -p "$OUT"
python - "$BASIS" "$BASIS_LIB" <<'PY'
import hashlib
import json
from pathlib import Path
import sys
basis, lib = map(Path, sys.argv[1:])
receipt = json.loads((basis / 'receipt.json').read_text())
intake = json.loads((basis / 'intake.json').read_text())
def verify(path, expected):
    if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        raise SystemExit('Accepted basis byte mismatch: ' + str(path))
for name, row in intake['files'].items():
    verify(basis / name, row['sha256'])
count = 0
for module, suffixes in receipt['compiled_object_hashes'].items():
    for suffix, expected in suffixes.items():
        verify(lib / (module + suffix), expected)
        count += 1
print('VERIFY_ACCEPTED_BASIS_PASS sources=' + str(len(intake['files'])) + ' objects=' + str(count))
PY
export LEAN_PATH="$OUT:$BASIS_LIB:${LEAN_PATH:-}"
lean --version | grep -F 'version 4.35.0'
while IFS= read -r module; do
  printf 'KERNEL_CHECK %s\n' "$module"
  lean -j1 -M6144 -Ddebug.skipKernelTC=false -R "$HERE" \
    "$HERE/$module.lean" -o "$OUT/$module.olean"
  printf 'STRICT_PASS %s\n' "$module"
done < "$HERE/MODULE_ORDER.txt"
lean -j1 -M6144 -Ddebug.skipKernelTC=false -R "$HERE" "$HERE/Audit.lean"
