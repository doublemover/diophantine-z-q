#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
# Supply pinned Lean4.35.0, pinned Mathlib and source/dependency-verified
# baseline modules in LEAN_PATH. No dependency downloading is performed here.
python3 - "$HERE" <<'VERIFY'
from pathlib import Path
import hashlib,json,sys
p=Path(sys.argv[1]); b=json.loads((p/'COPY_BINDINGS.json').read_text())
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
q=p.parent/b['packet']
assert sha(q/'receipt.json')==b['receipt_sha256']
assert sha(q/'APPLICATION.json')==b['application_sha256']
for name,digest in b['sources'].items():
    assert sha(p/name)==digest==sha(q/name),name
print('EXACT_PREDECESSOR_COPIES_PASS',len(b['sources']))
VERIFY
OUT=${1:-"$HERE/replay-lib"}
mkdir -p "$OUT"
export LEAN_PATH="$OUT:${LEAN_PATH:-}"
lean --version | grep -F 'version 4.35.0'
while IFS= read -r module; do
  printf 'KERNEL_CHECK %s\n' "$module"
  lean -j1 -M6144 -Ddebug.skipKernelTC=false -R "$HERE" \
    "$HERE/$module.lean" -o "$OUT/$module.olean"
  printf 'STRICT_PASS %s\n' "$module"
done < "$HERE/MODULE_ORDER.txt"
lean -j1 -M6144 -Ddebug.skipKernelTC=false -R "$HERE" "$HERE/Audit.lean"
