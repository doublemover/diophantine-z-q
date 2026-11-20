#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
d=rc-linked-scalar-order5-exact-audit-r1
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT HUP INT TERM
python3 -B "$d/check_order5_local_arms.py" >"$tmp/arms"
cmp "$tmp/arms" "$d/INDEPENDENT-THREE-ARMS.json"
if [ "$#" -gt 0 ] && [ "$1" = --local-only ]; then
    printf '%s\n' 'All three independent local arms match.'
    exit 0
fi
node "$d/quartic-2026-11-20-order-five-exact.js" >"$tmp/author"
cmp "$tmp/author" "$d/EXACT-ORDER-FIVE-REPLAY.json"
python3 -B "$d/check_order5_independent.py" >"$tmp/independent"
cmp "$tmp/independent" "$d/INDEPENDENT-DETERMINANTS-PSI.json"
python3 - "$tmp" <<'PY'
from pathlib import Path
import sys,json
d=Path(sys.argv[1])
A=json.loads((d/'author').read_text()); B=json.loads((d/'independent').read_text()); C=json.loads((d/'arms').read_text())
assert [{k:v for k,v in row.items() if k!='count'} for row in A['result']]==B
assert all(all(x[k]==y[k] for k in ('p','W','c','D','F')) for x,y in zip(A['local'],C))
PY
printf '%s\n' 'Author and both independent exact order-five replays match.'
