#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
sha256sum -c SHA256SUMS
a=linked-detector-all-split-but-no-orientation-r1
(cd "$a" && sha256sum -c SHA256SUMS)
python3 -B "$a/check_all_split_but_incompatible.py" | cmp - "$a/EXACT-ALL-SPLIT-BUT-INCOMPATIBLE.json"
printf '%s\n' 'Complete rational F support and the actual p=479 orientation obstruction replayed.'
