#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
sha256sum -c SHA256SUMS
a=linked-detector-w37-depth-r1
b=joined-slot190-w37-depth-cold-r1
(cd "$a" && sha256sum -c SHA256SUMS)
(cd "$b" && sha256sum -c SHA256SUMS)
python3 -B "$a/check_actual_shallow_formal.py" | cmp - "$a/EXACT-SPLIT-SHALLOW-FORMAL-ROWS.json"
python3 -B "$b/replay_w37_arms.py" "$a" | cmp - "$b/EXACT-INDEPENDENT-ARITHMETIC.json"
printf '%s\n' 'Author and independent depth arithmetic replay passed.'
