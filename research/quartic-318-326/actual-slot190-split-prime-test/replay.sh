#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
sha256sum -c SHA256SUMS
a=linked-detector-new-split-singleton-r1
b=joined-positive-singleton-cold-r1
for d in "$a" "$b"; do (cd "$d" && sha256sum -c SHA256SUMS); done
python3 -B "$a/check_actual_singleton_retune.py" | cmp - "$a/EXACT-SINGLETON-RETUNE.json"
python3 -B check_same_t_p67.py "$a/EXACT-SINGLETON-RETUNE.json"
printf '%s\n' 'Exact positive 3162001 replay passed.'
