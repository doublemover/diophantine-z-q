#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
sha256sum -c SHA256SUMS
a=linked-detector-three-scale-incidence-r1
for d in "$a" linked-detector-three-scale-prime-router-r1; do (cd "$d" && sha256sum -c SHA256SUMS); done
python3 -B "$a/check_actual_three_scale_incidence.py" | cmp - "$a/EXACT-THREE-SCALE-INCIDENCE.json"
b=joined-three-scale-incidence-cold-r1
(cd "$b" && sha256sum -c SHA256SUMS)
python3 -B "$b/check_three_scale_independent.py" rc-linked-four-pole-common-q-r1/ACTUAL-COMMON-Q-SCALAR-PREFIX.json linked-detector-new-split-singleton-r1/EXACT-SINGLETON-RETUNE.json "$a/EXACT-THREE-SCALE-INCIDENCE.json" | cmp - "$b/EXACT-INDEPENDENT-REPLAY.txt"
printf '%s\n' 'Exact author local triad and common real h replay passed.'
