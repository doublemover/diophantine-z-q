#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
sha256sum -c SHA256SUMS
a=linked-detector-low-opposite-unhit-r1
b=joined-fourteen-low-b-cold-r1
x=linked-detector-three-scale-incidence-r1/EXACT-THREE-SCALE-INCIDENCE.json
y=linked-detector-six-compatible-incidences-r1/EXACT-SIX-INCIDENCES.json
z=linked-detector-twelve-compatible-incidences-r1/EXACT-TWELVE-INCIDENCES.json
w="$a/EXACT-LOW-OPPOSITE-NEW-CLASS.json"
(cd "$a" && sha256sum -c SHA256SUMS)
(cd "$b" && sha256sum -c SHA256SUMS)
python3 -B "$a/check_low_opposite_new_class.py" | cmp - "$w"
python3 -B "$b/check_fourteen_incidence_independent.py" rc-linked-four-pole-common-q-r1/ACTUAL-COMMON-Q-SCALAR-PREFIX.json linked-detector-new-split-singleton-r1/EXACT-SINGLETON-RETUNE.json "$x" "$y" "$z" "$w" | cmp - "$b/EXACT-INDEPENDENT-REPLAY.txt"
printf '%s\n' 'Exact author and independent fourteen-contact low-order replays passed.'
