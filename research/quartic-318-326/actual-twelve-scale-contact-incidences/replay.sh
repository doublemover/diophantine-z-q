#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
sha256sum -c SHA256SUMS
a=linked-detector-twelve-compatible-incidences-r1
b=linked-detector-cross-symbol-support-r1
c=joined-twelve-cross-symbol-cold-r1
x=linked-detector-three-scale-incidence-r1/EXACT-THREE-SCALE-INCIDENCE.json
y=linked-detector-six-compatible-incidences-r1/EXACT-SIX-INCIDENCES.json
z="$a/EXACT-TWELVE-INCIDENCES.json"
w="$b/EXACT-CROSS-SYMBOL-ROWS.json"
for d in "$a" "$b" "$c" linked-detector-three-scale-incidence-r1 linked-detector-six-compatible-incidences-r1 linked-detector-three-scale-prime-router-r1; do
  (cd "$d" && sha256sum -c SHA256SUMS)
done
python3 -B "$a/check_actual_twelve_incidences.py" | cmp - "$z"
python3 -B "$b/check_actual_cross_support.py" | cmp - "$w"
python3 -B "$c/check_twelve_incidence_independent.py" rc-linked-four-pole-common-q-r1/ACTUAL-COMMON-Q-SCALAR-PREFIX.json linked-detector-new-split-singleton-r1/EXACT-SINGLETON-RETUNE.json "$x" "$y" "$z" | cmp - "$c/EXACT-INDEPENDENT-TWELVE-REPLAY.txt"
python3 -B "$c/check_cross_symbol_independent.py" "$x" "$y" "$w" | cmp - "$c/EXACT-INDEPENDENT-CROSS-REPLAY.txt"
printf '%s\n' 'Author and independent twelve-incidence and cross-symbol replays passed.'
