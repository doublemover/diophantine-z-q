#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
sha256sum -c SHA256SUMS
a=linked-detector-six-compatible-incidences-r1
b=joined-six-incidence-cold-r1
c=linked-detector-saturation-character-obstruction-r1
for d in "$a" "$b" "$c" linked-detector-three-scale-incidence-r1 linked-detector-three-scale-prime-router-r1; do
  (cd "$d" && sha256sum -c SHA256SUMS)
done
python3 -B "$a/check_actual_six_incidences.py" | cmp - "$a/EXACT-SIX-INCIDENCES.json"
python3 -B "$b/check_six_incidence_independent.py" rc-linked-four-pole-common-q-r1/ACTUAL-COMMON-Q-SCALAR-PREFIX.json linked-detector-new-split-singleton-r1/EXACT-SINGLETON-RETUNE.json linked-detector-three-scale-incidence-r1/EXACT-THREE-SCALE-INCIDENCE.json "$a/EXACT-SIX-INCIDENCES.json" | cmp - "$b/EXACT-INDEPENDENT-REPLAY.txt"
python3 -B "$c/check_saturation_character_rank.py" | cmp - "$c/EXACT-GAUSSIAN-ROSTER-CHARACTER-RANK.json"
printf '%s\n' 'Author six-incidence, independent six-incidence, and necessary saturation character replays passed.'
