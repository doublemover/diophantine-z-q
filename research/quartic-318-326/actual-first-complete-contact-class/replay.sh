#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
sha256sum -c SHA256SUMS
a=linked-detector-first-complete-order-compatible-class-r1
b=linked-detector-real-progression-density-r1
c=linked-detector-one-class-conic-completion-r1
d=joined-complete-first-class-cold-r1
e=linked-detector-gaussian-order29-new-classes-r1
f=joined-sixteen-gaussian-order29-cold-r1
for dir in "$a" "$b" "$c" "$d" "$e" "$f"; do (cd "$dir" && sha256sum -c SHA256SUMS); done
python3 -B "$a/check_complete_class_finite_donors.py" | cmp - "$a/EXACT-FINITE-PILOT-AND-CROSS-RAY.json"
python3 -B "$b/check_nontorsion_313.py" | cmp - "$b/EXACT-313-FIRST-ORDERS.json"
if [ "${1-}" = "--xvi" ]; then
  x=linked-detector-three-scale-incidence-r1/EXACT-THREE-SCALE-INCIDENCE.json
  y=linked-detector-six-compatible-incidences-r1/EXACT-SIX-INCIDENCES.json
  z=linked-detector-twelve-compatible-incidences-r1/EXACT-TWELVE-INCIDENCES.json
  w=linked-detector-low-opposite-unhit-r1/EXACT-LOW-OPPOSITE-NEW-CLASS.json
  v="$e/EXACT-GAUSSIAN-ORDER29-NEW-CLASSES.json"
  python3 -B "$e/check_gaussian_order29_new_classes.py" | cmp - "$v"
  python3 -B "$f/check_sixteen_incidence_independent.py" rc-linked-four-pole-common-q-r1/ACTUAL-COMMON-Q-SCALAR-PREFIX.json linked-detector-new-split-singleton-r1/EXACT-SINGLETON-RETUNE.json "$x" "$y" "$z" "$w" "$v" | cmp - "$f/joined-sixteen-independent.log"
fi
printf '%s\n' 'Exact finite pilot, all reciprocal phase rows and literal non-torsion replay passed.'
