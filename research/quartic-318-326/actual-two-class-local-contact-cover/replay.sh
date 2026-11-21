#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
sha256sum -c SHA256SUMS
a=linked-detector-first-complete-order-compatible-class-r1
b=linked-detector-real-progression-density-r1
c=linked-detector-two-class-local-genus-one-r1
d=joined-two-class-local-cover-cold-r1
for dir in "$a" "$b" "$c" "$d"; do (cd "$dir" && sha256sum -c SHA256SUMS); done
python3 -B "$a/check_complete_class_finite_donors.py" | cmp - "$a/EXACT-FINITE-PILOT-AND-CROSS-RAY.json"
python3 -B "$b/check_nontorsion_313.py" | cmp - "$b/EXACT-313-FIRST-ORDERS.json"
python3 -B "$c/check_second_pilot.py" | cmp - "$c/EXACT-SECOND-PILOT.json"
printf '%s\n' 'Both exact marked pilot counts, sixteen reciprocal phases, and literal non-torsion replay passed.'
