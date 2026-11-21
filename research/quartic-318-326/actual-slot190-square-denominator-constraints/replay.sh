#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
sha256sum -c SHA256SUMS
a=linked-detector-square-den2399-r1
b=linked-detector-pythagorean-contact-obstruction-r1
for d in "$a" "$b" joined-square-denominator-cold-r1; do (cd "$d" && sha256sum -c SHA256SUMS); done
python3 -B "$a/check_actual_2399_square_denominator.py" | cmp - "$a/EXACT-SQUARE-CONTACT-2399.json"
python3 -B "$b/check_pythagorean_contact.py" | cmp - "$b/EXACT-PYTHAGOREAN-CONTACT.json"
printf '%s\n' 'Universal 2399 and scoped Pythagorean 407 replays passed.'
