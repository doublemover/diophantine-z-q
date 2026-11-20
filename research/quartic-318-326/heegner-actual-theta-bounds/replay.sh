#!/usr/bin/env bash
set -euo pipefail
if [[ "$#" -gt 1 ]] || [[ "$#" == 1 && "$1" != --full-scan ]]; then exit 2; fi
cd "$(dirname "$0")"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
python3 -B check_theta_exceptional_places.py | cmp - EXACT-EXCLUDED-SMALL-PLACES-AND-SIZE.json
python3 -B source/rc-linked-scalar-higher-descent-r4/check_normalizer_primes_without_packages.py | cmp - source/rc-linked-scalar-higher-descent-r4/EXACT-NORMALIZER-PRIMES.json
g++ -std=c++17 -O3 bound_actual_scalar_expanded_input.cpp -lgmpxx -lgmp -o "$tmp/aff"
g++ -std=c++17 -O3 independent/check_3adic_jacobian.cpp -lgmpxx -lgmp -o "$tmp/jac"
"$tmp/aff" 4096 | cmp - ACTUAL-H-HEIGHT-BOUND-4K.txt
"$tmp/aff" 262188 residue > "$tmp/aff.txt"
head -n1 "$tmp/aff.txt" | cmp - ACTUAL-H-HEIGHT-BOUND-262K.txt
tail -n1 "$tmp/aff.txt" > "$tmp/aff-residue.txt"
"$tmp/jac" > "$tmp/jac-residue.txt"
cmp "$tmp/aff-residue.txt" "$tmp/jac-residue.txt"
printf '%s  %s\n' 756e95c8710a46822f373a9d528ee9e6f3a0dd820ab0d8e9b343f7e6bd656285 "$tmp/jac-residue.txt" | sha256sum -c -
python3 -B independent/check_3adic_cf.py < "$tmp/jac-residue.txt" | cmp - independent/INDEPENDENT-CF.txt
if [[ "$#" == 1 ]]; then
  g++ -std=c++17 -O3 scan_actual_odd_theta.cpp -o "$tmp/scan"
  "$tmp/scan" 30000000 11 | cmp - SCAN-11-30000000.txt
  "$tmp/scan" 200000000 30000001 | cmp - SCAN-30000001-200000000.txt
fi
printf '%s\n' 'Exact bounded replay passed.'
