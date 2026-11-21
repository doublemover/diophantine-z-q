#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
r() { (cd "actual-one-I-$1" && python3 -B "$2" | cmp - "$3"); }
r cyclotomic13-r1 check_point_field13_presentation.py EXACT-POINT-FIELD-13.json
r cyclotomic13-r1 check_local13_torsion.py EXACT-LOCAL13-ORDINARY-WILD.json
r explicit-line-field-r2 check_actual_line_field.py ACTUAL-DEGREE14-LINE-FIELD.json
r explicit-line-field-r2 check_field_discriminants.py ACTUAL-FIELD-DISCRIMINANTS.json
r incidence-selmer-r1 check_point_covector_incidence.py EXACT-POINT-COVECTOR-INCIDENCE.json
r incidence-selmer-r1 check_actual_transvection_53.py EXACT-ACTUAL-TRANSVECTION-53.json
r mirror-ray-class-r1 check_actual_mirror_53.py EXACT-ACTUAL-MIRROR-53-PRIME.json
r strict-ordinary-class-r1 check_ordinary_factor_base_gap.py EXACT-ORDINARY-FACTOR-BASE-GAP.json
r ordinary-q53-ideal-r1 check_actual_q53_principal_localization.py EXACT-ORDINARY-Q53-IDEAL-AND-PRINCIPAL-CHART.json
r q53-global-norm-r1 check_q53_global_principal_norm.py ACTUAL-Q53-GLOBAL-PRINCIPAL-NORM.json
r q53-global-norm-r1 check_q53_small_support.py EXACT-Q53-SMALL-MIRROR-SUPPORT.json
r q53-relative-gaussian-r1 check_relative_mirror_polynomial.py EXACT-RELATIVE-MIRROR-POLYNOMIAL-AND-COMPOSITE.json
(
  cd actual-one-I-q53-factor-base-smoothness-r1
  exe=$(mktemp)
  trap 'rm -f "$exe"' EXIT
  "${CXX:-c++}" -std=c++17 -O3 check_q53_smoothness.cpp -lgmpxx -lgmp -o "$exe"
  python3 -B exact_q53_cofactor.py | "$exe" 150000000 | cmp - EXACT-Q53-COMPLEMENT-150M-SIEVE.json
  python3 -B verify_q53_sieve_output.py
)
python3 -B independent-q53-review/check_q53_norm_residues_independent.py . |
  cmp - independent-q53-review/EXACT-INDEPENDENT-RESIDUES.txt
python3 -B independent-review/check_mirror53_independent.py \
    actual-one-I-cyclotomic13-r1/EXACT-POINT-FIELD-13.json \
    actual-one-I-incidence-selmer-r1/EXACT-ACTUAL-TRANSVECTION-53.json \
    actual-one-I-mirror-ray-class-r1/EXACT-ACTUAL-MIRROR-53-PRIME.json \
    actual-one-I-explicit-line-field-r2/ACTUAL-FIELD-DISCRIMINANTS.json \
  | cmp - independent-review/EXACT-INDEPENDENT-53-REPLAY.txt
echo "All archived q53 arithmetic replays match."
