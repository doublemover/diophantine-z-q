#!/bin/sh
set -eu
cd "$(dirname "$0")"
replay() {
    tmp=$(mktemp)
    trap 'rm -f "$tmp"' EXIT HUP INT TERM
    python3 "$1" > "$tmp"
    cmp "$tmp" "$2"
    rm -f "$tmp"
    trap - EXIT HUP INT TERM
}
replay principal-metric/check_principal_period.py principal-metric/EXACT-PRINCIPAL-PERIOD.json
replay period-cohomology/check_period_quotient.py period-cohomology/EXACT-PERIOD-QUOTIENT.json
replay shared-dt/check_shared_dt.py shared-dt/EXACT-SHARED-DT.json
replay ordinary-and-finite/check_same_section.py ordinary-and-finite/EXACT-SAME-SECTION.json
replay ordinary-and-finite/check_ordinary_axis.py ordinary-and-finite/EXACT-ORDINARY-AXIS.json
replay ordinary-and-finite/check_literal_coarse.py ordinary-and-finite/EXACT-LITERAL-COARSE.json
replay geometric-context/check_original_fine_overlap.py geometric-context/EXACT-FINE-OVERLAP-CONTROLS.json
replay geometric-context/check_universal_family_ks.py geometric-context/EXACT-UNIVERSAL-FAMILY-KS-CONTROLS.json
replay geometric-context/check_cech_boundary.py geometric-context/EXACT-CECH-BOUNDARY.json
