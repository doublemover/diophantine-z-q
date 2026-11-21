#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
M=high-hom-1120/heegner-compressed-trace/actual-zero-ordinate-crossed-sign-modulus-r1
A=high-hom-1120/heegner-compressed-trace/actual-zero-ordinate-fixed-artin-reciprocity-r1
python3 -B "$M/check_crossed_sign_modulus.py" | cmp - "$M/EXACT-CROSSED-MODULUS-CONTROLS.json"
python3 -B "$A/check_zero_ordinate_fixed_artin.py" | cmp - "$A/EXACT-FIXED-ARTIN-PHASES.json"
echo 'Two exact arithmetic replays matched.'
