#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
H=high-hom-1120/heegner-compressed-trace
R=rc-native-helper-20261120
P="$H/actual-zero-ordinate-aggregate-norm-admission-r2"
N="$H/actual-zero-ordinate-negative-isogeny-row-r1"
F="$H/actual-scalar-kummer-isogeny-and-marked-pairing-r1"
python3 -B "$R/ct-original-scalar-kummer-fiber-r1/verify_actual_scalar_lambda.py" | cmp - "$R/ct-original-scalar-kummer-fiber-r1/EXACT-ACTUAL-SCALAR-LAMBDA.json"
python3 -B "$R/ct-original-scalar-mestre-marked-selmer-r1/replay_marked_selmer.py" | cmp - "$R/ct-original-scalar-mestre-marked-selmer-r1/EXACT-MARKED-SELMER-ROWS.json"
python3 -B "$R/ct-original-scalar-zero-ordinate-boundary-r1/replay_boundary.py" | cmp - "$R/ct-original-scalar-zero-ordinate-boundary-r1/EXACT-ZERO-ORDINATE-CONTROLS.json"
python3 -B "$F/check_single_mark.py" | cmp - "$F/EXACT-SINGLE-MARK-CONTROL.json"
python3 -B "$P/check_boundaries_aggregate.py" | cmp - "$P/EXACT-AGGREGATE-NORM-RECEIVER.json"
python3 -B "$N/check_zero_ordinate_negative_row.py" | cmp - "$N/EXACT-NEGATIVE-ROW-CONTROL.json"
echo 'Six exact arithmetic replays matched.'
