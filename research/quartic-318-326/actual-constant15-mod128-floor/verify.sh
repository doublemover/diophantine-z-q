#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
(cd review && sha256sum -c SHA256SUMS)
cd high-hom-1120/heegner-compressed-trace/original-constant15-actual-coefficient-valuation-floor-r1
sha256sum -c SHA256SUMS
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM
python3 -B check_exact_level75_period_and_floor.py > "$work/out"
cmp "$work/out" EXACT-LEVEL75-PERIOD-AND-FLOOR.json
