#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
(cd independent-review && sha256sum -c SHA256SUMS)
cd source/high-hom-1120/heegner-compressed-trace/original-D311-inert19-selected-shell-x112-r1
sha256sum -c SHA256SUMS
python3 -B check_x112_physical_mark.py | cmp - EXACT-D311-P19-X112-PHYSICAL-MARK.json
python3 -B check_x112_all_factor_depths.py | cmp - EXACT-D311-P19-X112-ALL-FACTORS.json
