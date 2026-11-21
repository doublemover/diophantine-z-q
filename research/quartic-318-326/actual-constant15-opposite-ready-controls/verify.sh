#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
cd high-hom-1120/heegner-compressed-trace/original-constant15-opposite-ready-controls-r1
sha256sum -c SHA256SUMS
python3 -B check_constant15_ready_controls.py | cmp - EXACT-CONSTANT15-OPPOSITE-READY-CONTROLS.json
