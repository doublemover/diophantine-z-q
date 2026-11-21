#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
sha256sum -c SHA256SUMS
cd high-hom-1120/heegner-compressed-trace/original-a617-materialized-fixed-support-descent-r1
sha256sum -c SHA256SUMS
r=$(mktemp)
trap 'rm -f "$r"' EXIT
python3 -B check_fixed_support.py > "$r"
cmp "$r" EXACT-FIXED-SUPPORT.json
