#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
sha256sum -c SHA256SUMS
cd high-hom-1120/heegner-compressed-trace/original-materialized-a617-scalar-r1
sha256sum -c SHA256SUMS
r=$(mktemp)
trap 'rm -f "$r"' EXIT
python3 -B check_materialized_a617_scalar.py > "$r"
cmp "$r" EXACT-MATERIALIZED-A617-SCALAR.json
