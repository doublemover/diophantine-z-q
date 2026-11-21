#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
(cd review && sha256sum -c SHA256SUMS)
cd high-hom-1120/heegner-compressed-trace/original-a617-quadratic-graph-genus-one-r1
sha256sum -c SHA256SUMS
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM
python3 -B check_a617_quadratic_graph.py > "$work/out"
cmp "$work/out" EXACT-A617-GRAPH.json
