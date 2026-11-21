#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
sha256sum -c SHA256SUMS
(cd source && sha256sum -c SHA256SUMS)
r=$(mktemp)
trap 'rm -f "$r"' EXIT
python3 -B source/check_a617_cassels_controls.py > "$r"
cmp "$r" EXACT-REPLAY.txt
