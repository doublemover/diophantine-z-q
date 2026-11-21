#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
sha256sum -c SHA256SUMS
replay() (
 cd "source/$1"
 sha256sum -c SHA256SUMS
 python3 -B "$2" | cmp - "$3"
)
replay original-linear-q-a0-exact-anchor-depth-full-scalar-r1 verify_full_scalar_anchor_depth.py EXACT-A0-FULL-SCALAR-ANCHOR-DEPTH.json
replay original-linear-q-a0-exact-anchor-depth-r1 verify_exact_anchor_depth.py EXACT-A0-ANCHOR-DEPTH.json
replay original-linear-q-a0-short-anchor-labels-r1 verify_short_anchor_labels.py EXACT-A0-SHORT-ANCHOR-LABELS.json
replay original-linear-q-a0-archived-clearing-height-floor-r1 verify_archived_clearing_height_floor.py EXACT-ARCHIVED-CLEARING-HEIGHT-FLOOR.json
(cd independent-review; sha256sum -c SHA256SUMS)
