#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
sha256sum -c SHA256SUMS
(
 cd source/original-linear-q-a0-short-anchor-labels-r1
 sha256sum -c SHA256SUMS
 python3 -B verify_short_anchor_labels.py | cmp - EXACT-A0-SHORT-ANCHOR-LABELS.json
)
(
 cd source/original-linear-q-a0-archived-clearing-height-floor-r1
 sha256sum -c SHA256SUMS
 python3 -B verify_archived_clearing_height_floor.py | cmp - EXACT-ARCHIVED-CLEARING-HEIGHT-FLOOR.json
)
(cd independent-review; sha256sum -c SHA256SUMS)
