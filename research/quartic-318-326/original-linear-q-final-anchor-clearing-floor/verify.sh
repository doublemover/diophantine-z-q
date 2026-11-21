#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
(cd independent-review && sha256sum -c SHA256SUMS)
(cd source/original-linear-q-final-anchor-clearing-floor-r1
 sha256sum -c SHA256SUMS
 python3 -B verify_final_anchor_clearing.py | cmp - EXACT-FINAL-ANCHOR-CLEARING.json)
(cd source/original-linear-q-a0-archived-clearing-height-floor-r1
 sha256sum -c SHA256SUMS
 python3 -B verify_archived_clearing_height_floor.py | cmp - EXACT-ARCHIVED-CLEARING-HEIGHT-FLOOR.json)
