#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
(cd reference-D119
 sha256sum -c SHA256SUMS
 python3 -B replay_inert_cm_pilot.py | cmp - EXACT-INERT-CM-PILOT.json)
(cd proof
 sha256sum -c SHA256SUMS
 python3 -B replay_weighted_genus.py ../reference-D119/EXACT-INERT-CM-PILOT.json | cmp - EXACT-WEIGHTED-GENUS-CONTROLS.json)
(cd both-arm
 sha256sum -c SHA256SUMS
 python3 -B replay_both_weighted_blocks.py | cmp - EXACT-BOTH-WEIGHTED-BLOCKS.json)
(cd independent-review && sha256sum -c SHA256SUMS)
(cd both-arm-independent-review && sha256sum -c SHA256SUMS)
