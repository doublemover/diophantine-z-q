#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
(cd proof; sha256sum -c SHA256SUMS; python3 -B replay_dyadic_as_edge_phase.py | cmp - EXACT-AS-EDGE-PHASE.json)
(cd independent-review; sha256sum -c SHA256SUMS)
