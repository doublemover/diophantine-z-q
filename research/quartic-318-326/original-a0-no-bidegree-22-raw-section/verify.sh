#!/bin/sh
set -eu
CDPATH= cd -- "$(dirname -- "$0")"
sha256sum -c SHA256SUMS
(cd source && sha256sum -c SHA256SUMS && python3 -B replay_bidegree_22.py | cmp - EXACT-MOBIUS-CANDIDATES.json)
(cd independent-review && sha256sum -c SHA256SUMS)
