#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
(cd proof; sha256sum -c SHA256SUMS; python3 -B replay_cusp_pullback.py | cmp - EXACT-CUSP-PULLBACK.json)
(cd independent-review; sha256sum -c SHA256SUMS)
