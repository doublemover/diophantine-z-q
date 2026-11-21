#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
(cd independent-review && sha256sum -c SHA256SUMS)
(cd source/original-detectors-ordinary-seventh-moment-r1
 sha256sum -c SHA256SUMS
 python3 -B replay_ordinary_seventh_moment.py | cmp - EXACT-ORDINARY-SEVENTH-MOMENT.json
 [ "$(printf '47\n37\n' | python3 -B weber_seventh_moment.py --polynomials)" = '{"jet": [1, 0, 1, 0, 1, 1, 1, 0], "phase": 1, "power_sums": [0, 0, 0, 0, 1, 0, 1], "simplified_phase": 1}' ])
