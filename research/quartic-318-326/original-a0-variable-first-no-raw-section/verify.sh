#!/bin/sh
set -eu
CDPATH= cd -- "$(dirname -- "$0")"
sha256sum -c SHA256SUMS
(cd source/original-a0-variable-first-no-raw-section-r1 && sha256sum -c SHA256SUMS)
(cd source/original-a0-factorless-companion-norm-line-r1 && sha256sum -c SHA256SUMS &&
  python3 -B replay_actual_norm_line.py | cmp - EXACT-NORM-LINE-LOCAL-ROWS.json)
(cd independent-review && sha256sum -c SHA256SUMS)
