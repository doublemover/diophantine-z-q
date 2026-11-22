#!/bin/sh
set -eu
CDPATH= cd -- "$(dirname -- "$0")"
sha256sum -c SHA256SUMS
(cd source && sha256sum -c SHA256SUMS &&
  python3 -B replay_literal_trace_index.py | cmp - EXACT-LITERAL-TRACE-LOCAL-ROWS.json)
(cd independent-review && sha256sum -c SHA256SUMS)
