#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
python3 -B summarize_exact_rows.py
if [ "$#" -eq 1 ] && [ "$1" = "--all" ]; then
  T=$(mktemp -d)
  trap 'rm -rf "$T"' EXIT HUP INT TERM
  export T
  seq 0 18 | xargs -P 4 -I% sh -c 'python3 -B check_D311_p11_vertex.py "%" >"$T/%.row"'
  for i in $(seq 0 18); do cat "$T/$i.row"; done | cmp - EXACT-D311-P11-ALL-ARCS.ndjson
fi
