#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
d=rc-linked-scalar-H-visible-switch-cycles-r1
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT HUP INT TERM
python3 -B "$d/check_visible_switch_cycles.py" >"$tmp/author"
cmp "$tmp/author" "$d/ACTUAL-VISIBLE-SWITCH-CYCLES.json"
python3 -B independent-review/check_independent_visible_switches.py \
  --proof-dir "$d" \
  --small rc-linked-scalar-specialization-r1/ACTUAL-THETA-MODULAR-ROWS.json \
  --large rc-linked-scalar-higher-descent-r2/ACTUAL-NEW-H-PRIMES.json >"$tmp/independent"
cmp "$tmp/independent" independent-review/EXACT-INDEPENDENT-REPLAY.json
printf '%s\n' 'Author and independent exact cycle replays match.'
