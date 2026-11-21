#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM
for spec in check_uniform_mod8:EXACT-UNIFORM-MOD8.txt check_raw_weight_two_mod16:EXACT-RAW-WEIGHT-TWO-MOD16.txt
do
    name=${spec%%:*}
    "${CXX:-c++}" -O3 -std=c++17 "$name.cpp" -o "$work/$name"
    "$work/$name" > "$work/out"
    cmp "$work/out" "${spec#*:}"
done
python3 -B check_literal_scalar_at_23.py > "$work/out"
cmp "$work/out" EXACT-LITERAL-SCALAR-AT-23.json
