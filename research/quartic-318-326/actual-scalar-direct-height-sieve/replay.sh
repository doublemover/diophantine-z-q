#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM
python3 derive_scalar_rows.py > "$work/rows.tsv"
cmp independent-rows.tsv "$work/rows.tsv"
python3 - <<'PY'
import ast, re
src=open('quartic-2026-11-20-alternate-height-sieve.js').read()
expected=[tuple(z) for z in ast.literal_eval(re.search(r'expectedRows = ([^;]+);',src)[1])]
actual=[tuple(map(int,l.split())) for l in open('independent-rows.tsv')]
assert expected==actual and len(actual)==46
PY
${CXX:-c++} -std=c++17 -O3 -Wall -Wextra verify_direct_height.cpp -o "$work/verify"
"$work/verify" 1000000000000000 < "$work/rows.tsv" > "$work/independent.txt"
cmp independent-replay-10p15.txt "$work/independent.txt"
node quartic-2026-11-20-alternate-height-sieve.js 1000000000000000 > "$work/original.json"
cmp dreamer-replay-10p15.json "$work/original.json"
cat "$work/independent.txt"
echo 'Both complete direct-height computations agree with the frozen transcripts.'
