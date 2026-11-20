#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS >/dev/null
if [ "$#" -eq 0 ]; then set -- ../heegner-direct-cm4; fi
direct=$(realpath "$1")
book="$direct/donors/ACTUAL-ODD2544-MARKED-ORDERS-Q29.json"
chart="$direct/donors/LOW-48-SUPERSINGULAR-F53.json"
sieve="$direct/donors/eisenstein_representations.py"
test -f "$book" && test -f "$chart" && test -f "$sieve"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT HUP INT TERM
math="$tmp/high-hom-1120/heegner-compressed-trace"
join="$tmp/joined-work-20261120/rc-d1-f53-supersingular-low-map-r1"
mkdir -p "$math"/comparison "$math"/odd2544-weight-primefree-r1 \
    "$math"/paired-prime-surrogate-409-r1/eisenstein-replay-r1 \
    "$math"/odd2544-bounded-negative-probe-r1 "$join"
ln -s "$book" "$math"/odd2544-weight-primefree-r1/
ln -s "$chart" "$join/"
ln -s "$sieve" "$math"/paired-prime-surrogate-409-r1/eisenstein-replay-r1/
cp -a comparison/*.py "$math"/comparison/
cp weighted-donors/EXACT-TORIC-PAIR-Q*.json "$math"/paired-prime-surrogate-409-r1/
cp weighted-donors/SHORT-*.json "$math"/odd2544-bounded-negative-probe-r1/
python3 -B "$math/comparison/compare_seven_exact_controls.py" \
    | cmp - comparison/EXACT-SEVEN-DIRECT-NEGATIVE-COMPARISONS.json
printf '%s\n' 'Seven exact direct vs negative mod-13 comparisons passed.'
