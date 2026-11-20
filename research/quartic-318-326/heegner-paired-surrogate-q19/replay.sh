#!/usr/bin/env bash
set -euo pipefail
here="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$here"
short="${SHORT:-../heegner-odd2544-shorter}"
book="${BOOK:-../heegner-odd2544-theta/high-hom-1120/heegner-compressed-trace/odd2544-weight-primefree-r1}"
short="$(cd -- "$short" && pwd)"
book="$(cd -- "$book" && pwd)"
(cd "$short"; sha256sum -c "$here/SHORT-SHA256SUMS")
(cd "$book"; sha256sum -c "$here/BOOK-SHA256SUMS")
python3 -B check_q19_paired_support.py | cmp - EXACT-Q19-PAIRED-SUPPORT-AND-SEL2.json
(cd independent-review; python3 -B check_full_sel2.py | cmp - INDEPENDENT-SEL2.json)
work="$(mktemp -d)"
trap 'rm -rf -- "$work"' EXIT
"${CXX:-g++}" -O3 -std=c++17 "$short/rank3_exact_reps_small.cpp" -o "$work/rank3"
PYTHONPATH="$book" python3 -B "$short/recalibrate_short_auxiliaries.py" "$work/rank3" \
    -323 37 146965 -35 -132107 37 60108685 -35 | cmp - EXACT-TORIC-PAIR-Q19.json
echo "Exact paired q=19 replay passed."
