#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
sha256sum -c SHA256SUMS
(
 cd source/original-fixed241-primitive-moving-base-r1
 sha256sum -c SHA256SUMS
 python3 -B verify_level48_241_symbol_ratio.py | cmp - EXACT-LEVEL48-241-SYMBOL-RATIO.json
)
(
 cd source/original-fixed103-even-reference241-r1
 sha256sum -c SHA256SUMS
 python3 -B verify_even_ref241.py | cmp - EXACT-EVEN-REF241.json
)
(cd source/original-detectors-inert29-three-maximal-orders-r1; sha256sum -c SHA256SUMS)
(cd source/ct-level48-fixed103-D1751-conductor241-pilot-r1; sha256sum -c SHA256SUMS)
(cd independent-review; sha256sum -c SHA256SUMS)
