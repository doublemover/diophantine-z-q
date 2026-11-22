#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
sha256sum -c SHA256SUMS
(
 cd source/high-hom-1120/heegner-compressed-trace/original-inert29-CM-real-ideal-r2
 sha256sum -c SHA256SUMS
 python3 -B verify_real_CM_cubic.py | cmp - EXACT-REAL-CM-CUBIC.json
)
(
 cd source/high-hom-1120/heegner-compressed-trace/original-inert29-CM-supported-cubic-r1
 sha256sum -c SHA256SUMS
 python3 -B verify_CM_supported_cubic.py | cmp - EXACT-CM-SUPPORTED-CUBIC.json
)
(cd independent-review; sha256sum -c SHA256SUMS)
