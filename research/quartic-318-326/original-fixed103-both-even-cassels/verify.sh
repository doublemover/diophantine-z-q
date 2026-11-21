#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
sha256sum -c SHA256SUMS
(
 cd source/original-fixed103-both-even-cassels-r1
 sha256sum -c SHA256SUMS
 python3 -B verify_both_even_cassels.py | cmp - EXACT-BOTH-EVEN-CASSEL-GADGETS.json
)
(cd source/ct-original-fixed-final103-paired-selector-r1; sha256sum -c SHA256SUMS)
(cd source/ct-original-fixed-final103-even-cassels-r1; sha256sum -c SHA256SUMS)
(cd independent-review; sha256sum -c SHA256SUMS)
