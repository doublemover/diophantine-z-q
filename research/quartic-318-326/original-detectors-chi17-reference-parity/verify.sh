#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
(cd proof; sha256sum -c SHA256SUMS; python3 -B replay_reference_parity.py | cmp - EXACT-REFERENCE-PARITY.json)
(cd independent-review; sha256sum -c SHA256SUMS)
