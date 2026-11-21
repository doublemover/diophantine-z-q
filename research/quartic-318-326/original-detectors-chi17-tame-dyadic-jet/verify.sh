#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
(cd base-receiver; sha256sum -c SHA256SUMS)
(cd tame-receiver; sha256sum -c SHA256SUMS; python3 -B replay_D119_dyadic_tame_lift.py | cmp - EXACT-D119-DYADIC-TAME-LOG.json)
(cd independent-review; sha256sum -c SHA256SUMS)
