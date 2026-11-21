#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
(cd independent-review && sha256sum -c SHA256SUMS)
(cd source/original-detectors-chi17-universal-first-switch-r1
 sha256sum -c SHA256SUMS
 python3 -B verify_universal_first_switch.py | cmp - EXACT-UNIVERSAL-FIRST-SWITCH.json)
