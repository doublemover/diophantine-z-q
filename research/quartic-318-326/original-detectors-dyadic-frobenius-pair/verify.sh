#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
cd source
(
  cd dyadic/heegner-compressed-trace
  (cd original-detectors-dyadic-frobenius-pair-r1; sha256sum -c SHA256SUMS; python3 -B replay_exact_faber_clearing.py | cmp - EXACT-FABER-CLEARING.json)
  (cd original-detectors-invariant-cusp-pullback-r1; sha256sum -c SHA256SUMS; python3 -B replay_cusp_pullback.py | cmp - EXACT-CUSP-PULLBACK.json)
  (cd original-detectors-chi17-dyadic-as-edge-phase-r1; sha256sum -c SHA256SUMS; python3 -B replay_dyadic_as_edge_phase.py | cmp - EXACT-AS-EDGE-PHASE.json)
)
(
  cd rc-native-helper-20261120
  (cd ct-level48-actual-ramified-kummer-fourth-r2; sha256sum -c SHA256SUMS; python3 -B replay_level48_first_half.py | cmp - EXACT-LEVEL48-FIRST-HALF.json)
  (cd ct-original-balanced-detector-selmer-eights-r1; sha256sum -c SHA256SUMS; python3 -B replay_balanced_schur.py | cmp - EXACT-BALANCED-SCHUR.json)
)
(cd ../independent-review; sha256sum -c SHA256SUMS)
