#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
(
 cd prerequisites/marked-box
 sha256sum -c SHA256SUMS
 python3 -B check_one_I_marked_cover_box.py | cmp - EXACT-ONE-I-MARKED-COVER-BOX.json
)
(
 cd prerequisites/local-splits
 sha256sum -c SHA256SUMS
 python3 -B check_one_I_split_everywhere.py | cmp - EXACT-ONE-I-MARKED-SPLIT-LOCAL.json
)
(
 cd result
 sha256sum -c SHA256SUMS
 python3 -B check_actual_minimal_intersection.py | cmp - EXACT-MINIMAL-INTERSECTION.json
 python3 -B check_isogenous_exact_selmer.py | cmp - EXACT-ISOGENOUS-SEL2.json
)
(
 cd review
 sha256sum -c SHA256SUMS
 python3 -B check_literal_sel2.py | cmp - INDEPENDENT-REPLAY.txt
)
