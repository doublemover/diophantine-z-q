#!/usr/bin/env bash
set -euo pipefail
here="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$here"
book="${BOOK:-../heegner-odd2544-theta/high-hom-1120/heegner-compressed-trace/odd2544-weight-primefree-r1/ACTUAL-ODD2544-MARKED-ORDERS-Q29.json}"
ref="${REF:-../heegner-f53-fixed-example/high-hom-1120/heegner-f53-descended/ACTUAL-FULL-TRACE-F53.json}"
t=signed-optimal-embedding-replay-r1
(cd "$t"; sha256sum -c SHA256SUMS)
python3 -B "$t/replay_direct_signed_embeddings.py" "$book" "$ref" | cmp - "$t/EXACT-DIRECT-OPTIMAL-EMBEDDING-REPLAY-323.json"
echo "Exact direct reference replay passed."
