#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
for d in rc-linked-scalar-order3-resultant-r1 rc-linked-scalar-order3-resultant-gcd-r1 independent-review; do
    (cd "$d"; sha256sum -c SHA256SUMS)
done
donor=rc-linked-scalar-order3-resultant-r1/ORDER3-FIXED-RESULTANTS.json
python3 -B independent-review/check_independent_order3_resultants.py "$donor" | cmp - independent-review/EXACT-REPLAY.txt
python3 -B rc-linked-scalar-order3-resultant-gcd-r1/check_literal_order3_resultant_gcd.py "$donor" | cmp - rc-linked-scalar-order3-resultant-gcd-r1/LITERAL-ORDER3-RESULTANT-GCD.json
echo 'Independent full eliminants and literal order-three exclusion replay exactly.'
