#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
sha256sum -c SHA256SUMS
a=linked-detector-w37-full-h-boundary-r2
b=joined-slot190-full-h-cold-r1
for s in "$a" "$b" linked-detector-w37-elliptic-depth-split-r1 linked-detector-w37-depth-r1 linked-detector-known16-exhaustion-r1; do
  (cd "$s" && sha256sum -c SHA256SUMS)
done
python3 -B "$a/check_actual_h_prime_boundary.py" | cmp - "$a/EXACT-ALL-H-PRIME-BOUNDARY.json"
python3 -B "$b/replay_all_5_branches.py" "$a/EXACT-ALL-H-PRIME-BOUNDARY.json" | cmp - "$b/EXACT-ALL-WIDENED-5-BRANCHES.json"
printf '%s\n' 'All h-prime rows, sharp author branches and independent permissive branches passed.'
