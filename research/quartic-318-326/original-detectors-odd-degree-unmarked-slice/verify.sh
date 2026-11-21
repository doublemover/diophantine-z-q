#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
for d in source/* independent-review; do
  (cd "$d"; sha256sum -c SHA256SUMS)
done
