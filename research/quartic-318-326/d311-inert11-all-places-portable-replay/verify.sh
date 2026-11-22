#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
(cd independent-review && sha256sum -c SHA256SUMS)
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT HUP INT TERM
cp -R source "$T/"
find "$T/source" -type f -name '*.ndjson.txt' -exec sh -eu -c '
  for f in "$@"; do
    target=$(printf "%s" "$f" | sed "s/\\.txt$//")
    mv "$f" "$target"
  done
' sh {} +
base=$T/source/high-hom-1120/heegner-compressed-trace
(cd "$base/original-D311-inert11-full-valuation-r1" && sh verify.sh)
(cd "$base/original-D311-inert11-quadratic-projections-r1" && sh verify.sh "$@")
