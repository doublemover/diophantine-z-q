#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
(cd review && sha256sum -c SHA256SUMS)
sh high-hom-1120/heegner-compressed-trace/original-constant15-actual-mod16-lift-r2/verify.sh
