#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
(cd source && sha256sum -c SHA256SUMS)
(cd independent-review && sha256sum -c SHA256SUMS)
