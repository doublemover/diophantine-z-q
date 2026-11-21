#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
cd high-hom-1120/heegner-compressed-trace/original-constant15-actual-mod2-orbit-sturm-r1
sha256sum -c SHA256SUMS
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT HUP INT TERM
"${CXX:-c++}" -O3 -std=c++17 check_constant15_parity_sturm.cpp -o "$tmp/check"
"$tmp/check" | cmp - EXACT-CONSTANT15-PARITY-STURM.txt
