#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/.." && pwd)
source "$ROOT/recovery-toolchain/proof-environment.sh"
export LEAN_PATH="$HERE:$LEAN_PATH"
cd "$ROOT/diophantine-z-q/quartics/quartic-318-326/proof/progress"
lake env lean -M 6144 -j 1 -Ddebug.skipKernelTC=false -R "$HERE" -o "$HERE/$1.olean" "$HERE/$1.lean" 2>&1 | tee "$HERE/$1.log"
