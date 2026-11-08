#!/usr/bin/env bash
set -euo pipefail
source /workspace/scratch/2cb21e4e0864/recovery-geometric-0358/fifth-character-work/env.sh
echo "ACQUIRED $(date -u +%FT%TZ) fifth-character"
trap 'echo "RELEASED $(date -u +%FT%TZ) fifth-character"' EXIT
for m in "$@"; do
 echo "CHECK $m $(date -u +%FT%TZ)"
 timeout "${LEAN_TIMEOUT:-120}" lean -Ddebug.skipKernelTC=false -R "$HERE" -o "$HERE/$m.olean" "$HERE/$m.lean"
done
