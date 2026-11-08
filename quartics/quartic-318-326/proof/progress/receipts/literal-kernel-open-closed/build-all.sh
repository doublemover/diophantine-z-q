#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
source ./env.sh
# Caller holds compile-coordination/heavy.lock.
while read -r m; do
  lean -Ddebug.skipKernelTC=false -o "$m.olean" "$m.lean"
done < module-order.txt
lean -Ddebug.skipKernelTC=false Audit.lean
