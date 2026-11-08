#!/usr/bin/env bash
source /workspace/scratch/2cb21e4e0864/recovery-hodge-0358/character-invariant-lines-work/env.sh
cd /workspace/scratch/2cb21e4e0864
printf 'ACQUIRED %s\n' "$(date -u +%FT%TZ)"
rc=0
for m in "$@"; do
 echo START "$m" "$(date -u +%FT%TZ)"
 timeout -k 5 90 lean -Ddebug.skipKernelTC=false -j1 -M 6144 -o recovery-hodge-0358/character-invariant-lines-work/lib/$m.olean recovery-hodge-0358/character-invariant-lines-work/$m.lean
 rc=$?;echo RESULT "$m" "$rc";[ "$rc" = 0 ] || break
done
printf 'RELEASED %s status=%s\n' "$(date -u +%FT%TZ)" "$rc"
exit "$rc"
