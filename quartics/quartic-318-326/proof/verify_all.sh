#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
bash 318/verify_concrete.sh
bash components/verify_components.sh
for package in 318 components; do
  (cd "$package" && lake env lean -Ddebug.skipKernelTC=false FullAudit.lean)
done
(cd components && lake env lean -Ddebug.skipKernelTC=false ConstantLift326.lean \
  -o .lake/build/lib/lean/ConstantLift326.olean) | tee constant-lift-rechecked.log
python3 - <<'CHECK'
import re
from pathlib import Path
lines = re.sub(r'\n[ \t]+', ' ', Path('constant-lift-rechecked.log').read_text()).splitlines()
assert len(lines) == 7, lines
for line in lines:
    assert 'depends on axioms:' in line, line
    assert {x.strip() for x in line.split('[', 1)[1].split(']')[0].split(',')} <= {'propext'}, line
print('PASS: seven constant-lift theorem audits. Literal 326 replay and global source arithmetic remain open.')
CHECK
