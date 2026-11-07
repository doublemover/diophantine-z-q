#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if [[ -x .tooling/elan/bin/lake ]]; then
  export ELAN_HOME="$PWD/.tooling/elan"
  export PATH="$ELAN_HOME/bin:$PATH"
fi
export XDG_CACHE_HOME="${XDG_CACHE_HOME:-$PWD/.cache}"
python3 - <<'CHECK'
import json,hashlib
from pathlib import Path
for name,digest in json.loads(Path('concrete-verification.json').read_text())['sha256'].items():
 assert hashlib.sha256(Path(name).read_bytes()).hexdigest()==digest,name
print('All frozen sources and inputs match.')
CHECK
mkdir -p .lake/build/lib/lean
lake env lean -Ddebug.skipKernelTC=false QuarticOptimization.lean -o .lake/build/lib/lean/QuarticOptimization.olean
lake env lean -Ddebug.skipKernelTC=false SparseQuartic.lean -o .lake/build/lib/lean/SparseQuartic.olean
lake env lean -Ddebug.skipKernelTC=false CircuitReplay.lean -o .lake/build/lib/lean/CircuitReplay.olean
lake env lean -Ddebug.skipKernelTC=false ExactDegree.lean -o .lake/build/lib/lean/ExactDegree.olean
lake env lean -Ddebug.skipKernelTC=false AffineAnchor.lean -o .lake/build/lib/lean/AffineAnchor.olean
lake env lean -Ddebug.skipKernelTC=false AnchorValueShear.lean -o .lake/build/lib/lean/AnchorValueShear.olean
lake env lean -Ddebug.skipKernelTC=false Current318FinalPolynomial.lean -o .lake/build/lib/lean/Current318FinalPolynomial.olean
lake env lean -Ddebug.skipKernelTC=false Raw318FinalReplayData.lean -o .lake/build/lib/lean/Raw318FinalReplayData.olean
lake env lean -Ddebug.skipKernelTC=false Raw318FinalReplayStep0.lean -o .lake/build/lib/lean/Raw318FinalReplayStep0.olean
lake env lean -Ddebug.skipKernelTC=false Raw318FinalReplayStep1.lean -o .lake/build/lib/lean/Raw318FinalReplayStep1.olean
lake env lean -Ddebug.skipKernelTC=false Raw318FinalReplayStep2.lean -o .lake/build/lib/lean/Raw318FinalReplayStep2.olean
lake env lean -Ddebug.skipKernelTC=false Raw318FinalReplayStep3.lean -o .lake/build/lib/lean/Raw318FinalReplayStep3.olean
lake env lean -Ddebug.skipKernelTC=false Raw318FinalReplayStep4.lean -o .lake/build/lib/lean/Raw318FinalReplayStep4.olean
lake env lean -Ddebug.skipKernelTC=false Raw318FinalReplayStep5.lean -o .lake/build/lib/lean/Raw318FinalReplayStep5.olean
lake env lean -Ddebug.skipKernelTC=false Raw318FinalReplayStep6.lean -o .lake/build/lib/lean/Raw318FinalReplayStep6.olean
lake env lean -Ddebug.skipKernelTC=false Raw318FinalReplay.lean -o .lake/build/lib/lean/Raw318FinalReplay.olean
lake env lean -Ddebug.skipKernelTC=false Current318FinalBridge.lean -o .lake/build/lib/lean/Current318FinalBridge.olean
lake env lean -Ddebug.skipKernelTC=false Current318FinalExactDegree.lean -o .lake/build/lib/lean/Current318FinalExactDegree.olean
lake env lean -Ddebug.skipKernelTC=false Current318FinalAudit.lean | tee axioms-rechecked.log
python3 - <<'CHECK'
import json,re
from pathlib import Path
allowed={'propext','Classical.choice','Quot.sound'}
lines=re.sub(r'\n[ \t]+', ' ', Path('axioms-rechecked.log').read_text()).splitlines()
cfg=json.loads(Path('frozen-config.json').read_text())
assert len(lines)==cfg['auditCount']
for line in lines:
 if 'depends on axioms:' in line:assert {x.strip() for x in line.split('[',1)[1].split(']')[0].split(',')}<=allowed,line
 else:assert 'does not depend on any axioms' in line,line
print('PASS: complete concrete polynomial/raw-source equivalence and exact degree four. Source arithmetic is still an explicit hypothesis.')
CHECK
