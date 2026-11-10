#!/usr/bin/env python3
"""Preserve predecessor-bound tests; new source repair checked separately."""
from pathlib import Path
import runpy,json
H=Path(__file__).resolve().parent;O=H.parent/'forward-prime-local-density-r1'
d=json.loads((O/'intake.json').read_text())
for n in d['order']:
 if n!='FormalPoleCoherentChart318': assert (H/(n+'.lean')).read_bytes()==(O/(n+'.lean')).read_bytes(),n
assert (H/'FormalPoleCoherentChart318.lean').read_bytes()!=(O/'FormalPoleCoherentChart318.lean').read_bytes()
print('PASS248 exact density249r1 source copies;one narrow hosted proof repair')
runpy.run_path(str(Path(__file__).resolve().parent.parent/'forward-prime-local-density-r1'/'check_sieve_density.py'),run_name='__main__')
