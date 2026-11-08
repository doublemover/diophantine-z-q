from pathlib import Path
import hashlib,json
b=Path('/workspace/scratch/2cb21e4e0864');p=b/'norm-line-object-gauge-independent-review'
def sh(q):return hashlib.sha256(q.read_bytes()).hexdigest()
expected={'recovery-geometric-0358/fifth-norm-line-object/receipt.json':'dc3b2cb74826654a1d1c22931fdb80888362b3814d568a2fae2f17237ee8af27','recovery-geometric-0358/norm-cocycle-gauge/receipt.json':'6c47c822b9f6b33d060f588fd4c665bf1bb028b48880788e1b7cc73240addce7'}
bind={}
for r,h in expected.items():
 q=b/r;assert sh(q)==h,(r,'receipt mismatch');bind[r]=h
 d=json.loads(q.read_text())
 for n,hh in d['artifacts'].items():
  path=q.parent/n;assert sh(path)==hh,(str(path),'artifact mismatch');bind[str(path.relative_to(b))]=hh
 for n,hh in d['dependency_receipts'].items():
  assert sh(b/n)==hh,(n,'dependency mismatch');bind[n]=hh
assert 'FIFTH_NORM_LINE_OBJECT_AUDIT_PASS declarations=19 modules=2' in (b/'recovery-geometric-0358/fifth-norm-line-object/fifth-norm-line-object-audit.log').read_text()
assert 'NORM_COCYCLE_GAUGE_AUDIT_PASS declarations=32 modules=3' in (b/'recovery-geometric-0358/norm-cocycle-gauge/norm-gauge-audit-transport-check1.log').read_text()
extra=['recovery-geometric-0358/line-frame-reconstruction/LineFrameReconstructionIso318.lean','recovery-geometric-0358/fifth-character-work/OpenClutchedGauge318.lean','checkpoint-cocycle-lines-work/CocycleModule318.lean','checkpoint-unit-cocycles/FifthNormCocycle318.lean','resumed-completed-addition/InverseImageLineCocycle318.lean','resumed-completed-addition/LineFrameGauge318.lean']
for n in extra:bind[n]=sh(b/n)
(p/'BINDINGS.json').write_text(json.dumps(bind,indent=2)+'\n')
print('PASS',len(bind),'exact bindings; candidate target audit counts19/2 and32/3 retained, no replay')
