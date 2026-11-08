from pathlib import Path
import hashlib,json
root=Path('/workspace/scratch/2cb21e4e0864')
p=root/'recovery-geometric-0358/three-torsion-base-change'
checks=[]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check(p,want,kind):
 got=sha(p);checks.append({'path':str(p.relative_to(root)),'kind':kind,'expected':want,'actual':got,'pass':want==got})
check(p/'receipt.json','59966dcf48fda9837b15a6a2c99f703166b33ec1846a7f6a85bed8b2bf6fcfc6','target receipt')
r=json.loads((p/'receipt.json').read_text())
for f,h in r['sha256'].items():check(p/f,h,'target public artifact')
for f,h in r['dependency_receipts'].items():check(root/'recovery-geometric-0358'/f/'receipt.json',h,'predecessor receipt')
assert all(c['pass'] for c in checks)
a=(p/'bounded-audit.log').read_text();lines=[s for s in a.splitlines() if s.startswith('AXIOM_CHECK ')]
assert len(lines)==67 and 'THREE_TORSION_BASE_CHANGE_AUDIT_PASS declarations=67 modules=3' in a
for l in lines:
 v=l.rsplit(': [',1)[1].removesuffix(']');assert set(filter(None,v.split(', ')))<={'propext','Classical.choice','Quot.sound'}
for endpoint in r['endpoints']: assert any(l.startswith('AXIOM_CHECK '+endpoint+':') for l in lines)
P=root/'diophantine-z-q/quartics/quartic-318-326/proof/progress'
extra=[P/(n+'.lean') for n in ['ThreeTorsionAlgebra318','ThreeTorsionFunctor318','ThreeTorsionScheme318','ThreeTorsionCompletedDoubling318','WeierstrassCoefficientMap318']]
extra += [root/'recovery-geometric-0358/kernel-base-change/CompletedKernelBaseChange318.lean',P/'.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Pullbacks.lean']
report={'status':'PASS exact bindings and retained audit evidence; no replay','binding_checks':len(checks),'checks':checks,'retained_audit_declarations':67,'retained_audit_modules':3,'required_endpoints_present':r['endpoints'],'additional_read_sources':{str(f.relative_to(root)):sha(f) for f in extra},'unhashed_public_file_binding':{'SHA256SUMS':sha(p/'SHA256SUMS')}}
d=root/'recovery-modular-0358/primitive-base-change-independent-review';(d/'checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(len(checks),'exact binding checks passed')
