from pathlib import Path
import hashlib,json,re
root=Path('/workspace/scratch/2cb21e4e0864');target=root/'rational-group-associativity';out=root/'recovery-modular-0358/rational-associativity-independent-review'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((target/'receipt.json').read_text());checks=[]
def check(p,h):
 checks.append({'path':str(p.relative_to(root)),'expected':h,'actual':sha(p)})
check(target/'receipt.json','19686b74005a4f9c71572bafa5ee84fd5c94c8fb5bca38097d8c7b5af0ef6e6e')
for n,h in r['artifacts'].items():check(target/n,h)
for n,h in r['predecessor_receipts'].items():check(root/n,h)
for n,h in json.loads((target/'predecessor-sources.json').read_text()).items():check(root/n,h)
assert all(c['actual']==c['expected'] for c in checks)
log=(target/'AuditRationalAssociativity.log').read_text()
entries=re.findall(r'^AXIOM_CHECK ([^:]+): \[([^\]]*)\]',log,re.M)
assert len(entries)==105
allowed={'propext','Quot.sound','Classical.choice'}
assert all(set(x.strip() for x in axs.split(',') if x.strip())<=allowed for _,axs in entries)
assert all(any(n==e for n,_ in entries) for e in r['endpoints'])
assert 'RATIONAL_GROUP_ASSOCIATIVITY_AUDIT_PASS declarations=105 modules=10' in log
order=(target/'module-order.txt').read_text().splitlines();assert len(order)==10
for n in order:assert not re.search(r'\b(sorry|admit|axiom)\b',(target/(n+'.lean')).read_text())
P=root/'diophantine-z-q/quartics/quartic-318-326/proof/progress';ML=P/'.lake/packages/mathlib/Mathlib'
extra=[P/(n+'.lean') for n in ['LiteralWeierstrassPoints318','CompletedIntegral318','FinitePairCover318','AffineProductEvaluation318','CompletedAdditionTriple318','CompletedAdditionRestrictions318','CompletedAdditionUnits318']]
extra += [ML/n for n in ['AlgebraicGeometry/EllipticCurve/Affine/Point.lean','AlgebraicGeometry/Morphisms/Separated.lean','AlgebraicGeometry/Geometrically/Reduced.lean','AlgebraicGeometry/Morphisms/Flat.lean']]
res={'status':'BINDINGS_AND_RETAINED_AUDIT_CHECK_PASS_NOT_FRESH_REPLAY','hash_comparisons':len(checks),'checks':checks,'retained_declarations':len(entries),'retained_modules':10,'all_endpoints_present':True,'source_placeholders_found':False,'additional_read_sources':{str(p.relative_to(root)):sha(p) for p in extra},'no_replay':True}
(out/'checks.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps({'bindings':len(checks),'retained_declarations':len(entries),'retained_modules':10,'checks_sha256':sha(out/'checks.json')}))
