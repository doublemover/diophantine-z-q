from pathlib import Path
import json, hashlib, re
root=Path('/workspace/scratch/2cb21e4e0864')
t=root/'recovery-hodge-0358/character-invariant-pullback'
o=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((t/'receipt.json').read_text()); a=json.loads((t/'APPLICATION.json').read_text()); cs=[]
def ck(p,h):
 cs.append({'path':str(p.relative_to(root)),'expected':h,'actual':sha(p)})
ck(t/'receipt.json','cd6a34418b8dc2fdcb6ce6aa32247857590037c47e1e6d80f012fa61b20d8866')
ck(t/'APPLICATION.json','6648299480887a9518a215cfa3964d1e0367dfc0757a8304cf8947841cc5019e')
for n,h in a['sources'].items():ck(t/n,h)
for d in a['direct_dependencies'].values():ck(root/d['path'],d['sha256'])
for n,h in a['predecessor_receipts'].items():ck(root/n,h)
assert all(c['expected']==c['actual'] for c in cs)
for n,v in r['strict_checks'].items():
 assert v['source_sha256']==a['sources'][n+'.lean']
 assert v['success_marker'] in (t/v['log']).read_text()
s=(t/'audit-run.log').read_text();es=re.findall(r'^AXIOM_CHECK ([^:]+): \[([^\]]*)\]',s,re.M)
assert len(es)==76 and len({n for n,_ in es})==76
assert all(set(x.strip() for x in ax.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'} for _,ax in es)
assert all(any(n==e for n,_ in es) for e in a['endpoints'])
assert 'CHARACTER_DIFFERENTIAL_AUDIT_PASS declarations=76 modules=11' in s and 'RESULT Audit 0' in s
p=root/'diophantine-z-q/quartics/quartic-318-326/proof/progress'
refs=['UniversalSheafDifferentials318.lean','IntrinsicChartNormalization318.lean','IntrinsicChartSections318.lean','IntrinsicGlobalFrame318.lean','FiniteInvariantDifferential318.lean','InvariantChartForms318.lean','InvariantChartCover318.lean','ShortAffineJacobian318.lean','KaehlerAdditiveExt318.lean','CompletedCharacterSchemeMaps318.lean','SourceCharacterAlgebra318.lean','AlgHomDifferential318.lean','.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Modules/Sheaf.lean']
result={'status':'BINDINGS_AND_RETAINED_AUDIT_PASS_NO_REPLAY','hash_comparisons':len(cs),'checks':cs,'retained_strict_sources':11,'retained_declarations':76,'retained_modules':11,'all_endpoints_present':True,'read_interfaces':{str((p/n).relative_to(root)):sha(p/n) for n in refs},'evidence_sha256':{n:sha(t/n) for n in ['Audit.lean','audit-run.log','MODULE_ORDER.txt','README.md','SHA256SUMS']},'strict_logs_sha256':{n:sha(t/n) for n in sorted({v['log'] for v in r['strict_checks'].values()})},'no_replay':True}
(o/'checks.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS',len(cs),'bindings; eleven strict markers; 76 audited declarations; all endpoints')
