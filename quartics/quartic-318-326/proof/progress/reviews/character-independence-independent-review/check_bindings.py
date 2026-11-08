from pathlib import Path
import json,hashlib,re
root=Path('/workspace/scratch/2cb21e4e0864');t=root/'recovery-hodge-0358/character-differential-independence';o=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();r=json.loads((t/'receipt.json').read_text());a=json.loads((t/'APPLICATION.json').read_text());cs=[]
def ck(p,h):cs.append({'path':str(p.relative_to(root)),'expected':h,'actual':sha(p)})
ck(t/'receipt.json','3c417c846f4f30ac0433247e4626aa88ceec055a5ae2c176bee08b2498b48b14')
for n,h in r['files'].items():ck(t/n,h)
for n,h in a['sources'].items():ck(t/n,h)
for v in a['direct_dependencies'].values():ck(root/v['path'],v['sha256'])
for n,h in a['consuming_joins'].items():ck(root/n,h)
for n,h in a['predecessor_receipts'].items():ck(root/n,h)
assert all(c['expected']==c['actual'] for c in cs)
s=(t/'audit-run.log').read_text();es=re.findall(r'^AXIOM_CHECK ([^:]+): \[([^\]]*)\]',s,re.M)
assert len(es)==134 and len({n for n,_ in es})==134
assert all(set(x.strip() for x in ax.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'} for _,ax in es)
assert all(any(n==e for n,_ in es) for e in a['endpoints'])
assert 'CHARACTER_DIFFERENTIAL_INDEPENDENCE_AUDIT_PASS declarations=134 modules=6' in s
for n,v in r['strict_checks'].items():
 assert v['success_marker'] in (t/v['log']).read_text()
 assert sha(t/(n+'.lean'))==v['source_sha256']
math='diophantine-z-q/quartics/quartic-318-326/proof/progress/.lake/packages/mathlib/'
refs=['diophantine-z-q/quartics/quartic-318-326/proof/progress/EtaleDifferentialFrame318.lean', math+'Mathlib/RingTheory/Etale/Kaehler.lean',math+'Mathlib/RingTheory/Kaehler/Polynomial.lean']
result={'status':'BINDINGS_AND_RETAINED_STRICT_AUDIT_PASS_NO_REPLAY','hash_comparisons':len(cs),'checks':cs,'retained_declarations':134,'retained_modules':6,'all_endpoints_present':True,'all_strict_markers_present':True,'additional_read_interfaces':{n:sha(root/n) for n in refs},'no_replay':True}
(o/'checks.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS',len(cs),'bindings; retained 134/6 audit; all eight endpoints and six strict markers present')
