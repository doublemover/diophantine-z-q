from pathlib import Path
import json,hashlib,re
root=Path('/workspace/scratch/2cb21e4e0864');t=root/'recovery-geometric-0358/independent-geometric-sections';o=root/'recovery-modular-0358/geometric-sections-independent-review';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();r=json.loads((t/'receipt.json').read_text());cs=[]
def ck(p,h):cs.append({'path':str(p.relative_to(root)),'expected':h,'actual':sha(p)})
ck(t/'receipt.json','b7b6a73971cd663151b1760f3957b6470b2692e0d7246ac5e67f0c1d5a675708')
for n,h in r['sha256'].items():ck(t/n,h)
for n,h in r['dependency_receipts'].items():ck(root/n,h)
ck(root/'kernel-geometric-bases-independent-review/acceptance.json','2f5a6cc0b0d078b17ef57aa66e7932f560998a8c24935a993edc44c2c13fe6dc')
assert all(c['expected']==c['actual'] for c in cs)
s=(t/'bounded-audit.log').read_text();es=re.findall(r'^AXIOM_CHECK ([^:]+): \[([^\]]*)\]',s,re.M);assert len(es)==44
assert all(set(a.strip() for a in ax.split(',') if a.strip())<={'propext','Classical.choice','Quot.sound'} for _,ax in es)
assert all(any(n==e for n,_ in es) for e in r['endpoints'])
assert 'INDEPENDENT_GEOMETRIC_SECTIONS_AUDIT_PASS declarations=44 modules=3' in s
refs=['literal-independent-pairs/LiteralKernelPrimitiveOpen318.lean','literal-independent-pairs/LiteralIndependentPairOpen318.lean','literal-independent-pairs/LiteralIndependentPairFunctor318.lean','literal-independent-pairs/F3PairIndependence318.lean','literal-kernel-group/LiteralKernelFunctor318.lean','literal-kernel-field-card/LiteralIndependentPairFinite318.lean','recovery-geometric-0358/kernel-geometric-bases/LiteralKernelGeometricBases318.lean','recovery-geometric-0358/kernel-geometric-bases/F3RankTwoBases318.lean']
r={'status':'BINDINGS_AND_RETAINED_AUDIT_CHECK_PASS_NOT_FRESH_REPLAY','hash_comparisons':len(cs),'checks':cs,'retained_declarations':44,'retained_modules':3,'all_endpoints_present':True,'read_interfaces':{n:sha(root/n) for n in refs},'no_replay':True}
(o/'checks.json').write_text(json.dumps(r,indent=2)+'\n');print('bindings',len(cs));print('checks',sha(o/'checks.json'))
