from pathlib import Path
import json,hashlib,re
root=Path('/workspace/scratch/2cb21e4e0864');t=root/'recovery-geometric-0358/universal-kernel-basis';o=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();r=json.loads((t/'receipt.json').read_text());m=json.loads((t/'source-manifest.json').read_text());cs=[]
def ck(p,h):cs.append({'path':str(p.relative_to(root)),'expected':h,'actual':sha(p)})
ck(t/'receipt.json','684608da1647ccfd67b15a01bdb01033d26cc27112b549c3dc3114dd36409107')
for n,h in r['sha256'].items():ck(t/n,h)
for n,h in r['dependency_receipts'].items():ck(root/n,h)
math=root/'diophantine-z-q/quartics/quartic-318-326/proof/progress/.lake/packages/mathlib'
for n,h in m['mathlib_sources'].items():ck(math/n,h)
for n,h in m['project_sources'].items():ck(root/n,h)
ck(root/'independent-pair-rank-independent-review/acceptance.json','a3fb0b8e3c5f222edb51ca85220a81efa285df9cc72853cd531f346adf141cec')
ck(root/'recovery-modular-0358/geometric-sections-independent-review/acceptance.json','ad53731b39f73f7b32efd3c8e05e6f78609f9a9a12e404591fd0fe881b5c3ade')
assert all(c['expected']==c['actual'] for c in cs)
s=(t/'bounded-audit.log').read_text();es=re.findall(r'^AXIOM_CHECK ([^:]+): \[([^\]]*)\]',s,re.M)
assert len(es)==72 and len({n for n,_ in es})==72
assert all(set(x.strip() for x in ax.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'} for _,ax in es)
assert all(any(n==e for n,_ in es) for e in r['endpoints'])
assert 'UNIVERSAL_KERNEL_BASIS_AUDIT_PASS declarations=72 modules=4' in s
f=(t/'full-check.log').read_text();assert all('CHECK '+n in f for n in r['modules']) and 'error:' not in f
refs=['recovery-geometric-0358/independent-geometric-sections/LiteralIndependentGeometricBases318.lean','recovery-geometric-0358/independent-pair-rank/LiteralIndependentPairRank318.lean','literal-kernel-group/LiteralKernelSchemePoints318.lean','literal-kernel-group/LiteralKernelScalar318.lean']
extra=['Mathlib/AlgebraicGeometry/PullbackCarrier.lean','Mathlib/AlgebraicGeometry/Morphisms/UnderlyingMap.lean']
result={'status':'BINDINGS_AND_RETAINED_STRICT_AUDIT_PASS_NO_REPLAY','hash_comparisons':len(cs),'checks':cs,'retained_declarations':72,'retained_modules':4,'all_endpoints_present':True,'read_additional_interfaces':{n:sha(root/n) for n in refs}|{str((math/n).relative_to(root)):sha(math/n) for n in extra},'read_full_check_log_sha256':sha(t/'full-check.log'),'no_replay':True}
(o/'checks.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS',len(cs),'bindings; retained72/4 audit')
