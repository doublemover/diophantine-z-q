from pathlib import Path
import json,hashlib
root=Path('/workspace/scratch/2cb21e4e0864');t=root/'recovery-contact-0358/source-order-full-inertia';o=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();cs=[]
def ck(p,h):cs.append({'path':str(p.relative_to(root)),'expected':h,'actual':sha(p)})
r=json.loads((t/'receipt.json').read_text());ck(t/'receipt.json','18ec3c0aff98cdec9132339392d56485a4fcab0202ff0499f4b19b406a5816b7')
for n,h in r['artifacts'].items():ck(t/n,h)
for n,h in r['predecessor_receipts'].items():ck(root/n,h)
for n,h in r['exact_dependencies'].items():ck(root/n,h)
ck(root/'recovery-modular-0358/branch-inertia-independent-review/acceptance.json','29922b195d6b635ab0d0e5febbc7907b42c9041c5609728fb991673b9f903f50')
for v in r['validation']:
 ck(t/(v['module']+'.lean'),v['source_sha256']);s=(t/v['log']).read_text();assert 'PASS '+v['module'] in s and 'exit=0' in s and 'error:' not in s;assert v['kernel_check']=='debug.skipKernelTC=false'
assert all(v['actual']==v['expected'] for v in cs)
refs=['diophantine-z-q/quartics/quartic-318-326/proof/progress/SourceKummerField318.lean','diophantine-z-q/quartics/quartic-318-326/proof/progress/TensorFractionField318.lean','recovery-contact-0358/contact-global-signs/SourceSignFieldComparison318.lean','checkpoint-global-sign-action/frozen/FourRootOrderSignAction318.lean']
z={'status':'SOURCE_BINDINGS_AND_TWO_RETAINED_STRICT_PASS_MARKERS_VERIFIED_NO_REPLAY','hash_comparisons':len(cs),'checks':cs,'read_additional_interfaces':{n:sha(root/n) for n in refs},'combined_recursive_audit':'pending in target receipt','no_replay':True}
(o/'checks.json').write_text(json.dumps(z,indent=2)+'\n');print('PASS',len(cs),'bindings; two strict markers; recursive audit remains pending')
