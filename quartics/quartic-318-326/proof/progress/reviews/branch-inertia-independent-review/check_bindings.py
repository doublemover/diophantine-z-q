from pathlib import Path
import json,hashlib
root=Path('/workspace/scratch/2cb21e4e0864');o=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();cs=[]
def ck(p,h):cs.append({'path':str(p.relative_to(root)),'expected':h,'actual':sha(p)})
targets={'contact-branch-stabilizer':'3f06389eb5fe17b87a0f5ca691d753f7eeeeaf5a450698cf666b3a15d7a93b36','contact-branch-residue-inertia':'c663c817ec00444b23c77cf27782158f658dbb22d59857d90b2fe85c5efa3faf'};logs=[]
for name,h in targets.items():
 p=root/'recovery-contact-0358'/name;r=json.loads((p/'receipt.json').read_text());ck(p/'receipt.json',h)
 for n,h in r['artifacts'].items():ck(p/n,h)
 for n,h in r['predecessor_receipts'].items():ck(root/n,h)
 for v in r.get('direct_and_consumed_dependencies',{}).values():ck(root/v['path'],v['sha256'])
 for n,h in r.get('mathlib_definitions',{}).items():ck(root/n,h)
 for v in r['validation']:
  ck(p/(v['module']+'.lean'),v['source_sha256']);s=(p/v['log']).read_text();assert 'RELEASED ' in s and 'exit=0' in s and 'error:' not in s
  assert v['kernel_check']=='debug.skipKernelTC=false';logs.append({'module':v['module'],'log':str((p/v['log']).relative_to(root)),'exit_marker_verified':True,'kernel_flag_attested_by_receipt':True})
assert all(v['actual']==v['expected'] for v in cs)
refs=['recovery-contact-0358/contact-global-signs/SourceSignFieldComparison318.lean','recovery-contact-0358/contact-global-signs/FourRootOrderSigns318.lean','recovery-contact-0358/contact-global-signs/FourRootSignBaseChange318.lean','checkpoint-global-sign-action/frozen/ContactGlobalSignFaithful318.lean','diophantine-z-q/quartics/quartic-318-326/proof/progress/SourceOpenFractionField318.lean']
refs += ['diophantine-z-q/quartics/quartic-318-326/proof/progress/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/GammaSpecAdjunction.lean','diophantine-z-q/quartics/quartic-318-326/proof/progress/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Defs.lean']
result={'status':'SOURCE_BINDINGS_AND_RETAINED_STRICT_EXIT_LOGS_PASS_NO_REPLAY','hash_comparisons':len(cs),'checks':cs,'strict_modules':logs,'read_additional_predecessors':{n:sha(root/n) for n in refs},'combined_recursive_audit':'Pending in both target receipts; no audit pass inferred','no_replay':True}
(o/'checks.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS',len(cs),'bindings; six strict exit logs; no recursive audit claim')
