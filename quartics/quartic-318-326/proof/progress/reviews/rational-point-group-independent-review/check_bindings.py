from pathlib import Path
import hashlib,json,re
root=Path('/workspace/scratch/2cb21e4e0864');target=root/'rational-scheme-point-group';out=root/'recovery-modular-0358/rational-point-group-independent-review';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();r=json.loads((target/'receipt.json').read_text());checks=[]
def check(p,h):checks.append({'path':str(p.relative_to(root)),'expected':h,'actual':sha(p)})
check(target/'receipt.json','91b320f4d6af684385416ea62c9c5ac55be2ae77dce7ab4d45c483e09db3add6')
for n,h in r['artifacts'].items():check(target/n,h)
for n,h in r['predecessor_receipts'].items():check(root/n,h)
check(root/'recovery-modular-0358/rational-associativity-independent-review/acceptance.json','24aef56068bfbf7cf9623f19d273d413567bc3dc7db3de9e4c512b8f84b7c52a')
assert all(x['expected']==x['actual'] for x in checks)
log=(target/'AuditRationalPointGroup.log').read_text();entries=re.findall(r'^AXIOM_CHECK ([^:]+): \[([^\]]*)\]',log,re.M);assert len(entries)==71
assert all(set(x.strip() for x in a.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'} for _,a in entries)
assert all(any(n==e for n,_ in entries) for e in r['endpoints'])
assert 'RATIONAL_SCHEME_POINT_GROUP_AUDIT_PASS declarations=71 modules=3' in log
P=root/'diophantine-z-q/quartics/quartic-318-326/proof/progress'
refs=[P/(n+'.lean') for n in ['CompletedAdditionTriple318','CompletedAdditionUnits318','CompletedAdditionInverse318','CompletedLeftInverse318','CompletedAdditionCommutative318','GluedNegation318']]+[root/'rational-group-associativity/RationalGroupAssociativity318.lean']
res={'status':'BINDINGS_AND_RETAINED_AUDIT_CHECK_PASS_NOT_FRESH_REPLAY','hash_comparisons':len(checks),'checks':checks,'retained_declarations':71,'retained_modules':3,'all_endpoints_present':True,'read_interfaces':{str(p.relative_to(root)):sha(p) for p in refs},'prior_acceptance_unchanged':True,'no_replay':True}
(out/'checks.json').write_text(json.dumps(res,indent=2)+'\n');print('bindings',len(checks));print('checks',sha(out/'checks.json'))
