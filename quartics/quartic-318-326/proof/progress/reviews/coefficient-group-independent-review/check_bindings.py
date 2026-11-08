from pathlib import Path
import hashlib,json,re
root=Path('/workspace/scratch/2cb21e4e0864'); target=root/'coefficient-group-transport'
checks=[]
def check(path,want,kind):
    got=hashlib.sha256(path.read_bytes()).hexdigest()
    checks.append({'path':str(path.relative_to(root)),'kind':kind,'expected':want,'actual':got,'pass':got==want})
check(target/'receipt.json','26696b066b4f787178533cf5db4285667b7d1f0dae0d63bea6c7c2bd1b958096','target receipt')
check(target/'PUBLIC-ARTIFACTS.json','96956c05bd28287a4d37c01cce2906a19bf3b1902a13a0795f535cd3a236a67f','public manifest')
r=json.loads((target/'receipt.json').read_text())
for n,h in r['artifacts'].items(): check(target/n,h,'target artifact')
for n,h in r['predecessor_receipts'].items(): check(root/n,h,'predecessor receipt')
for n,h in r['published_predecessor_source_hashes'].items(): check(root/n,h,'published predecessor source')
p=json.loads((target/'PUBLIC-ARTIFACTS.json').read_text())
assert set(p['public_whitelist']) == set(p['sha256'])|{'PUBLIC-ARTIFACTS.json'}
for n,h in p['sha256'].items(): check(target/n,h,'public whitelist artifact')
a=(target/'AuditCoefficientGroup.log').read_text()
assert 'COEFFICIENT_GROUP_AUDIT_PASS declarations=100 modules=4' in a
lines=[x for x in a.splitlines() if x.startswith('AXIOM_CHECK ')]
assert len(lines)==100
allowed={'propext','Classical.choice','Quot.sound'}
for line in lines:
    v=line.rsplit(': [',1)[1].removesuffix(']')
    assert set(filter(None,v.split(', ')))<=allowed
assert all(c['pass'] for c in checks)
extra=[root/'completed-coefficient-base-change'/n for n in ['CompletedCoefficientProduct318.lean','CompletedAdditionCoefficient318.lean']]
P=root/'diophantine-z-q/quartics/quartic-318-326/proof/progress'
extra += [P/(n+'.lean') for n in ['WeierstrassBaseChange318','WeierstrassCoefficientMap318','ChartNegation318','GluedNegation318','LiteralSchemePointOperations318','LiteralSchemePointAssociativity318','LiteralSchemePointGroup318','LiteralGroupAssociativity318','CompletedAdditionTriple318','SchematicEqualityExtension318','FiniteProductSchematicDensity318']]
extra += [P/'.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/IsPullback/Defs.lean']
extra += [root/'recovery-geometric-0358/coefficient-square-independent-review'/n for n in ['acceptance.json','REVIEW.md']]
out={'status':'PASS exact artifact and predecessor bindings; retained audit read, no replay','binding_checks':len(checks),'checks':checks,'retained_audit_declarations':len(lines),'retained_audit_modules':4,'additional_read_sources':{str(f.relative_to(root)):hashlib.sha256(f.read_bytes()).hexdigest() for f in extra}}
dest=root/'recovery-modular-0358/coefficient-group-independent-review/checks.json'
dest.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'binding_checks':len(checks),'all_pass':True,'retained_declarations':len(lines),'read_sources':len(extra)}))
