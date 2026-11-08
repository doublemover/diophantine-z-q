from pathlib import Path
import json,hashlib
root=Path('/workspace/scratch/2cb21e4e0864');t=root/'recovery-contact-0358/character-boolean-quotient';o=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();r=json.loads((t/'receipt.json').read_text());cs=[]
def ck(p,h):cs.append({'path':str(p.relative_to(root)),'expected':h,'actual':sha(p)})
ck(t/'receipt.json','a9c265868f3d98845764ba3708011650897cb78dd35a500a4c629ebec91ecc2d')
for n,h in r['artifacts'].items():ck(t/n,h)
for n,h in r['predecessor_receipts'].items():ck(root/n,h)
for v in r['direct_and_consumed_dependencies'].values():ck(root/v['path'],v['sha256'])
assert all(c['expected']==c['actual'] for c in cs)
assert all(v['source_sha256']==sha(t/(v['module']+'.lean')) for v in r['validation'])
assert 'exit=0' in (t/'check-77.log').read_text() and 'exit=0' in (t/'check-81.log').read_text()
assert 'PASS CharacterBooleanKernel318' in (t/'check-80.log').read_text()
assert 'CharacterBooleanAffine318.lean:' in (t/'check-76.log').read_text()
assert not any('CharacterBooleanAffine318.lean:' in line and 'error:' in line for line in (t/'check-76.log').read_text().splitlines())
refs=['recovery-contact-0358/character-sign-equivariance/CharacterSignAffine318.lean','recovery-contact-0358/character-sign-equivariance/CharacterSignGlobal318.lean','recovery-contact-0358/contact-global-signs/SourceSignFieldComparison318.lean','recovery-contact-0358/contact-global-signs/ContactGlobalSigns318.lean','recovery-contact-0358/character-quotient-point-group/CharacterQuotientPointGroup318.lean']
p='diophantine-z-q/quartics/quartic-318-326/proof/progress/'
refs += [p+n+'.lean' for n in ['CompletedCharacterInfinity318','CompletedNormalizationIso318','CompletedIsoOperations318','CharacterQuotientOperations318','SchematicEqualityExtension318']]
res={'status':'EXACT_BINDINGS_AND_RETAINED_SOURCE_EVIDENCE_READ_NO_REPLAY','hash_comparisons':len(cs),'checks':cs,'retained_strict_sources':4,'affine_log_qualification':'Producer receipt binds final source/olean; check-76 is sequential and shows the later global module failure, not an explicit standalone affine PASS marker. No missing standalone audit is inferred.','combined_recursive_audit':'pending hosted CI; no PASS claimed','read_interfaces':{n:sha(root/n) for n in refs},'no_replay':True}
(o/'checks.json').write_text(json.dumps(res,indent=2)+'\n');print('PASS',len(cs),'bindings')
