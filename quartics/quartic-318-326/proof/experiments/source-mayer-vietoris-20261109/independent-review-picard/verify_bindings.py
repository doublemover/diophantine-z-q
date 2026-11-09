from pathlib import Path
import hashlib,json,subprocess,re
p=Path(__file__).resolve().parent.parent;r=p.parents[4]
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
receipt=json.loads((p/'receipt.json').read_text());app=json.loads((p/'APPLICATION.json').read_text());intake=json.loads((p/'intake.json').read_text());policy=json.loads((p/'source-policy.json').read_text())
assert sha(p/'receipt.json')=='2cab8b5d51ca799efd3fdb3c4d212ff10cb1bc10e91d68f2ad1ac97f2528a816'
assert sha(p/'APPLICATION.json')==receipt['application_sha256']=='13645a5b6a53d99dbd7ee6d36b688361937ec8cc64f387646222b682474233c1'
assert len(receipt['new_modules'])==7 and len(receipt['modules'])==30
for name,digest in receipt['source_hashes'].items():
 assert sha(p/name)==digest==app['sources'][name]==intake['files'][name]['sha256']
for name,digest in receipt['evidence_hashes'].items():assert sha(p/name)==digest,name
for name,digest in receipt['compiled_artifacts'].items():assert sha(p/name)==digest,name
for line in (p/'SHA256SUMS').read_text().splitlines():
 digest,name=line.split(maxsplit=1);assert sha(p/name)==digest,name
copies=0
for q in json.loads((p/'COPY_BINDINGS.json').read_text()):
 pred=p.parent/q['packet'];assert sha(pred/'receipt.json')==q['receipt_sha256'];assert sha(pred/'APPLICATION.json')==q['application_sha256']
 for name,digest in q['sources'].items():assert sha(pred/name)==sha(p/name)==digest;copies+=1
assert copies==23
prefix='quartics/quartic-318-326/proof/progress/'
manifest=json.loads(subprocess.check_output(['git','show',policy['baseline_commit']+':'+prefix+'checkpoint-manifest.json'],cwd=r,text=True))
base=policy['required_predecessor_sources']
for name,digest in base.items():
 module=Path(name).stem;source=r/prefix/(module+'.lean')
 assert sha(source)==digest==manifest['modules'][module]['sha256'],name
assert len(base)==428
log=(p/'logs/strict-replay.log').read_text()
assert 'FINAL_EXIT=0' in log and 'SOURCE_MAYER_VIETORIS_AUDIT_PASS declarations=321 modules=30' in log
assert 'error:' not in log and 'warning:' not in log
assert re.findall(r'^STRICT_PASS (\S+)$',log,re.M)==receipt['modules']
assert len(re.findall(r'^AXIOM_CHECK ',log,re.M))==321
upstream={}
m=r/prefix/'.lake/packages/mathlib/Mathlib'
for path in ['CategoryTheory/Sites/SheafCohomology/Basic.lean','CategoryTheory/Sites/SheafCohomology/MayerVietoris.lean','CategoryTheory/Sites/MayerVietorisSquare.lean']:
 upstream[path]=sha(m/path)
result={'status':'PASS','reviewer':'/root/resume_relative_picard','producer_receipt_sha256':sha(p/'receipt.json'),'application_sha256':sha(p/'APPLICATION.json'),'intake_sha256':sha(p/'intake.json'),'source_files_verified':30,'new_modules':receipt['new_modules'],'exact_copied_predecessors':copies,'baseline_pins_verified_against_original_commit_manifest_and_current_sources':len(base),'producer_artifact_hashes_verified':len(receipt['compiled_artifacts']),'producer_evidence_hashes_verified':len(receipt['evidence_hashes']),'producer_replay_verified':30,'producer_private_inclusive_audit_declarations':321,'reviewer_fresh_replay':False,'reviewer_new_axiom_audit':False,'primary_library_sources_read':upstream,'source_hashes':receipt['source_hashes']}
(p/'independent-review-picard/bindings.json').write_text(json.dumps(result,indent=2)+'\n')
print('REVIEW_BINDINGS_PASS sources=30 new=7 copies=23 baseline=428 artifacts=150 producer_audit=321 reviewer_replay=0')
