from pathlib import Path
import json,hashlib,shutil
B=Path('/workspace/scratch/41c6d5925c0e');O=B/'review43603177874';P=B/'geometry-run43603177874/successors/height-normalized-valuative-center-r69';Q=P/'RECONSTRUCTED-REVIEWED-EVIDENCE';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((Q/'RECONSTRUCTION.json').read_text());old=json.loads((O/'GEOMETRY-PROPAGATION-BINDINGS.json').read_text())['packets'][0];cur=json.loads((P/'APPLICATION.json').read_text())
assert sha(P/'APPLICATION.json')==m['current_application_sha256']=='da1f9308bfe51c04aea91d437bd089582ee08755ad7ca17eea5b2a0914031c04'
assert (Q/'CURRENT-INPUT-APPLICATION.json').read_bytes()==(P/'APPLICATION.json').read_bytes()
assert m['reviewed_application_sha256']==old['application_sha256']=='b5183c4ab89210a9d346d5cbeb98c6349112ec65027f98eae2904bf8892f7a4a'
assert sha(P/'PROPAGATION-REVIEWED-APPLICATION.json')==old['application_sha256']
for n,h in m['evidence'].items():assert sha(Q/n)==h
assert m['historical_storage_retrieved'] is False and m['library_history_mutated'] is False and m['local_lean_run'] is False
for n,row in m['receipts'].items():
 before=Q/row['reconstructed_path'];after=Q/('CURRENT-INPUT-'+n)
 assert after.read_bytes()==(P/n).read_bytes();assert sha(after)==row['current_input_sha256'];assert sha(before)==row['reconstructed_sha256']==row['historically_reviewed_sha256']==old['application_bindings'][n]
 a=json.loads(before.read_text());b=json.loads(after.read_text());assert [k for k in a.keys()|b.keys() if a.get(k)!=b.get(k)]==['propagation_review'];assert a['propagation_review']=='PENDING' and b['propagation_review']=='PASS_SOURCE_AND_CONTRACT_ONLY_HOSTED_PENDING'
 a['propagation_review']=b['propagation_review'];assert (json.dumps(a,indent=2)+'\n').encode()==after.read_bytes()
 b['propagation_review']='PENDING';assert (json.dumps(b,indent=2)+'\n').encode()==before.read_bytes()
assert sha(P/'intake.json')==old['intake_sha256'] and sha(P/'README.md')==old['readme_sha256']
assert {p.name:sha(p) for p in P.glob('*.lean')}==old['source_sha256']
raw=json.loads((P/'PROPAGATION-REVIEWED-APPLICATION.json').read_text());obs=json.loads(json.dumps(cur['obligations']))
for ob in obs:ob.pop('independent_review',None)
assert obs==raw['obligations']
for fn,h in cur['bindings'].items():assert sha(P/fn)==h
for n in ['build_successor.py','finalize_center.py','reconstruct_reviewed_receipts.py']:assert (Q/n).read_bytes()==(B/'geometry-run43603177874'/n).read_bytes()
assert "'propagation_review':'PENDING'" in (Q/'build_successor.py').read_text();assert "q['propagation_review']='PASS_SOURCE_AND_CONTRACT_ONLY_HOSTED_PENDING'" in (Q/'finalize_center.py').read_text()
snap=O/'center-history-snapshots';snap.mkdir(exist_ok=True)
for p in Q.iterdir():
 if p.is_file():shutil.copy2(p,snap/p.name)
for n in ['GEOMETRY-PROPAGATION-BINDINGS.json','GEOMETRY-PROPAGATION-REVIEW.md']:
 shutil.copy2(O/n,snap/n)
shutil.copy2(O/'CURRENT-INDEX-CHECK.log',O/'CURRENT-INDEX-PRE-HISTORY-CORRECTION-CHECK.log')
d={'status':'PASS_EXACT_HASH_VERIFIED_RECONSTRUCTION_NOT_RETRIEVED_ORIGINALS','packet':P.name,'current_application_sha256':sha(P/'APPLICATION.json'),'reviewed_application_sha256':old['application_sha256'],'reconstruction_manifest_sha256':sha(Q/'RECONSTRUCTION.json'),'receipts':m['receipts'],'intake_sha256':sha(P/'intake.json'),'readme_sha256':sha(P/'README.md'),'source_sha256':old['source_sha256'],'obligation_prose_unchanged':True,'current_receipts_unchanged':True,'historical_storage_retrieved':False,'library_history_mutated':False,'local_lean_run':False,'kernel_acceptance':False,'evidence':{str(p.relative_to(B)):sha(p) for p in snap.iterdir() if p.is_file()}}
(O/'CENTER-HISTORY-CHECK.json').write_text(json.dumps(d,indent=2)+'\n');print('PASS: two reconstructed reviewed hashes equal prior independent bindings; one existing value reversed, exact forward roundtrip, current source/intake/README/receipt bytes unchanged. Not retrieved originals.')
