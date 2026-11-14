from pathlib import Path
import json,hashlib,shutil
B=Path(__file__).resolve().parent;V=B.parent/'review43592150561';F='HOSTED-43593737114';p=B/'successors/height-normalized-valuative-center-r67';ed=p/F;H=lambda f:hashlib.sha256(f.read_bytes()).hexdigest();W=lambda f,d:f.write_text(json.dumps(d,indent=2)+'\n')
expected={'GEOMETRY-FIVECHART-SOURCE-REVIEW.md':'3be229407ab2ac51e018f548e52cf65e0f65d5ddc58b3b4027bd63c08af466c5','GEOMETRY-FIVECHART-SOURCE-BINDINGS.json':'61b065eef07de80a1b6476847bec9c5de12a3daa1cff4b94c2f5bb520f57aeb0'}
for n,h in expected.items():assert H(V/n)==h
manifest=json.loads((V/'GEOMETRY-FIVECHART-SOURCE-BINDINGS.json').read_text());files={**manifest['source_bindings'],**expected}
intake,readme=H(p/'intake.json'),H(p/'README.md');snap=ed/'SOURCE-REVIEW-PRE-BIND-APPLICATION.json';assert not snap.exists();assert H(p/'APPLICATION.json')=='3fbd88cbd0c441ebf4b2b0eb46e18ed7da1bf58ab5e59eb178a0d4036126ec71';shutil.copyfile(p/'APPLICATION.json',snap)
for n,h in files.items():
 assert H(V/n)==h
 for dst in [ed/'reviews'/n,B/'candidates/reviews'/n]:dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(V/n,dst)
for n in ['build_successor.py','prepare_candidate.py','validate_successors.py','bind_source_review.py','PAIRS.json','VALIDATION.log','TOOLING-TESTS.log','AUDIT-SELF-TEST.log']:shutil.copyfile(B/n,ed/n)
refs=[{'path':F+'/reviews/'+n,'sha256':h} for n,h in expected.items()]
for n in ['HOSTED_REPAIR.json','SOURCE_VALIDATION.json']:
 d=json.loads((p/n).read_text());d['source_review']='NO_SOURCE_LEVEL_BLOCKER';d['source_review_reports']=refs
 if n=='SOURCE_VALIDATION.json':d.update(source_hash_import_binding_checks='PASS',predecessor_closure_comparison='PASS',classification_negative_controls_rejected=4,test_progress_experiment={'tests':19,'result':'PASS','tooling_only':True},audit_history_self_test={'literal_command_exit':0,'scope':'Existing history/current registry, not proof validation'})
 W(p/n,d)
a=json.loads((p/'APPLICATION.json').read_text());a['status']='SOURCE_REVIEWED_PROPAGATION_AND_HOSTED_REPLAY_PENDING'
for n in a['bindings']:a['bindings'][n]=H(p/n)
for f in sorted(ed.rglob('*')):
 if f.is_file():a['bindings'][f.relative_to(p).as_posix()]=H(f)
W(p/'APPLICATION.json',a)
for n,h in a['bindings'].items():assert H(p/n)==h
assert H(p/'intake.json')==intake and H(p/'README.md')==readme
print(json.dumps({'packet':p.name,'intake':intake,'README':readme,'APPLICATION':H(p/'APPLICATION.json'),'copied_review_evidence_files':len(files)}))
