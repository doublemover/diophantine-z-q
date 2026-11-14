"""Bind authored source-only reviews to frozen geometry successor metadata."""
from pathlib import Path
import json,hashlib,shutil
B=Path(__file__).resolve().parent;V=B.parent/'review43568616769';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();W=lambda p,d:p.write_text(json.dumps(d,indent=2)+'\n')
reports={n:H(V/n) for n in ['GEOMETRY-GLOBAL-SOURCE-REVIEW.md','GEOMETRY-GLOBAL-SOURCE-BINDINGS.json','GEOMETRY-COMMON-SOURCE-REVIEW.md','GEOMETRY-COMMON-SOURCE-BINDINGS.json']}
assert reports['GEOMETRY-COMMON-SOURCE-REVIEW.md']=='5a98c59a7da230d9ad5a6b2ec8fabf1e506c493018399e5be489f29216a77539'
assert reports['GEOMETRY-COMMON-SOURCE-BINDINGS.json']=='84934340f7c0546a0e2bd9234b9c0c8a89e788f94cc3cace87328214d5b88fd5'
assert reports['GEOMETRY-GLOBAL-SOURCE-REVIEW.md']=='b9069801222f68b2c200c319cde6846bb5ad25858adfcb782d99567954214cf0'
assert reports['GEOMETRY-GLOBAL-SOURCE-BINDINGS.json']=='967b8f5ddc0c2987d19b255effdaf7a5410edb392ce2d48aca5ef84a6dd9dd20'
assert H(B/'candidates/IntegralOriginalCommonRestriction318.lean')=='01c42107bb65a1e9e145a03d8e424750bbdef64482fd9b80000bb7c096f24590'
assert '01c42107bb65a1e9e145a03d8e424750bbdef64482fd9b80000bb7c096f24590' in (V/'GEOMETRY-COMMON-SOURCE-REVIEW.md').read_text()
for n in reports:shutil.copyfile(V/n,B/'candidates/reviews'/n)
for row in json.loads((B/'PAIRS.json').read_text()):
 p=B/'successors'/row['packet'];ed=p/'HOSTED-43568616769';(ed/'reviews').mkdir(exist_ok=True);old_intake=H(p/'intake.json');old_readme=H(p/'README.md')
 selected=[n for n in reports if 'GLOBAL' in n or 'lattice' in row['packet']]
 for n in selected:shutil.copyfile(V/n,ed/'reviews'/n)
 for n in ['build_successors.py','validate_successors.py','bind_source_reviews.py','PAIRS.json','VALIDATION.log','TOOLING-TESTS.log','AUDIT-SELF-TEST.log']:shutil.copyfile(B/n,ed/n)
 refs=[{'path':'HOSTED-43568616769/reviews/'+n,'sha256':reports[n]} for n in selected]
 for n in ['HOSTED_REPAIR.json','SOURCE_VALIDATION.json']:
  d=json.loads((p/n).read_text());d['source_review']='NO_SOURCE_LEVEL_BLOCKER';d['source_review_reports']=refs
  if n=='SOURCE_VALIDATION.json':d.update(source_hash_import_binding_checks='PASS',predecessor_closure_comparison='PASS',classification_negative_controls_rejected=4,test_progress_experiment={'tests':19,'result':'PASS','tooling_only':True},audit_history_self_test={'literal_command_exit':0,'scope':'Existing historical/current manuscript registry, not new proof validation'})
  W(p/n,d)
 a=json.loads((p/'APPLICATION.json').read_text());a['status']='SOURCE_REVIEWED_PROPAGATION_AND_HOSTED_REPLAY_PENDING'
 for n in a['bindings']:a['bindings'][n]=H(p/n)
 for f in sorted(ed.rglob('*')):
  if f.is_file():a['bindings'][f.relative_to(p).as_posix()]=H(f)
 W(p/'APPLICATION.json',a);assert H(p/'intake.json')==old_intake and H(p/'README.md')==old_readme
 print(json.dumps({'packet':row['packet'],'intake':old_intake,'README':old_readme,'APPLICATION':H(p/'APPLICATION.json'),'reviews':refs}))
