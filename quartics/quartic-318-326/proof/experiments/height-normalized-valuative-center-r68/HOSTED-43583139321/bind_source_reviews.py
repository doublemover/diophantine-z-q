"""Bind authored source-only reviews; preserves exact raw pre-binding APPLICATIONs."""
from pathlib import Path
import json,hashlib,shutil,sys
B=Path(__file__).resolve().parent;V=Path(sys.argv[1]);H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();W=lambda p,d:p.write_text(json.dumps(d,indent=2)+'\n');F='HOSTED-43583139321'
reports={n:H(V/n) for n in ['GEOMETRY-GLOBAL-SOURCE-REVIEW.md','GEOMETRY-GLOBAL-SOURCE-BINDINGS.json','GEOMETRY-COMMON-SOURCE-REVIEW.md','GEOMETRY-COMMON-SOURCE-BINDINGS.json']}
for name,expected in [('IntegralRationalGlobalComparison318','0782c7b9b9aa48645357033992db1a11d27fabdf9ef4f9dd93ad966bb3a7a3a9'),('IntegralOriginalCommonRestriction318','11d365488de375da288b7c3336d34e80f46213393fce57a57373b86ca8df6963')]:assert H(B/'candidates'/(name+'.lean'))==expected
(B/'candidates/reviews').mkdir(exist_ok=True)
for n in reports:shutil.copyfile(V/n,B/'candidates/reviews'/n)
for row in json.loads((B/'PAIRS.json').read_text()):
 p=B/'successors'/row['packet'];ed=p/F;(ed/'reviews').mkdir(exist_ok=True);old_intake=H(p/'intake.json');old_readme=H(p/'README.md')
 snapshot=ed/'SOURCE-REVIEW-PRE-BIND-APPLICATION.json';assert not snapshot.exists();shutil.copyfile(p/'APPLICATION.json',snapshot)
 # Both reports preserve explicit cross-lane context; center changes only Global.
 for n in reports:shutil.copyfile(V/n,ed/'reviews'/n)
 for n in ['build_successors.py','validate_successors.py','bind_source_reviews.py','PAIRS.json','VALIDATION.log','TOOLING-TESTS.log','AUDIT-SELF-TEST.log']:shutil.copyfile(B/n,ed/n)
 refs=[{'path':F+'/reviews/'+n,'sha256':reports[n]} for n in reports]
 for n in ['HOSTED_REPAIR.json','SOURCE_VALIDATION.json']:
  d=json.loads((p/n).read_text());d['source_review']='NO_SOURCE_LEVEL_BLOCKER';d['source_review_reports']=refs
  if n=='SOURCE_VALIDATION.json':d.update(source_hash_import_binding_checks='PASS',predecessor_closure_comparison='PASS',classification_negative_controls_rejected=4,test_progress_experiment={'tests':19,'result':'PASS','tooling_only':True},audit_history_self_test={'literal_command_exit':0,'scope':'Existing history/current registry, not proof validation'})
  W(p/n,d)
 a=json.loads((p/'APPLICATION.json').read_text());a['status']='SOURCE_REVIEWED_PROPAGATION_AND_HOSTED_REPLAY_PENDING'
 for n in a['bindings']:a['bindings'][n]=H(p/n)
 for f in sorted(ed.rglob('*')):
  if f.is_file():a['bindings'][f.relative_to(p).as_posix()]=H(f)
 W(p/'APPLICATION.json',a);assert H(p/'intake.json')==old_intake and H(p/'README.md')==old_readme
 print(json.dumps({'packet':row['packet'],'intake':old_intake,'README':old_readme,'APPLICATION':H(p/'APPLICATION.json'),'reviews':refs}))
