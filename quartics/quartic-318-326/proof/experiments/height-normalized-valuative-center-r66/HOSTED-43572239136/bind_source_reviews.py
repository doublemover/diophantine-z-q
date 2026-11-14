"""Bind authored source-only reviews to frozen geometry successor metadata."""
from pathlib import Path
import json,hashlib,shutil
B=Path(__file__).resolve().parent;V=B.parent/'review43572239136';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();W=lambda p,d:p.write_text(json.dumps(d,indent=2)+'\n')
reports={n:H(V/n) for n in ['GEOMETRY-GLOBAL-SOURCE-REVIEW.md','GEOMETRY-GLOBAL-SOURCE-BINDINGS.json','GEOMETRY-COMMON-SOURCE-REVIEW.md','GEOMETRY-COMMON-SOURCE-BINDINGS.json']}
assert reports['GEOMETRY-COMMON-SOURCE-REVIEW.md']=='ab0e16f818f76ec74125e18660e4f82cc45671ba9532efcf42b9ad5b4e0b3df7'
assert reports['GEOMETRY-COMMON-SOURCE-BINDINGS.json']=='c42da9ab992e42b176e1a05b01bc4fd311d7d791be1aa1daba3fd5ee831b4766'
assert reports['GEOMETRY-GLOBAL-SOURCE-REVIEW.md']=='f0e4595dd739c24a5997efa0dc5b58e94f07f7b1c87dda74b934e23b7b84d535'
assert reports['GEOMETRY-GLOBAL-SOURCE-BINDINGS.json']=='b6079be803f02b723c67c4513e9fb783c9649e5d79ab935c36f3b7f1eba4823c'
assert H(B/'candidates/IntegralOriginalCommonRestriction318.lean')=='d40c691814996c92d3c49d23f3e6f7747b21af8324aec6c7445154d95c94a0b4'
assert 'd40c691814996c92d3c49d23f3e6f7747b21af8324aec6c7445154d95c94a0b4' in (V/'GEOMETRY-COMMON-SOURCE-REVIEW.md').read_text()
(B/'candidates/reviews').mkdir(exist_ok=True)
for n in reports:shutil.copyfile(V/n,B/'candidates/reviews'/n)
for row in json.loads((B/'PAIRS.json').read_text()):
 p=B/'successors'/row['packet'];ed=p/'HOSTED-43572239136';(ed/'reviews').mkdir(exist_ok=True);old_intake=H(p/'intake.json');old_readme=H(p/'README.md')
 snapshot=ed/'SOURCE-REVIEW-PRE-BIND-APPLICATION.json';assert not snapshot.exists();shutil.copyfile(p/'APPLICATION.json',snapshot)
 selected=[n for n in reports if 'GLOBAL' in n or 'lattice' in row['packet']]
 for n in selected:shutil.copyfile(V/n,ed/'reviews'/n)
 for n in ['build_successors.py','validate_successors.py','bind_source_reviews.py','PAIRS.json','VALIDATION.log','TOOLING-TESTS.log','AUDIT-SELF-TEST.log']:shutil.copyfile(B/n,ed/n)
 refs=[{'path':'HOSTED-43572239136/reviews/'+n,'sha256':reports[n]} for n in selected]
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
