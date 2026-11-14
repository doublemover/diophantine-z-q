from pathlib import Path
import json,hashlib,shutil
w=Path(__file__).resolve().parent;p=w/'successors/contact-original-positive-generators-r79';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert 'Ran 22 tests' in (w/'progress-tests.txt').read_text();assert 'Ran 15 tests' in (w/'ci-tests.txt').read_text()
a=p/'APPLICATION.json';v=p/'SOURCE_VALIDATION.json';assert sha(a)=='8e6240e7a098a56e59b725afaf86d197e07f514bab5dfebd4feb9d8511f52e97'
snap=p/'metadata-history/test-count-correction';snap.mkdir(parents=True)
for src in [a,v,w/'validate_successors.py']:shutil.copyfile(src,snap/src.name)
f=w/'validate_successors.py';old=f.read_text();assert 'python_progress_tests=34' in old;f.write_text(old.replace('python_progress_tests=34','python_progress_tests=22'))
data=json.loads(v.read_text());assert data['python_progress_tests']==34;data['python_progress_tests']=22;data['python_progress_suite']='test_progress_experiment.py';v.write_text(json.dumps(data,indent=2)+'\n')
receipt={'reason':'Copied validator metadata confused test_progress_lean count34 with actually executed test_progress_experiment count22. Corrected to observed log, not a test or proof failure.','exact_progress_tests':22,'exact_ci_tests':15,'sources_intake_README_human_contract_changed':False,'old_application_sha256':sha(snap/'APPLICATION.json'),'old_validation_sha256':sha(snap/'SOURCE_VALIDATION.json'),'new_validation_sha256':sha(v),'generator_before_sha256':sha(snap/'validate_successors.py'),'generator_after_sha256':sha(f)}
(p/'TEST-COUNT-CORRECTION.json').write_text(json.dumps(receipt,indent=2)+'\n');data=json.loads(a.read_text());data['bindings']['SOURCE_VALIDATION.json']=sha(v);data['bindings']['TEST-COUNT-CORRECTION.json']=sha(p/'TEST-COUNT-CORRECTION.json')
for x in snap.iterdir():data['bindings'][x.relative_to(p).as_posix()]=sha(x)
a.write_text(json.dumps(data,indent=2)+'\n')
for rel,h in data['bindings'].items():assert sha(p/rel)==h,rel
print('APP',sha(a));print('intake',sha(p/'intake.json'));print('source',sha(p/'ContactOriginalLineHOneFinite318.lean'))
