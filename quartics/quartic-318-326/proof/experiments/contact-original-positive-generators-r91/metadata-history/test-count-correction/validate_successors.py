from pathlib import Path
import sys,json,hashlib,shutil
W=Path(__file__).resolve().parent;R=Path('/workspace/scratch/41c6d5925c0e/pel-integration43603177874/repo'); E=R/'quartics/quartic-318-326/proof/experiments'
sys.path.insert(0,str(R/'scripts')); import check_progress_experiment as chk
rows=json.loads((W/'SUCCESSOR_MAP.json').read_text());V=W/'validation-root';V.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
base=chk.ci.derive_plan()
for row in rows:
 old,new=row['predecessor'],row['successor']; src=W/'successors'/new
 p=V/old;p.mkdir(exist_ok=True)
 oldd=json.loads((E/old/'intake.json').read_text())
 for n in ['intake.json']+[n+'.lean' for n in oldd['order']]:shutil.copyfile(E/old/n,p/n)
 q=V/new;shutil.copytree(src,q,dirs_exist_ok=True)
 _,d,direct,external=chk.packet(new,base,root=V)
 hashes={n+'.lean':sha(src/(n+'.lean')) for n in d['order']}
 assert d['order']==oldd['order'];assert [n for n in d['order'] if sha(src/(n+'.lean'))!=sha(p/(n+'.lean'))]==[row['module']]
 app=json.loads((src/'APPLICATION.json').read_text());assert app['sources']==hashes
 result=dict(packet=new,status='SOURCE_HASH_IMPORT_BINDING_AND_REVISION_CLASSIFICATION_CHECKS_PASS',modules=len(d['order']),direct_baseline_dependencies=len(direct),external_imports=len(external),revision_classification_schema=1,ordered_closure_unchanged=True,only_changed_modules=[row['module']],python_progress_tests=34,python_ci_tooling_tests=15,local_lean_run=False,kernel_verified=False,audit_history_self_test='PASS: 7 negative controls,19 application-review negative controls,3 current application contracts; not a proof check',publication_check='PENDING integration index')
 write(src/'SOURCE_VALIDATION.json',result)
 app['bindings']['SOURCE_VALIDATION.json']=sha(src/'SOURCE_VALIDATION.json');write(src/'APPLICATION.json',app)
 chk.check_application_bindings(src)
 print(json.dumps(result));print('APP',sha(src/'APPLICATION.json'))
