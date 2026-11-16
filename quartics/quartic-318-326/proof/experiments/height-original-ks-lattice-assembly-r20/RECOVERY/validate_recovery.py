"""Validate exact source recovery and native packet metadata; never runs Lean."""
from pathlib import Path
import hashlib,json,sys,tempfile,shutil,copy,subprocess
BASE=Path(__file__).resolve().parent
REPO=Path('/workspace/scratch/41c6d5925c0e/pel-integration43539970197/repo')
sys.path.insert(0,str(REPO/'scripts'))
import check_progress_experiment as check
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=json.loads((BASE/'recovered/geometry-PROPAGATION-BINDINGS.json').read_text())['packets']
plan=check.ci.derive_plan()
with tempfile.TemporaryDirectory(dir=BASE,prefix='validation-') as temp:
 root=Path(temp)
 for row in rows:
  old,new=row['predecessor'],row['packet'];p=BASE/'successors'/new;before=REPO/'quartics/quartic-318-326/proof/experiments'/old
  shutil.copytree(p,root/new);(root/old).mkdir()
  for f in [before/'intake.json',*before.glob('*.lean')]:shutil.copyfile(f,root/old/f.name)
  _,d,_,_=check.packet(new,plan,root)
  assert H(p/'intake.json')==row['intake_sha256'] and H(p/'README.md')==row['readme_sha256']
  sourcehash={n+'.lean':H(p/(n+'.lean')) for n in d['order']}
  assert sourcehash==row['sources'] and set(sourcehash)=={f.name for f in p.glob('*.lean')}
  assert d['order']==json.loads((before/'intake.json').read_text())['order']
  revised=[n for n in d['order'] if H(before/(n+'.lean'))!=H(p/(n+'.lean'))];reused=[n for n in d['order'] if n not in revised]
  assert set(revised)==set(row['changed']) and len(reused)==row['unchanged']
  for k,v in dict(new_modules=[],revised_modules=revised,reused_modules=reused,unchanged_predecessor_modules=reused).items():assert d[k]==v
  inheritance=json.loads((p/'INHERITANCE.json').read_text());assert inheritance['old_sources']=={n+'.lean':H(before/(n+'.lean')) for n in d['order']};assert inheritance['new_sources']==sourcehash
  app=json.loads((p/'APPLICATION.json').read_text());assert app['sources']==sourcehash and app['intake_sha256']==H(p/'intake.json') and app['contract_sha256']==H(p/'README.md')
  for result in row['own_results']:
   assert H(p/result['path'])==result['sha256']
   assert json.loads((p/result['path']).read_text())['packet_sha256']==H(before/'intake.json')
  controls=0
  for key in ['new_modules','revised_modules','reused_modules','unchanged_predecessor_modules']:
   bad=copy.deepcopy(d);bad[key]=['__unexpected__'] if key=='new_modules' else []
   try:check.check_revision_classifications(root/new,bad,root)
   except ValueError:controls+=1
   else:raise AssertionError('Invalid classification accepted: '+key)
  print(json.dumps(dict(packet=new,status='PASS_EXACT_SOURCE_RECOVERY_AND_METADATA_CHECK',modules=row['modules'],unchanged=row['unchanged'],classification_negative_controls=controls)))
