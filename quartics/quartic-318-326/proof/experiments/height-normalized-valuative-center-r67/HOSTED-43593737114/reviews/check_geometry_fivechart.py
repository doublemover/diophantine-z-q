import json,hashlib,subprocess,zipfile,shutil
from pathlib import Path
B=Path('/workspace/scratch/41c6d5925c0e');O=B/'review43592150561';W=B/'geometry-run43593737114';C=W/'candidates';R=B/'followup-integration43592150561/repo';H='2b151fc62f5872fd569489336d35f536d4cae0a4';P='quartics/quartic-318-326/proof/experiments/height-normalized-valuative-center-r66';N='IntegralRationalFiveChartGeometry318.lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
blob=lambda p:subprocess.check_output(['git','show',H+':'+p],cwd=R)
a=next(x for x in json.loads((O/'INDEPENDENT-GITHUB-ARTIFACTS-435937.json').read_text())['artifacts'] if x['id']==14113449077)
assert a['workflow_run']['head_sha']==H and a['workflow_run']['id']==43593737114
assert a['digest']=='sha256:'+sha(W/'evidence/center.zip')
with zipfile.ZipFile(W/'evidence/center.zip') as z:
 assert z.testzip() is None
 for n in z.namelist():
  if not n.endswith('/'): assert z.read(n)==(W/'evidence/center'/n).read_bytes()
before=(C/(N+'.before')).read_text();after=(C/N).read_text()
assert (C/(N+'.before')).read_bytes()==blob(P+'/'+N)
assert sha(C/N)=='b2b593c35843495dcdcf76200d17b4d546366cf2d064ac5f6ea7974c084dff4a'
x='  change Spec.map (branchEquiv c i).toRingEquiv.toCommRingCatIso.hom ≫ _ = _\n'
y='  change Spec.map (branchEquiv c i).toRingEquiv.toCommRingCatIso.hom ≫ _ =\n    _ ≫ Spec.map (IntegralRationalFullOverlap318.sourceEquiv c).toRingEquiv.toCommRingCatIso.hom\n'
assert before.count(x)==1 and before.replace(x,y)==after
for q in json.loads((C/'primary/PROVENANCE.json').read_text()):
 p=C/'primary'/Path(q['path']).name;assert p.read_bytes()==blob(q['path']) and sha(p)==q['sha256']
assert (C/'predecessor-intake.json').read_bytes()==blob(P+'/intake.json')
E=W/'evidence/center/progress-experiments/height-normalized-valuative-center-r66'
for q,n in [('center-RESULT.json','RESULT.json'),('IntegralRationalFiveChartGeometry318.log','logs/IntegralRationalFiveChartGeometry318.log')]:assert (C/q).read_bytes()==(E/n).read_bytes()
res=json.loads((E/'RESULT.json').read_text());assert res['packet_sha256']==sha(C/'predecessor-intake.json') and res['status']=='FAILED'
assert sum('error:' in l for l in (C/'IntegralRationalFiveChartGeometry318.log').read_text().splitlines())==1
ss=O/'source-snapshots/geometry-fivechart';ss.mkdir(parents=True,exist_ok=True)
for p in C.rglob('*'):
 if p.is_file():dst=ss/p.relative_to(C);dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dst)
shutil.copy2(W/'evidence/center.zip',ss/'center.zip')
check={'status':'PASS_SOURCE_AND_AUTHENTIC_EVIDENCE_ONLY','artifact':a,'before_sha256':sha(C/(N+'.before')),'after_sha256':sha(C/N),'result_sha256':sha(C/'center-RESULT.json'),'exact_single_replacement':True,'public_statements_options_imports_unchanged':True,'local_lean_run':False,'candidate_hosted_pass':False,'commands':res['commands'][-4:]}
(O/'GEOMETRY-FIVECHART-SOURCE-CHECK.json').write_text(json.dumps(check,indent=2)+'\n');print('PASS',check['after_sha256'],check['commands'])
