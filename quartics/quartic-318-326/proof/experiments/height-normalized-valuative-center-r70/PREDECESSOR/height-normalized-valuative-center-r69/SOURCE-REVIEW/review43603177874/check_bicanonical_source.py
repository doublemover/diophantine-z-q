from pathlib import Path
import hashlib,json,subprocess,shutil,zipfile,re
B=Path('/workspace/scratch/41c6d5925c0e');W=B/'geometry-run43603177874';C=W/'candidates';O=B/'review43603177874';S=O/'bicanonical-source-snapshots';S.mkdir(exist_ok=True);R=B/'pel-integration43597228569/repo';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();n='IntegralOriginalBicanonicalRestrictions318';m=json.loads((C/(n+'-REPAIR.json')).read_text());H=m['head'];a=(C/(n+'.lean')).read_text();b=(C/(n+'.before')).read_text();assert sha(C/(n+'.lean'))==m['after_sha256'] and sha(C/(n+'.before'))==m['before_sha256']
x=a;start=x.index('/-- Abstract route transport');end=x.index('variable (c : Fin 4',start);helpers=x[start:end];x=x[:start]+x[end:];assert helpers.count('theorem ')==2
for term in ['IntegralRationalFiniteAtlas318.branchEquiv c i','IntegralInfinityOriginalField318.rationalOrderEquiv c']:
 line='  letI := spec_algEquiv_open ('+term+')\n';assert x.count(line)==1;x=x.replace(line,'')
for kind,suffix in [('branch',' c i'),('infinity',' c')]:
 new='  exact imageLE_of_route _ _ _ ('+kind+'_route'+suffix+')';old='  rw [←'+kind+'_route]\n  exact OpenChartSections318.imageLE _ _';assert x.count(new)==1;x=x.replace(new,old)
assert x==b
prov=json.loads((C/'primary/PROVENANCE.json').read_text())
for row in prov:
 p=C/row['path'];assert sha(p)==row['sha256'];v=p.read_bytes();assert hashlib.sha1(b'blob '+str(len(v)).encode()+b'\0'+v).hexdigest()==row['git_blob'];assert v==subprocess.check_output(['git','show',H+':'+row['repository_path']],cwd=R)
assert (C/'primary'/ (n+'.lean')).read_bytes()==(C/(n+'.before')).read_bytes()
A=W/'evidence/center';meta=json.loads((A/'ARTIFACT.json').read_text());assert meta['id']==m['artifact'] and meta['workflow_run']['id']==m['run'] and meta['workflow_run']['head_sha']==H;assert sha(A/'artifact.zip')==m['zip_sha256'] and meta['digest']=='sha256:'+m['zip_sha256']
with zipfile.ZipFile(A/'artifact.zip') as z:
 assert z.testzip() is None
 for fn in z.namelist():
  if not fn.endswith('/'):assert (A/'unpacked'/fn).read_bytes()==z.read(fn)
rp=A/'unpacked/progress-experiments/height-normalized-valuative-center-r68';assert (rp/'RESULT.json').read_bytes()==(C/'CENTER-RESULT.json').read_bytes();assert (rp/'logs'/(n+'.log')).read_bytes()==(C/(n+'.log')).read_bytes();assert sha(C/'CENTER-RESULT.json')==m['result_sha256'];assert sha(C/(n+'.log'))==m['log_sha256'];r=json.loads((C/'CENTER-RESULT.json').read_text());assert r['packet_sha256']==sha(C/'primary/intake.json');assert r['commands'][-1]=={'module':n,'exit_code':1,'seconds':9.386};assert all(v['exit_code']==0 for v in r['commands'][:-1]);log=(C/(n+'.log')).read_text();assert log.count('motive is not type correct')==2 and log.count('failed to synthesize instance of type class')==2
files=[C/(n+'.lean'),C/(n+'.before'),C/(n+'.diff'),C/(n+'.log'),C/(n+'-REPAIR.json'),C/'CENTER-RESULT.json',A/'ARTIFACT.json']+list((C/'primary').iterdir())
for p in files:
 d=S/p.relative_to(W);d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,d)
consumer='quartics/quartic-318-326/proof/experiments/height-normalized-valuative-center-r68/IntegralOriginalGlobalPair318.lean';v=subprocess.check_output(['git','show',H+':'+consumer],cwd=R);(S/'IntegralOriginalGlobalPair318.lean').write_bytes(v)
j={'status':'PASS_SOURCE_ONLY_NOT_HOSTED_ACCEPTANCE','module':n,'before_sha256':m['before_sha256'],'after_sha256':m['after_sha256'],'run':m['run'],'head':H,'artifact_id':m['artifact'],'zip_sha256':m['zip_sha256'],'two_new_helpers':['imageLE_of_route','spec_algEquiv_open'],'previous_statements_options_maps_unchanged':True,'direct_consumer':{'path':consumer,'sha256':hashlib.sha256(v).hexdigest()},'source_bindings':{str(p.relative_to(B)):sha(p) for p in S.rglob('*') if p.is_file()},'local_lean_run':False}
(O/'BICANONICAL-SOURCE-CHECK.json').write_text(json.dumps(j,indent=2)+'\n');print('PASS source inverse, native project primaries, direct consumer and own hosted ZIP/result/intake/log')
