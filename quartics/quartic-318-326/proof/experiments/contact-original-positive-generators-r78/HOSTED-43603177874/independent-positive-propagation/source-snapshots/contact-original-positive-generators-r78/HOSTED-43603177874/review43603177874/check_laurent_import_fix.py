from pathlib import Path
import json,hashlib,subprocess,re,zipfile,shutil
B=Path('/workspace/scratch/41c6d5925c0e');W=B/'arithmetic-run43603177874';C=W/'candidates';O=B/'review43603177874';O.mkdir(exist_ok=True);S=O/'laurent-import-snapshots';S.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();meta=json.loads((C/'POSITIVE_BINDINGS.json').read_text());H=meta['head'];R=B/'pel-integration43597228569/repo';rel='quartics/quartic-318-326/proof/experiments/contact-original-positive-generators-r77';name=meta['module']+'.lean';before=C/(meta['module']+'.before.lean');after=C/name
assert sha(before)==meta['before_sha256'] and sha(after)==meta['after_sha256'];assert subprocess.check_output(['git','show',H+':'+rel+'/'+name],cwd=R)==before.read_bytes()
a=after.read_text();b=before.read_text();names=re.findall(r'^public import all (\w+)$',b,re.M);assert len(names)==4;expected=b
for n in names:expected=expected.replace('public import all '+n+'\n','public import '+n+'\nimport all '+n+'\n')
assert a==expected and a.split('public section',1)[1]==b.split('public section',1)[1]
assert sorted(set(re.findall(r'^(?:public )?import (?:all )?(\w+)$',a,re.M)))==sorted(names)
assert sha(W/'positive.zip')==meta['artifact_zip_sha256'];ar=json.loads((W/'positive-artifact.json').read_text());assert ar['id']==meta['artifact_id'] and ar['workflow_run']['head_sha']==H and ar['workflow_run']['id']==meta['run'] and ar['digest']=='sha256:'+meta['artifact_zip_sha256']
with zipfile.ZipFile(W/'positive.zip') as z:
 assert z.testzip() is None
 for n in z.namelist():
  if not n.endswith('/'):assert (W/'positive-logs'/n).read_bytes()==z.read(n)
rp=W/'positive-logs/progress-experiments/contact-original-positive-generators-r77';r=json.loads((rp/'RESULT.json').read_text());assert r['packet_sha256']==meta['intake_sha256']==sha(W/'positive-intake.before.json');assert r['commands'][-1]=={'module':meta['module'],'exit_code':1,'seconds':0.065};assert all(x['exit_code']==0 for x in r['commands'][:-1]);log=(rp/'logs'/name.replace('.lean','.log')).read_text();assert log.count('error: cannot use `all` with `public import`')==4
for f,h in meta['primary_sources'].items():assert sha(C/'primary'/f)==h
native={}
for n in ['src-Lean-Parser-Module','src-Lean-Elab-Import']:
 p=C/'primary'/(n+'.lean');v=p.read_bytes();m=json.loads((C/'primary'/(n+'.lean.json')).read_text());assert m['content'].encode()==v;obj=hashlib.sha1(b'blob '+str(len(v)).encode()+b'\0'+v).hexdigest();assert obj==m['sha'];assert 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc' in m['display_url'];native[n]=obj
for p in (C/'primary').glob('*.lean'):
 if p.name.startswith('src-'):continue
 assert p.read_bytes()==subprocess.check_output(['git','show',H+':'+rel+'/'+p.name],cwd=R)
assert 'cannot use `all` with `public import`' in (C/'primary/src-Lean-Parser-Module.lean').read_text()
consumer=(C/'primary/ContactOriginalLineHOneFinite318.lean').read_text();assert 'ContactOriginalLaurentBoundary318.kernel_eq_boundary c L' in consumer
files=[C/'POSITIVE_BINDINGS.json',C/'POSITIVE_APPLICATION.md',before,after,C/(meta['module']+'.diff'),W/'positive-artifact.json',W/'positive-intake.before.json',rp/'RESULT.json',rp/'logs'/name.replace('.lean','.log')]+list((C/'primary').iterdir())
for p in files:
 dest=S/p.relative_to(W);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dest)
j={'status':'PASS_SOURCE_ONLY_NOT_ELABORATION','module':meta['module'],'before_sha256':sha(before),'after_sha256':sha(after),'contract_sha256':sha(C/'POSITIVE_APPLICATION.md'),'run':meta['run'],'head':H,'artifact_id':meta['artifact_id'],'artifact_zip_sha256':meta['artifact_zip_sha256'],'intake_sha256':meta['intake_sha256'],'split_directives':names,'all_after_public_section_identical':True,'native_git_blobs':native,'direct_consumer':'ContactOriginalLineHOneFinite318.equivalence via kernel_eq_boundary','local_lean_run':False,'source_bindings':{str(p.relative_to(B)):sha(p) for p in S.rglob('*') if p.is_file()}}
(O/'LAURENT-IMPORT-CHECK.json').write_text(json.dumps(j,indent=2)+'\n');print('PASS exact four splits; original body unchanged; own ZIP/log/intake/Git/native parser verified')
