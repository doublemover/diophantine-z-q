from pathlib import Path
import json,hashlib,subprocess,io,zipfile,base64,shutil
B=Path('/workspace/scratch/41c6d5925c0e'); W=B/'arithmetic-run43611323966'; O=B/'review43611323966'; S=O/'arithmetic-hone-source-snapshots'; R=B/'pel-integration43603177874/repo'; H='2428de0d42f12dc71e2bc6f19495025a5912d41c'; P='quartics/quartic-318-326/proof/experiments/contact-original-positive-generators-r78'; N='ContactOriginalLineHOneFinite318'; sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();dig=lambda b:hashlib.sha256(b).hexdigest()
b=json.loads((W/'candidates/BINDINGS.json').read_text()); assert sha(W/'candidates/BINDINGS.json')=='90967db54ff891e5073d2f0e7fea92a8bdca80fd7a7bc1efe77ccc5b2649b6a0'
for n,h in b['bindings'].items(): assert sha(W/n)==h,n
before=(W/f'candidates/before.{N}.lean').read_bytes(); after=(W/f'candidates/{N}.lean').read_bytes(); assert dig(before)==b['source_before_sha256']=='0864e0182845294a7657d759abe976bb4f938866af8ddc95043e29c0153b9862';assert dig(after)==b['source_after_sha256']=='e4581783e4c1a4701a47d5c9f90e1dc6f32a83867259044f0b2a13ef8473365d';assert before.count(b'\ndef equivalence :')==1;assert before.replace(b'\ndef equivalence :',b'\n@[expose] def equivalence :')==after
assert b['human_contract_sha256']==sha(W/'candidates/APPLICATION.md')=='71d945bcc35b6228d4e90c9b844923c33ce35d6edd51984f7ac2c52a4a52cc52'
i=json.loads((W/'candidates/before.intake.json').read_text());assert len(i['order'])==len(set(i['order']))==len(i['files'])==107
files=['intake.json','APPLICATION.json']+list(i['files']);req=''.join(H+':'+P+'/'+n+'\n' for n in files);out=subprocess.check_output(['git','cat-file','--batch'],input=req.encode(),cwd=R);s=io.BytesIO(out);vals={};blobs={}
for n in files:
 hdr=s.readline().decode().split();assert len(hdr)==3 and hdr[1]=='blob';v=s.read(int(hdr[2]));assert s.read(1)==b'\n';vals[n]=v;blobs[n]=hdr[0]
assert s.read()==b'';assert vals['intake.json']==(W/'candidates/before.intake.json').read_bytes();assert vals['APPLICATION.json']==(W/'candidates/before.APPLICATION.json').read_bytes();assert vals[N+'.lean']==before
for n,row in i['files'].items():assert dig(vals[n])==row['sha256']
for p in (W/'candidates/primary').glob('*.lean'):
 if not p.name.startswith('Mathlib-'):assert p.read_bytes()==vals[p.name],p.name
pin=json.loads((W/'candidates/primary/PINNED-API-BINDINGS.json').read_text())
for row in pin['sources']:
 p=W/'candidates/primary'/row['copy'];v=p.read_bytes();receipt=json.loads(p.with_suffix(p.suffix+'.json').read_text());assert sha(p)==row['sha256'];assert hashlib.sha1(b'blob '+str(len(v)).encode()+b'\0'+v).hexdigest()==row['git_blob_sha1']==receipt['sha'];assert base64.b64decode(receipt['content'])==v;assert row['commit']=='56a005855ea17e0b0958f73ec801ae140b0a1679' and row['commit'] in receipt['url'];assert '@[expose] public section' in v.decode()
a=json.loads((W/'positive-artifact.json').read_text());assert a['id']==14121280761 and a['workflow_run']['id']==43611323966 and a['workflow_run']['head_sha']==H;assert sha(W/'positive.zip')==a['digest'].split(':')[1]==b['artifact_sha256']=='f1bb14d0afd09abe7ebe1b05c1ab0fa28ff905f953aea6643358afa22a9b99cb';assert (W/'positive.zip').stat().st_size==a['size_in_bytes']
with zipfile.ZipFile(W/'positive.zip') as z:
 assert z.testzip() is None
 for n in z.namelist():
  if not n.endswith('/'): assert z.read(n)==(W/'positive-evidence'/n).read_bytes(),n
r=json.loads((W/'candidates/RESULT.json').read_text());assert r['packet_sha256']==sha(W/'candidates/before.intake.json');assert r['status']=='FAILED' and r['new_source_acceptance'] is False and r['full_arithmetic_theorem_proved'] is False;assert r['commands'][-1]=={'exit_code':1,'module':N,'seconds':38.579};assert all(x['exit_code']==0 for x in r['commands'][:-1]);assert r['commands'][-2]=={'exit_code':0,'module':'ContactOriginalLaurentBoundary318','seconds':35.113};pos={n:j for j,n in enumerate(i['order'])};assert [pos[x['module']] for x in r['commands']]==sorted(pos[x['module']] for x in r['commands']);log=(W/f'candidates/{N}.log').read_text();assert log.count(': error:')==1 and 'requires that all definitions' in log and 'must be exposed' in log
S.mkdir(exist_ok=True)
for n in list(b['bindings'])+['candidates/BINDINGS.json']:
 p=W/n;d=S/n;d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,d)
(S/'GIT-PREDECESSOR-CHECK.json').write_text(json.dumps({'head':H,'packet':P,'git_blobs':blobs,'sources_verified':107},indent=2)+'\n')
result={'status':'PASS_SOURCE_AND_HUMAN_CONTRACT_ONLY_NOT_HOSTED_ACCEPTANCE','module':N,'before_sha256':dig(before),'after_sha256':dig(after),'contract_sha256':b['human_contract_sha256'],'exact_single_attribute_inverse':True,'public_types_bodies_instances_imports_options_unchanged':True,'definition_visibility_changed':True,'run':43611323966,'head':H,'artifact_id':a['id'],'zip_sha256':b['artifact_sha256'],'observed_last_command':r['commands'][-1],'observed_previous_command':r['commands'][-2],'owner_bindings_verified':len(b['bindings']),'published_source_hashes_verified':107,'native_git_blobs_verified':3,'human_obligations_reviewed':9,'local_lean_run':False,'kernel_acceptance':False,'source_bindings':{str(p.relative_to(B)):sha(p) for p in sorted(S.rglob('*')) if p.is_file()}}
(O/'ARITHMETIC-HONE-SOURCE-CHECK.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS exact single expose attribute; 107 predecessor Git/source hashes; all owner bindings; 3 native Git blobs; authentic ordinary artifact/ordered results; 9 human obligations. No Lean.')
