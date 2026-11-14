from pathlib import Path
import json,hashlib,subprocess,shutil,zipfile,re
B=Path('/workspace/scratch/41c6d5925c0e');W=B/'pel-run43597228569';O=B/'review43597228569';R=B/'pel-integration43592150561/repo';H='2af419e128047c483b3cdc0ba5e4d65c09d7c4ce';X='quartics/quartic-318-326/proof/experiments/'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
S=O/'source-snapshots/pel-residue'; S.mkdir(parents=True,exist_ok=True)
def save(p,r):
 d=S/r;d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,d)
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',H,'--',X],cwd=R).decode().splitlines();checked=[]
for tag in ['RESIDUE']:
 m=W/'candidates'/f'{tag}-MANIFEST.json';M=json.loads(m.read_text());assert M['base']==H and M['run']==43597228569
 save(m,m.name);n=M['module'];a=(W/'candidates/before'/f'{n}.lean').read_text();b=(W/'candidates/after'/f'{n}.lean').read_text()
 assert re.findall(r'^.*(?:import|set_option).*$',a,re.M)==re.findall(r'^.*(?:import|set_option).*$',b,re.M)
 exp=a.replace('push_cast <;> simp [ZMod.natCast_zmod_val] <;> ring','push_cast <;> (try simp [ZMod.natCast_zmod_val]) <;> ring')
 assert exp==b
 for rel,h in M['source_bindings'].items():
  p=W/rel;assert sha(p)==h;save(p,rel)
  if '/primary/' in rel and p.suffix=='.lean' and not p.name.startswith('Mathlib_'):
   pp=[q for q in paths if q.endswith('/'+p.name) and q.count('/')==5]
   assert any(subprocess.check_output(['git','show',H+':'+q],cwd=R)==p.read_bytes() for q in pp),p
 for e in M['evidence']:
  for rel,h in e['files'].items():assert sha(W/rel)==h;save(W/rel,rel)
  packet=e['packet'];art=json.loads((W/'logs'/f"{e['lane']}-artifact.json").read_text());z=W/'logs'/f"{e['lane']}.zip"
  assert art['id']==e['artifact_id'] and art['workflow_run']['id']==43597228569 and art['workflow_run']['head_sha']==H and art['digest']=='sha256:'+sha(z)
  base=W/'logs'/f"{e['lane']}-artifact"
  with zipfile.ZipFile(z) as zz:
   assert zz.testzip() is None
   for name in zz.namelist():
    if not name.endswith('/'): assert zz.read(name)==(base/name).read_bytes()
  res=json.loads((base/'progress-experiments'/packet/'RESULT.json').read_text());it=W/'logs'/f"{e['lane']}-published-intake.json"
  assert res['packet_sha256']==sha(it) and res['status']=='FAILED' and res['commands'][-1]['module']==n and res['commands'][-1]['exit_code']==1
  assert subprocess.check_output(['git','show',H+':'+X+packet+'/'+n+'.lean'],cwd=R)==a.encode()
  assert subprocess.check_output(['git','show',H+':'+X+packet+'/intake.json'],cwd=R)==it.read_bytes()
 checked.append({'module':n,'before':M['before_sha256'],'after':M['after_sha256'],'contract':sha(W/'candidates'/f'{tag}-APPLICATION.md'),'own_artifacts':[e['artifact_id'] for e in M['evidence']]})
for rel,v in json.loads((W/'candidates/primary/ZMOD-PROVENANCE.json').read_text()).items():
 p=W/'candidates'/rel;data=p.read_bytes();assert sha(p)==v['sha256'];assert v['mathlib_commit']=='56a005855ea17e0b0958f73ec801ae140b0a1679';assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==v['git_blob_sha']
J={'status':'PASS_SOURCE_AND_CURRENT_HUMAN_CONTRACT_ONLY','run':43597228569,'head':H,'modules':checked,'local_lean_run':False,'candidate_hosted_pass':False,'future_packet_contract_review_complete':False,'source_bindings':{str(p.relative_to(O)):sha(p) for p in S.rglob('*') if p.is_file()}}
(O/'PEL-RESIDUE-SOURCE-CHECK.json').write_text(json.dumps(J,indent=2)+'\n');print('PASS: exact one optional-simp delta, two own artifact ZIPs/results/intakes, published before and primary bytes; no Lean.')
