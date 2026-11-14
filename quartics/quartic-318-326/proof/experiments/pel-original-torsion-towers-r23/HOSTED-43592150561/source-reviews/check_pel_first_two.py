from pathlib import Path
import json,hashlib,subprocess,re,zipfile,shutil,base64
B=Path('/workspace/scratch/41c6d5925c0e'); O=B/'review43592150561'; W=B/'pel-run43592150561'; C=W/'candidates'; R=B/'pel-integration43586414080/repo'; H='75be14ed25ed39f46289f1c69914810afd46068c'; X='quartics/quartic-318-326/proof/experiments/'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
M=json.loads((C/'FIRST-TWO-MANIFEST.json').read_text());assert M['base']==H and M['run']==43592150561
assert sha(C/M['contract'])==M['contract_sha256']
arts={x['id']:x for x in json.loads((O/'INDEPENDENT-GITHUB-ARTIFACTS-DIAGNOSTICS.json').read_text())['artifacts']}
S=O/'source-snapshots/pel-first-two';S.mkdir(parents=True,exist_ok=True)
def save(p,r):
 d=S/r;d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,d)
for p in [C/'FIRST-TWO-MANIFEST.json',C/M['contract']]:save(p,p.name)
for c in M['candidates']:
 n=c['module'];before=C/'before'/f'{n}.lean';after=C/'after'/f'{n}.lean'
 assert sha(before)==c['before_sha256'] and sha(after)==c['after_sha256']
 a=before.read_text();b=after.read_text()
 assert re.findall(r'^.*(?:import|set_option).*$',a,re.M)==re.findall(r'^.*(?:import|set_option).*$',b,re.M)
 if n=='FourRootCompletedHausdorff318':expected=a.replace('(hf:IsOpenEmbedding f)','(hf:Topology.IsOpenEmbedding f)')
 else:
  expected=a.replace('lemma normSq_positive:','lemma normSq_positive (hτ:0<τ.im):').replace('lemma coercive_positive:','lemma coercive_positive (hτ:0<τ.im):').replace('lemma energy_lower (x:','lemma energy_lower (hτ:0<τ.im) (x:')
  expected=expected.replace('    dsimp [m]\n    nlinarith','    calc\n      m*(U+V)=m*U+m*V:=mul_add _ _ _\n      _≤1*U+(1/Complex.normSq τ)*V:=add_le_add h1 h2\n      _=U+V/Complex.normSq τ:=by ring')
 assert expected==b
 save(before,Path('before')/before.name);save(after,Path('after')/after.name);save(C/f'{n}.diff',f'{n}.diff')
 for e in c['evidence']:
  art=arts[e['artifact_id']];assert art['workflow_run']['head_sha']==H and art['workflow_run']['id']==43592150561
  assert art['digest']=='sha256:'+e['zip_sha256']
  for k in ['zip','result','intake','log']:assert sha(W/e[k])==e[k+'_sha256']
  z=W/e['zip'];base=(W/e['result']).parents[2]
  with zipfile.ZipFile(z) as zz:
   assert zz.testzip() is None
   for name in zz.namelist():
    if not name.endswith('/'):assert zz.read(name)==(base/name).read_bytes()
  result=json.loads((W/e['result']).read_text());assert result['status']=='FAILED' and result['packet_sha256']==e['intake_sha256']
  assert result['commands'][-1]['module']==n and result['commands'][-1]['exit_code']==1
  packet=(W/e['result']).parent.name
  assert subprocess.check_output(['git','show',H+':'+X+packet+'/'+n+'.lean'],cwd=R)==before.read_bytes()
  assert subprocess.check_output(['git','show',H+':'+X+packet+'/intake.json'],cwd=R)==(W/e['intake']).read_bytes()
  for k in ['result','intake','log','artifact_metadata']:save(W/e[k],Path('evidence')/e['lane']/Path(e[k]).name)
for rel,h in M['primary_bindings'].items():
 p=C/rel;assert sha(p)==h;save(p,rel)
 if p.suffix=='.lean' and not p.name.startswith('Mathlib_'):
  paths=subprocess.check_output(['git','ls-tree','-r','--name-only',H,'--',X],cwd=R).decode().splitlines()
  paths=[q for q in paths if q.endswith('/'+p.name) and q.count('/')==5]
  assert any(subprocess.check_output(['git','show',H+':'+q],cwd=R)==p.read_bytes() for q in paths),p
for label,filename in [('Topology_Defs_Induced','Mathlib_Topology_Defs_Induced.lean'),('Topology_Maps_Basic','Mathlib_Topology_Maps_Basic.lean')]:
 meta=json.loads((C/'primary'/f'{label}-API.json').read_text());data=(C/'primary'/filename).read_bytes()
 assert '56a005855ea17e0b0958f73ec801ae140b0a1679' in meta['url'];assert base64.b64decode(meta['content'])==data
 assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==meta['sha']
r={'status':'PASS_SOURCE_AND_CURRENT_HUMAN_CONTRACT_ONLY','run':43592150561,'head':H,'modules':M['candidates'],'contract_sha256':M['contract_sha256'],'public_text_changes':'Native qualified private helper input; exactly three intended hτ binders restored. No claim of literal public telescope identity for coercivity.','local_lean_run':False,'candidate_hosted_pass':False,'future_packet_contract_review_complete':False,'source_bindings':{str(p.relative_to(O)):sha(p) for p in S.rglob('*') if p.is_file()}}
(O/'PEL-FIRST-TWO-SOURCE-CHECK.json').write_text(json.dumps(r,indent=2)+'\n');print('PASS exact2 candidates,3 own artifacts,all primary bytes,9 human obligations; no Lean')
