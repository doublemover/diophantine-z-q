from pathlib import Path
import json,hashlib,subprocess,shutil,zipfile,re
B=Path('/workspace/scratch/41c6d5925c0e');W=B/'pel-run43597228569';O=B/'review43597228569';R=B/'pel-integration43592150561/repo';H='2af419e128047c483b3cdc0ba5e4d65c09d7c4ce';X='quartics/quartic-318-326/proof/experiments/'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
S=O/'source-snapshots/pel-first-two'; S.mkdir(parents=True,exist_ok=True)
def save(p,r):
 d=S/r;d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,d)
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',H,'--',X],cwd=R).decode().splitlines();checked=[]
for tag in ['SIGN','COERCIVITY']:
 m=W/'candidates'/f'{tag}-MANIFEST.json';M=json.loads(m.read_text());assert M['base']==H and M['run']==43597228569
 save(m,m.name);n=M['module'];a=(W/'candidates/before'/f'{n}.lean').read_text();b=(W/'candidates/after'/f'{n}.lean').read_text()
 assert re.findall(r'^.*(?:import|set_option).*$',a,re.M)==re.findall(r'^.*(?:import|set_option).*$',b,re.M)
 if tag=='SIGN':
  exp=a.replace('    rw [p.property.1,mul_one,←pow_two,coordinate_square],by','    change coordinate (F:=ℂ) 0 g*coordinate (F:=ℂ) 0 g*p.val.2 0=1\n    rw [p.property.1,mul_one,←pow_two,coordinate_square],by').replace('    rw [s.property.1,mul_one,←pow_two,coordinate_square],by','    change coordinate (F:=ℂ) 0 g*coordinate (F:=ℂ) 0 g*s.val 0=1\n    rw [s.property.1,mul_one,←pow_two,coordinate_square],by')
  exp=exp.replace('    apply Prod.ext rfl\n    funext i\n    change coordinate (F:=ℂ) i g*(coordinate (F:=ℂ) i g*p.val.2 i)=p.val.2 i\n    rw [←mul_assoc,←pow_two,coordinate_square,one_mul]','    apply Prod.ext\n    · rfl\n    · funext i\n      change coordinate (F:=ℂ) i g*(coordinate (F:=ℂ) i g*p.val.2 i)=p.val.2 i\n      rw [←mul_assoc,←pow_two,coordinate_square,one_mul]')
 else:exp=a.replace('  have hpos:0≤alpha*τ.im/20:=by positivity','  have hpos:0≤alpha*τ.im/20:=\n    (div_pos (mul_pos alpha_pos hτ) (by norm_num : (0:ℝ)<20)).le')
 assert exp==b
 for rel,h in M['source_bindings'].items():
  p=W/rel;assert sha(p)==h;save(p,rel)
  if '/primary/' in rel:
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
J={'status':'PASS_SOURCE_AND_CURRENT_HUMAN_CONTRACT_ONLY','run':43597228569,'head':H,'modules':checked,'local_lean_run':False,'candidate_hosted_pass':False,'future_packet_contract_review_complete':False,'source_bindings':{str(p.relative_to(O)):sha(p) for p in S.rglob('*') if p.is_file()}}
(O/'PEL-FIRST-TWO-SOURCE-CHECK.json').write_text(json.dumps(J,indent=2)+'\n');print('PASS: exact two deltas, three own artifact ZIPs/results/intakes, published before and primary bytes; no Lean.')
