from pathlib import Path
import json,hashlib,subprocess,zipfile,shutil,base64
B=Path('/workspace/scratch/41c6d5925c0e');O=B/'review43592150561';W=B/'arithmetic-run43592150561';C=W/'candidates';R=B/'pel-integration43586414080/repo';H='75be14ed25ed39f46289f1c69914810afd46068c';X='quartics/quartic-318-326/proof/experiments/contact-original-positive-generators-r75';N='ContactOriginalCohomologyCoordinates318';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
M=json.loads((C/'POSITIVE_BINDINGS.json').read_text());assert M['head']==H and M['run']==43592150561
before=C/(N+'.before.lean');after=C/(N+'.lean');assert sha(before)==M['before_sha256'] and sha(after)==M['after_sha256'];assert sha(C/'POSITIVE_APPLICATION.md')==M['contract_sha256']
a=before.read_text();assert a.count('    AddEquiv.apply_symm_apply,LinearEquiv.coe_toAddEquiv]')==2;assert a.replace('    AddEquiv.apply_symm_apply,LinearEquiv.coe_toAddEquiv]','    AddEquiv.apply_symm_apply,LinearEquiv.coe_toAddEquiv,\n    LinearEquiv.coe_addEquiv_apply]')==after.read_text()
assert subprocess.check_output(['git','show',H+':'+X+'/'+N+'.lean'],cwd=R)==before.read_bytes()
art=next(x for x in json.loads((O/'INDEPENDENT-GITHUB-ARTIFACTS-DIAGNOSTICS.json').read_text())['artifacts'] if x['id']==M['artifact_id']);assert art['workflow_run']['head_sha']==H and art['workflow_run']['id']==M['run'];assert sha(W/'positive.zip')==art['digest'].removeprefix('sha256:')
with zipfile.ZipFile(W/'positive.zip') as z:
 assert z.testzip() is None
 for f in z.namelist():
  if not f.endswith('/'):assert z.read(f)==(W/'positive-logs'/f).read_bytes()
E=W/'positive-logs/progress-experiments/contact-original-positive-generators-r75';result=json.loads((E/'RESULT.json').read_text());assert result['status']=='FAILED' and result['packet_sha256']==M['intake_sha256'];assert result['commands'][-1]['module']==N and result['commands'][-1]['exit_code']==1
assert hashlib.sha256(subprocess.check_output(['git','show',H+':'+X+'/intake.json'],cwd=R)).hexdigest()==M['intake_sha256'];assert sha(W/'positive-intake.before.json')==M['intake_sha256']
S=O/'source-snapshots/arithmetic-positive';S.mkdir(parents=True,exist_ok=True)
def save(p,r):
 d=S/r;d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,d)
for p in [before,after,C/'POSITIVE_APPLICATION.md',C/'POSITIVE_BINDINGS.json',C/(N+'.diff')]:save(p,p.name)
for p in [W/'positive-intake.before.json',W/'positive-artifact.json',E/'RESULT.json',E/'logs'/f'{N}.log']:save(p,Path('evidence')/p.name)
for f,h in M['primary_sources'].items():
 p=C/'primary'/f;assert sha(p)==h;save(p,Path('primary')/f)
 if f.endswith('.lean') and not f.startswith('Mathlib'):
  assert subprocess.check_output(['git','show',H+':'+X+'/'+f],cwd=R)==p.read_bytes()
meta=json.loads((C/'primary/Mathlib-Algebra-Module-Equiv-Defs.metadata.json').read_text());data=(C/'primary/Mathlib-Algebra-Module-Equiv-Defs.lean').read_bytes();assert '56a005855ea17e0b0958f73ec801ae140b0a1679' in meta['url'];assert base64.b64decode(meta['content'])==data;assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==meta['sha']
r={'status':'PASS_SOURCE_AND_HUMAN_CONTRACT_ONLY','run':M['run'],'head':H,'before_sha256':M['before_sha256'],'after_sha256':M['after_sha256'],'contract_sha256':M['contract_sha256'],'own_artifact':art,'public_statements_definitions_imports_options_unchanged':True,'local_lean_run':False,'hosted_candidate_pass':False,'source_bindings':{str(p.relative_to(O)):sha(p) for p in S.rglob('*') if p.is_file()}}
(O/'ARITHMETIC-POSITIVE-SOURCE-CHECK.json').write_text(json.dumps(r,indent=2)+'\n');print('PASS exact2 simp additions, authentic own evidence, pinned evaluation theorem, published producer/consumer bytes')
