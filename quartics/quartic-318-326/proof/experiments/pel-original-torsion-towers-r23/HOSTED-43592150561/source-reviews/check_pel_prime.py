from pathlib import Path
import json,hashlib,subprocess,zipfile,shutil,re
B=Path('/workspace/scratch/41c6d5925c0e'); O=B/'review43592150561';W=B/'pel-run43592150561';C=W/'candidates';R=B/'pel-integration43586414080/repo';H='75be14ed25ed39f46289f1c69914810afd46068c';X='quartics/quartic-318-326/proof/experiments/';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();M=json.loads((C/'PRIME-MANIFEST.json').read_text());N=M['module'];assert M['base']==H and M['run']==43592150561;assert sha(C/M['contract'])==M['contract_sha256']
a=(C/'before'/f'{N}.lean').read_text();b=(C/'after'/f'{N}.lean').read_text();assert sha(C/'before'/f'{N}.lean')==M['before_sha256'] and sha(C/'after'/f'{N}.lean')==M['after_sha256']
old='''  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [residue,rows,product,conjugateCoefficients,prime] <;> ring'''
new='''  ext j
  change ((product (a+b) (conjugateCoefficients i)) (rows i j):ZMod (prime i))=
    ((product a (conjugateCoefficients i)) (rows i j):ZMod (prime i))+
      ((product b (conjugateCoefficients i)) (rows i j):ZMod (prime i))
  fin_cases i <;> fin_cases j <;>
    norm_num [rows,product,conjugateCoefficients,prime,Pi.add_apply] <;> push_cast <;> ring'''
assert a.count(old)==1
expected=a.replace(old,new).replace('  ext j\n  simp [residue,product]','  fin_cases i <;> ext j <;> fin_cases j <;>\n    norm_num [residue,rows,product,conjugateCoefficients,prime]');assert expected==b
S=O/'source-snapshots/pel-prime';S.mkdir(parents=True,exist_ok=True)
def save(p,r):
 d=S/r;d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,d)
for p in [C/'PRIME-MANIFEST.json',C/M['contract'],C/f'{N}.diff',C/'before'/f'{N}.lean',C/'after'/f'{N}.lean']:save(p,p.relative_to(C))
arts={x['id']:x for x in json.loads((O/'INDEPENDENT-GITHUB-ARTIFACTS-DIAGNOSTICS.json').read_text())['artifacts']}
for e in M['evidence']:
 art=arts[e['artifact_id']];assert art['workflow_run']['head_sha']==H and art['workflow_run']['id']==M['run'];assert art['digest']=='sha256:'+e['zip_sha256']
 for k in ['zip','result','log']:assert sha(W/e[k])==e[k+'_sha256']
 E=W/e['result'];result=json.loads(E.read_text());assert result['status']=='FAILED' and result['packet_sha256']==e['intake_sha256'];assert result['commands'][-1]['module']==N and result['commands'][-1]['exit_code']==1
 with zipfile.ZipFile(W/e['zip']) as z:
  assert z.testzip() is None
  for f in z.namelist():
   if not f.endswith('/'):assert z.read(f)==(E.parents[2]/f).read_bytes()
 packet=E.parent.name;assert subprocess.check_output(['git','show',H+':'+X+packet+'/'+N+'.lean'],cwd=R)==a.encode();intake=subprocess.check_output(['git','show',H+':'+X+packet+'/intake.json'],cwd=R);assert hashlib.sha256(intake).hexdigest()==e['intake_sha256']
 d=S/'evidence'/e['lane'];d.mkdir(parents=True,exist_ok=True);(d/'intake.json').write_bytes(intake);save(E,Path('evidence')/e['lane']/'RESULT.json');save(W/e['log'],Path('evidence')/e['lane']/f'{N}.log')
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',H,'--',X],cwd=R).decode().splitlines()
for rel,h in M['primary_bindings'].items():
 p=C/rel;assert sha(p)==h;save(p,rel)
 if p.suffix=='.lean' and not p.name.startswith('Mathlib_'):
  ps=[q for q in paths if q.endswith('/'+p.name) and q.count('/')==5];assert any(subprocess.check_output(['git','show',H+':'+q],cwd=R)==p.read_bytes() for q in ps),p
for rel,m in json.loads((C/'primary/REUSED-PRIMARY-PROVENANCE.json').read_text()).items():
 data=(C/rel).read_bytes();assert m['mathlib_commit']=='56a005855ea17e0b0958f73ec801ae140b0a1679';assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==m['git_blob_sha']
r={'status':'PASS_SOURCE_AND_CURRENT_HUMAN_CONTRACT_ONLY','manifest':M,'public_statements_definitions_options_unchanged':True,'local_lean_run':False,'hosted_candidate_pass':False,'source_bindings':{str(p.relative_to(O)):sha(p) for p in S.rglob('*') if p.is_file()}};(O/'PEL-PRIME-SOURCE-CHECK.json').write_text(json.dumps(r,indent=2)+'\n');print('PASS exact2 proof replacements,all4x2 cases retained,2 authentic own artifacts,all primary hashes and published consumers')
