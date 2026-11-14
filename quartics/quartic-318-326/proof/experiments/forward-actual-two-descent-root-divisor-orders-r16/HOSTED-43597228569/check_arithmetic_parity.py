from pathlib import Path
import hashlib,json,subprocess,zipfile,shutil,base64
B=Path('/workspace/scratch/41c6d5925c0e');W=B/'arithmetic-run43597228569';C=W/'candidates';O=B/'review43597228569';R=B/'pel-integration43592150561/repo';H='2af419e128047c483b3cdc0ba5e4d65c09d7c4ce';S=O/'source-snapshots/arithmetic-parity';S.mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();M=json.loads((C/'FORWARD_BINDINGS.json').read_text());assert M['head']==H and M['run']==43597228569
name='ScalarSmallPrimePreparation318.lean';a=C/'ScalarSmallPrimePreparation318.before.lean';b=C/name
assert sha(a)==M['before_sha256'] and sha(b)==M['after_sha256'];assert sha(C/'FORWARD_APPLICATION.md')==M['contract_sha256']
old='simp [Int.add_emod,Int.pow_emod,h]';new='simp [Int.add_emod,pow_two,Int.mul_emod,h]';assert a.read_text().count(old)==1;assert a.read_text().replace(old,new)==b.read_text()
def save(p,r):
 q=S/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
for p in [a,b,C/'ScalarSmallPrimePreparation318.diff',C/'FORWARD_APPLICATION.md',C/'FORWARD_BINDINGS.json']:save(p,p.name)
for row in M['own_packets']:
 lab=row['label'];packet=row['packet'];rel='quartics/quartic-318-326/proof/experiments/'+packet+'/';assert subprocess.check_output(['git','show',H+':'+rel+name],cwd=R)==a.read_bytes()==(C/(lab+'-'+a.name)).read_bytes()
 z=W/(lab+'.zip');art=W/(lab+'-artifact.json');j=json.loads(art.read_text());assert sha(z)==row['artifact_sha256'] and j['digest']=='sha256:'+sha(z);assert j['id']==row['artifact'] and j['workflow_run']['head_sha']==H and j['workflow_run']['id']==M['run']
 E=W/(lab+'-logs')/'progress-experiments'/packet;res=E/'RESULT.json';it=W/(lab+'-intake.before.json');r=json.loads(res.read_text());assert sha(it)==row['intake_sha256']==r['packet_sha256'];assert sha(res)==row['result_sha256'];assert subprocess.check_output(['git','show',H+':'+rel+'intake.json'],cwd=R)==it.read_bytes();last=r['commands'][-1];assert last['module']==M['module'] and last['exit_code']==124
 with zipfile.ZipFile(z) as zz:
  assert zz.testzip() is None
  for n in zz.namelist():
   if not n.endswith('/'):assert zz.read(n)==(W/(lab+'-logs')/n).read_bytes()
 for p in [z,art,it,res,E/'logs'/(M['module']+'.log')]:save(p,'evidence/'+lab+'/'+p.name)
D=next((W/'descent-logs').rglob('DIAGNOSTIC.json'));assert sha(D)==M['diagnostic_json_sha256'];d=json.loads(D.read_text());assert d['actual_head']==H and d['original_source_sha256']==sha(a);assert d['variants'][0]['exit_code']==0
for i,v in enumerate(d['variants']):
 assert v['admitted'] is False and v['proof_acceptance'] is False
 assert sha(D.with_name(v['variant']+'.lean.txt'))==v['source_sha256']
 if i in [1,2]:assert v['exit_code']==1 and v['limit'] is None and 'Unknown constant `Int.pow_emod`' in D.with_name(v['variant']+'.log').read_text()
 if i in [3,4,5]:assert v['exit_code']==-9 and v['limit']=='SCRATCH_LOG_LIMIT' and v['bytes']==2097152
 if i==6:assert v['historical_source_different'] and v['limit']=='SCRATCH_WALL_LIMIT'
for p in D.parent.iterdir():
 if p.is_file():save(p,'evidence/diagnostic/'+p.name)
for k in ['Bootstrap','Basic','Lemmas','Pow']:
 p=C/'primary'/('Lean-Int-DivMod-'+k+'.lean');jpath=p.with_suffix('.json');j=json.loads(jpath.read_text());assert base64.b64decode(j['content'])==p.read_bytes();assert hashlib.sha1(b'blob '+str(p.stat().st_size).encode()+b'\0'+p.read_bytes()).hexdigest()==j['sha'];save(p,'native/'+p.name);save(jpath,'native/'+jpath.name)
assert 'theorem mul_emod (a b n : Int)' in (C/'primary/Lean-Int-DivMod-Bootstrap.lean').read_text()
rel='quartics/quartic-318-326/proof/experiments/'+M['own_packets'][0]['packet']+'/'
for n in ['ScalarPackedLocalUnit318.lean','ScalarPolePreparation318.lean','ScalarForwardWitness318.lean','PreparedTwistSource318.lean','PreparedLucasSource318.lean','AllScalarSupportPreparation318.lean']:
 p=C/'primary'/n;assert subprocess.check_output(['git','show',H+':'+rel+n],cwd=R)==p.read_bytes();save(p,'primary/'+n)
j={'status':'PASS_SOURCE_AND_CURRENT_HUMAN_CONTRACT_ONLY','module':M['module'],'before':sha(a),'after':sha(b),'contract':M['contract_sha256'],'run':M['run'],'head':H,'exact_one_simp_list_delta':True,'all_other_source_bytes_unchanged':True,'full_module_timeout_fixed':False,'local_lean_run':False,'candidate_hosted_pass':False,'future_packet_contract_review_complete':False,'source_bindings':{str(p.relative_to(O)):sha(p) for p in sorted(S.rglob('*')) if p.is_file()}}
(O/'ARITHMETIC-PARITY-SOURCE-CHECK.json').write_text(json.dumps(j,indent=2)+'\n');print('PASS exact one simp list; two own artifact/intake/result/source identities; authentic seven scratch outcomes; native Git blobs; exact producers/consumers. No Lean, no timeout-resolution claim.')
