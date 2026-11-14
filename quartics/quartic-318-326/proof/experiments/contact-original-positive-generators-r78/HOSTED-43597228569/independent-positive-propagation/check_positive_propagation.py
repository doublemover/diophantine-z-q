from pathlib import Path
import json,hashlib,subprocess,sys,re,copy,tempfile,shutil,zipfile
R=Path('/workspace/scratch/41c6d5925c0e');W=Path(__file__).resolve().parent
repo=R/'pel-integration43592150561/repo';owner=R/'arithmetic-run43597228569';name='contact-original-positive-generators-r77';old='contact-original-positive-generators-r76';p=owner/'successors'/name;before=repo/'quartics/quartic-318-326/proof/experiments'/old
head='2af419e128047c483b3cdc0ba5e4d65c09d7c4ce';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD']).decode().strip()==head
assert sha(p/'APPLICATION.json')=='eec04a14bd734cde417ff3f0775a3401f654223ccd66a0c57f0239c5eafbec1e'
a=json.loads((p/'APPLICATION.json').read_text());d=json.loads((p/'intake.json').read_text());od=json.loads((before/'intake.json').read_text())
assert a['author']!='geometry_repair_resume'
assert (a['packet'],a['predecessor'],a['source_commit'],a['run_id'])==(name,old,head,43597228569)
for k in ['local_lean_run','kernel_verified','independently_accepted','new_source_acceptance','full_arithmetic_theorem_proved']:assert a[k] is False,k
assert set(a['obligations'])=={'source_statement','constructed_objects','index_set_coverage','transition_maps','limiting_object_identity','coefficient_conventions','local_conditions','exceptional_cases','downstream_consumption'}
for ob in a['obligations'].values():
 for k in ['required_input','constructed_input','justification']:assert ob[k].strip()
 for k in ['source_references','evidence']:
  assert ob[k]
  for q in ob[k]:assert (p/q).is_file(),q
assert len(d['order'])==107 and d['order']==od['order']
assert set(d['files'])==set(od['files'])=={x.name for x in p.glob('*.lean')}
cur={n+'.lean':sha(p/(n+'.lean')) for n in d['order']};prior={n+'.lean':sha(before/(n+'.lean')) for n in d['order']}
for n,h in prior.items():
 b=subprocess.check_output(['git','-C',str(repo),'show',head+':quartics/quartic-318-326/proof/experiments/'+old+'/'+n]);assert hashlib.sha256(b).hexdigest()==h
 assert od['files'][n]['sha256']==h
assert cur==a['sources'];changed=[n for n in d['order'] if cur[n+'.lean']!=prior[n+'.lean']];unchanged=[n for n in d['order'] if n not in changed]
assert changed==['ContactOriginalLaurentBoundary318'] and len(unchanged)==106
assert d['revision_classification_schema']==1 and d['new_modules']==[] and d['changed_modules']==changed and d['unchanged_producer_modules']==unchanged
for k,h in a['bindings'].items():assert sha(p/k)==h,k
cp=json.loads((p/'SOURCE-COPIES.json').read_text());assert cp['predecessor_intake_sha256']==sha(before/'intake.json') and cp['predecessor_application_sha256']==sha(before/'APPLICATION.json')
assert cp['unchanged_sources']=={n+'.lean':cur[n+'.lean'] for n in unchanged}
module='ContactOriginalLaurentBoundary318.lean';assert cur[module]=='0981ca2be0e2d41fcf341201ca59bc31b8543ec4c688eea0060d7e7639047fcf'
host=p/'HOSTED-43597228569';assert sha(host/'SOURCE.lean.after')==cur[module] and sha(host/'SOURCE.lean.before')==prior[module]
oldtext=(before/module).read_text();newtext=(p/module).read_text()
for label in ['reindex_negative','negative_image','zero_iff','kernel_eq_boundary']:
 pat=r'(?m)^lemma '+label+r'\b[\s\S]*?:= by'
 assert re.search(pat,oldtext).group()==re.search(pat,newtext).group(),label
assert re.search(r'lemma zero_iff[\s\S]*?(?=/-- Exact geometric)',oldtext).group()==re.search(r'lemma zero_iff[\s\S]*?(?=/-- Exact geometric)',newtext).group()
assert re.findall(r'^set_option.*$',oldtext,re.M)==re.findall(r'^set_option.*$',newtext,re.M)
assert re.findall(r'^public import all (.*)$',newtext,re.M)==['ContactOriginalCohomologyCoordinates318','OriginalFiniteBasisBaseChange318','ContactOriginalLaurentCoordinates318','OriginalLineMayerVietorisQuotient318']
m=json.loads((host/'INDEPENDENT-SOURCE-BINDINGS.json').read_text());assert m['after_sha256']==cur[module] and m['contract_sha256']==sha(p/'APPLICATION.md')
for k,h in m['source_bindings'].items():assert sha(host/k)==h,k
assert sha(host/'INDEPENDENT-SOURCE-REVIEW.md')==m['report_sha256']
for q in (host/'primary-sources').glob('*.lean'):assert q.read_bytes()==(before/q.name).read_bytes(),q.name
api=json.loads((host/'ARTIFACT_PROVENANCE.json').read_text());assert api['id']==14115292804 and api['workflow_run']['id']==43597228569 and api['workflow_run']['head_sha']==head
z=owner/'positive.zip';assert 'sha256:'+sha(z)==api['digest'] and z.stat().st_size==api['size_in_bytes']
with zipfile.ZipFile(z) as archive:
 assert archive.testzip() is None
 for n in archive.namelist():
  assert not Path(n).is_absolute() and '..' not in Path(n).parts
  if n.endswith('/'):continue
  suffix=n.split('/'+old+'/',1)[1]
  assert archive.read(n)==(host/'own-hosted-evidence'/suffix).read_bytes(),n
result=json.loads((host/'own-hosted-evidence/RESULT.json').read_text())
assert result['packet']==old and result['packet_sha256']==sha(before/'intake.json') and result['status']=='FAILED'
assert result['commands'][-2:]==[{'exit_code':0,'module':'ContactOriginalCohomologyCoordinates318','seconds':32.226},{'exit_code':1,'module':'ContactOriginalLaurentBoundary318','seconds':7.186}]
# Native static checker executes on a temporary copy, never the frozen owner tree.
sys.path.insert(0,str(repo/'scripts'));import check_progress_experiment as native
controls=[]
with tempfile.TemporaryDirectory(dir=W,prefix='native-') as td:
 root=Path(td);np=root/name;np.mkdir();op=root/old;op.mkdir()
 for n in ['APPLICATION.json','intake.json',*cur,*a['bindings']]:
  q=np/n;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p/n,q)
 for n in ['intake.json',*prior]:shutil.copy2(before/n,op/n)
 _,nd,direct,external=native.packet(name,native.ci.derive_plan(),root)
 native.check_application_bindings(np)
 for key in ['changed_modules','revised_modules','modified_predecessor_modules','reused_modules','unchanged_predecessor_modules','exact_predecessor_modules','unchanged_producer_modules','new_modules']:
  bad=copy.deepcopy(nd);bad[key]=['__false_alias__']
  try:native.check_revision_classifications(np,bad,root)
  except ValueError as e:assert 'classification mismatch' in str(e);controls.append(key)
  else:raise AssertionError('false alias accepted '+key)
# Snapshot exactly the inspected current contract, source closure and all bound evidence.
snap=W/'source-snapshots'/name;snap.mkdir(parents=True,exist_ok=True)
for n in ['APPLICATION.json','intake.json','README.md','APPLICATION.md',*cur,*a['bindings']]:
 q=snap/n;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p/n,q)
oldp=W/'source-snapshots'/old;oldp.mkdir(parents=True,exist_ok=True)
for n in ['APPLICATION.json','intake.json',module]:shutil.copy2(before/n,oldp/n)
shutil.copy2(z,W/'positive.zip')
assert sha(p/'APPLICATION.json')=='eec04a14bd734cde417ff3f0775a3401f654223ccd66a0c57f0239c5eafbec1e'
r={'status':'PASS_STATIC_PROPAGATION_AND_SOURCE_IDENTITY_ONLY','reviewer':'geometry_repair_resume','author':a['author'],'packet':name,'predecessor':old,'head':head,'run':43597228569,'application_sha256':sha(p/'APPLICATION.json'),'intake_sha256':sha(p/'intake.json'),'readme_sha256':sha(p/'README.md'),'human_contract_sha256':sha(p/'APPLICATION.md'),'sources':cur,'before_sources':prior,'source_count':107,'changed_modules':changed,'unchanged_source_count':106,'exact_current_application_bindings':len(a['bindings']),'source_review_companions_verified':len(m['source_bindings']),'native_alias_negative_controls':controls,'direct_baseline_dependencies':len(direct),'external_imports':len(external),'own_artifact':api['id'],'own_zip_sha256':sha(z),'own_result_sha256':sha(host/'own-hosted-evidence/RESULT.json'),'local_lean_run':False,'hosted_candidate_pass':False,'publication_index_review':'SEPARATE_PENDING'}
(W/'POSITIVE-PROPAGATION-CHECK.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k not in ['sources','before_sources']},indent=2))
