from pathlib import Path
import json,hashlib,subprocess,sys,re,copy,tempfile,shutil,zipfile,io
R=Path(__file__).resolve().parent.parent;W=Path(__file__).resolve().parent;repo=R/'pel-followup43603177874/repo';owner=R/'arithmetic-run43605497804';head='4c5562395a9891e0d79fa5808926ebf9b2781470';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();prefix='quartics/quartic-318-326/proof/experiments/'
assert subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD']).decode().strip()==head
frozen=json.loads((owner/'FROZEN_PROPAGATION_TARGETS.json').read_text());mapping=json.loads((owner/'FORWARD_SUCCESSOR_MAP.json').read_text())
sys.path.insert(0,str(repo/'scripts'));import check_progress_experiment as native
plan=native.ci.derive_plan();rows=[]
for frozenrow,mp in zip(frozen,mapping):
 name=mp['successor'];old=mp['predecessor'];p=owner/'successors'/name;before=repo/prefix/old;assert frozenrow['packet']==name
 assert sha(p/'APPLICATION.json')==frozenrow['application_sha256'];assert sha(p/'intake.json')==frozenrow['intake_sha256']
 a=json.loads((p/'APPLICATION.json').read_text());d=json.loads((p/'intake.json').read_text());od=json.loads((before/'intake.json').read_text())
 assert a['author']!='geometry_repair_resume';assert (a['packet'],a['predecessor'],a['source_commit'],a['run_id'])==(name,old,head,43605497804)
 for k in ['local_lean_run','kernel_verified','independently_accepted','new_source_acceptance','full_arithmetic_theorem_proved']:assert a[k] is False
 assert len(a['obligations'])==9
 for ob in a['obligations'].values():
  for k in ['required_input','constructed_input','justification']:assert ob[k].strip()
  for k in ['source_references','evidence']:
   assert ob[k]
   for q in ob[k]:assert (p/q).is_file(),q
 assert len(d['order'])==frozenrow['sources'] and d['order']==od['order'];assert set(d['files'])==set(od['files'])=={x.name for x in p.glob('*.lean')}
 # Batch-read exact Git objects, not merely local intake labels.
 names=['intake.json','APPLICATION.json',*od['files']];queries=[head+':'+prefix+old+'/'+n for n in names]
 raw=subprocess.check_output(['git','-C',str(repo),'cat-file','--batch'],input=('\n'.join(queries)+'\n').encode());buf=io.BytesIO(raw);prior={}
 for n in names:
  hdr=buf.readline().split();assert hdr[1]==b'blob';size=int(hdr[2]);b=buf.read(size);assert buf.read(1)==b'\n';assert b==(before/n).read_bytes(),n
  if n.endswith('.lean'):prior[n]=hashlib.sha256(b).hexdigest();assert prior[n]==od['files'][n]['sha256']
 cur={n+'.lean':sha(p/(n+'.lean')) for n in d['order']};assert cur==a['sources'];changed=[n for n in d['order'] if cur[n+'.lean']!=prior[n+'.lean']];unchanged=[n for n in d['order'] if n not in changed];assert changed==['ScalarSmallPrimePreparation318'];assert d['revision_classification_schema']==1
 for n,h in cur.items():assert d['files'][n]['sha256']==h
 for k,h in a['bindings'].items():assert sha(p/k)==h,k
 cp=json.loads((p/'SOURCE-COPIES.json').read_text());assert cp['predecessor_intake_sha256']==sha(before/'intake.json') and cp['predecessor_application_sha256']==sha(before/'APPLICATION.json');assert cp['unchanged_sources']=={n+'.lean':cur[n+'.lean'] for n in unchanged}
 module='ScalarSmallPrimePreparation318.lean';assert cur[module]=='6903b836d5f5a08954574cc67bfb9981ddba7ab60b9bb3b973362450da82c2e3';host=p/'HOSTED-43605497804'
 assert sha(host/'SOURCE.lean.before')==prior[module]=='e808d212ea6cd4edc8fe7ca8b839b19b80480adfacddf0671d227ce6ee8bec9e';assert sha(host/'SOURCE.lean.after')==cur[module]
 oldtext=(before/module).read_text();newtext=(p/module).read_text();block=re.search(r'/-- The elementary unit facts[\s\S]*?constructor <;> omega\n\n',newtext).group()
 inverse=newtext.replace(block,'').replace('  have hu := multiplier_units k₂ k₃ k₁₇\n','').replace('hu.2.2 using','(by omega) using').replace('hu.2.1 using','(by omega) using').replace('hu.1 using','(by omega) using');assert inverse==oldtext
 assert re.findall(r'^set_option.*$',oldtext,re.M)==re.findall(r'^set_option.*$',newtext,re.M)
 for q in (host/'primary-sources').glob('*.lean'):assert q.read_bytes()==(before/q.name).read_bytes(),q.name
 m=json.loads((host/'INDEPENDENT-SOURCE-BINDINGS.json').read_text());assert m['candidate_sha256']==cur[module] and m['human_contract_sha256']==sha(p/'APPLICATION.md');assert sha(host/'INDEPENDENT-SOURCE-REVIEW.md')==m['report_sha256']
 for k,h in {**m['source_bindings'],**m['reviewer_evidence']}.items():assert sha(host/'source-review-evidence'/k)==h,k
 api=json.loads((host/'ARTIFACT_PROVENANCE.json').read_text());assert api['id']==mp['artifact_id'] and api['workflow_run']['id']==43605497804 and api['workflow_run']['head_sha']==head
 z=owner/('descent.zip' if 'two-descent' in name else 'weighted-retry.zip');assert 'sha256:'+sha(z)==api['digest'] and z.stat().st_size==api['size_in_bytes']
 with zipfile.ZipFile(z) as zip:
  assert zip.testzip() is None
  for n in zip.namelist():
   assert not Path(n).is_absolute() and '..' not in Path(n).parts
   if n.endswith('/'):continue
   suffix=n.split('/'+old+'/',1)[1];assert zip.read(n)==(host/'own-hosted-evidence'/suffix).read_bytes(),n
 result=json.loads((host/'own-hosted-evidence/RESULT.json').read_text());assert result['status']=='FAILED' and result['packet']==old and result['packet_sha256']==sha(before/'intake.json');assert all(x['exit_code']==0 for x in result['commands'][:-1]);assert result['commands'][-1]['module']=='ScalarSmallPrimePreparation318' and result['commands'][-1]['exit_code']==124;assert [x['module'] for x in result['commands']]==od['order'][:len(result['commands'])]
 support=host/'supporting-descent-diagnostics';D=json.loads((support/'DIAGNOSTIC.json').read_text());assert D['packet']=='forward-actual-two-descent-root-divisor-orders-r16' and D['actual_head']==head and len(D['variants'])==5 and D['seconds_per_probe']==90;assert D['production_limits_changed'] is False and D['writes_olean'] is False
 own_descent=owner/'successors/forward-actual-two-descent-root-divisor-orders-r17/HOSTED-43605497804/own-hosted-evidence/scratch-small-prime-decidable'
 for q in support.iterdir():assert q.read_bytes()==(own_descent/q.name).read_bytes()
 # Native validators and deliberate stale aliases, only in isolated real copies.
 controls=[]
 with tempfile.TemporaryDirectory(dir=W,prefix='native-') as td:
  nr=Path(td);np=nr/name;op=nr/old;np.mkdir();op.mkdir()
  for n in ['APPLICATION.json','intake.json',*cur,*a['bindings']]:
   dest=np/n;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p/n,dest)
  for n in ['intake.json',*prior]:shutil.copy2(before/n,op/n)
  _,nd,direct,external=native.packet(name,plan,nr);native.check_application_bindings(np)
  for key in ['changed_modules','revised_modules','modified_predecessor_modules','reused_modules','unchanged_predecessor_modules','exact_predecessor_modules','unchanged_producer_modules','new_modules']:
   bad=copy.deepcopy(nd);bad[key]=['__false_alias__']
   try:native.check_revision_classifications(np,bad,nr)
   except ValueError as e:assert 'classification mismatch' in str(e);controls.append(key)
   else:raise AssertionError('stale alias accepted '+key)
 snap=W/'source-snapshots'/name;snap.mkdir(parents=True,exist_ok=True)
 for n in ['APPLICATION.json','intake.json',*cur,*a['bindings']]:
  dest=snap/n;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p/n,dest)
 oldsnap=W/'source-snapshots'/old;oldsnap.mkdir(parents=True,exist_ok=True)
 for n in ['APPLICATION.json','intake.json',module]:shutil.copy2(before/n,oldsnap/n)
 shutil.copy2(z,W/z.name)
 assert sha(p/'APPLICATION.json')==frozenrow['application_sha256']
 rows.append({'packet':name,'predecessor':old,'current_application_sha256':sha(p/'APPLICATION.json'),'intake_sha256':sha(p/'intake.json'),'readme_sha256':sha(p/'README.md'),'human_contract_sha256':sha(p/'APPLICATION.md'),'source_count':len(cur),'changed':changed,'unchanged_count':len(unchanged),'sources':cur,'before_sources':prior,'native_controls':controls,'application_bindings':len(a['bindings']),'source_review_companions':len(m['source_bindings'])+len(m['reviewer_evidence']),'own_artifact':api['id'],'own_zip_sha256':sha(z),'own_result_sha256':sha(host/'own-hosted-evidence/RESULT.json'),'own_first_failure':result['commands'][-1],'supporting_diagnostic_packet':D['packet'],'supporting_diagnostic_sha256':sha(support/'DIAGNOSTIC.json'),'direct_dependencies':len(direct),'external_imports':len(external)})
result={'reviewer':'geometry_repair_resume','author':'arithmetic_repair_resume','head':head,'run':43605497804,'status':'PASS_SOURCE_CURRENT_CONTRACT_PROPAGATION_ONLY','packets':rows,'exact_source_inverse':True,'local_lean_run':False,'kernel_verified':False,'production_timeout_resolved':False,'publication_index_review':'SEPARATE'}
(W/'FORWARD-PROPAGATION-CHECK.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({**result,'packets':[{k:v for k,v in x.items() if k not in ['sources','before_sources']} for x in rows]},indent=2))
