import sys,json,hashlib,subprocess,re,tempfile,copy,shutil
from pathlib import Path
B=Path('/workspace/scratch/41c6d5925c0e'); mode=sys.argv[1]; GEO=mode=='geometry'; O=B/('review43588277165' if GEO else 'review43586414080'); R=B/'geometry-integration43583139321/repo'; REL='quartics/quartic-318-326/proof/experiments'; HEAD='83851e60e8b2e42cab7eeb55831b45c41d20f2d5'
sys.path.insert(0,str(R/'scripts'));import check_progress_experiment as ce
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
plan=ce.ci.derive_plan(); prefix='GEOMETRY' if GEO else 'ARITHMETIC-PREVENTIVE'
if GEO:
 root=B/'geometry-run43588277165/successors'; items=[{'successor':'height-normalized-valuative-center-r66','predecessor':'height-normalized-valuative-center-r65','application_sha256':'afb11b72f335b09e7c9c4832c7c6cca1672d488686c284d1c2773300820bb8ee'}]; preds=R/REL
 reviewed={x['module']:x for x in json.loads((O/'SOURCE-CHECK.json').read_text())['candidates']}
else:
 root=B/'arithmetic-lexical-preflight43586414080/successors'; items=json.loads((root.parent/'SUCCESSOR_MAP.json').read_text());preds=B/'arithmetic-run43586414080/successors'
 reviewed={x['module']:x for x in json.loads((O/'ARITHMETIC-PREVENTIVE-CHECK.json').read_text())['candidates']}
 handoff=json.loads((preds.parent/'FINAL_HANDOFF.json').read_text());ph={x['packet']:x for x in handoff['packets']}
result={'scope':prefix,'local_lean_run':False,'kernel_verified':False,'baseline_modules':len(plan['module_order']),'packets':[]}
with tempfile.TemporaryDirectory(prefix=prefix.lower()+'-',dir=O) as td:
 t=Path(td)
 for item in items:
  name=item['successor'];old=item['predecessor'];p=root/name;q=preds/old;a=json.loads((p/'APPLICATION.json').read_text());d=json.loads((p/'intake.json').read_text());pd=json.loads((q/'intake.json').read_text())
  assert sha(p/'APPLICATION.json')==item['application_sha256'];assert a['predecessor']==old
  assert d['revision_classification_schema']==1 and d['order']==pd['order']
  assert {f.name for f in p.glob('*.lean')}==set(d['files'])==set(pd['files'])
  if GEO:
   assert subprocess.check_output(['git','show',f'{HEAD}:{REL}/{old}/intake.json'],cwd=R)==(q/'intake.json').read_bytes()
  else:
   cp=json.loads((p/'SOURCE-COPIES.json').read_text());assert cp['predecessor_application_sha256']==sha(q/'APPLICATION.json')==ph[old]['application_sha256'];assert cp['predecessor_intake_sha256']==sha(q/'intake.json')==ph[old]['intake_sha256'];assert cp['predecessor_commit_at_packaging'] is None
   assert (p/'PREVENTIVE-LEXICAL-SWEEP/PREDECESSOR-OWNER-HANDOFF.json').read_bytes()==(preds.parent/'FINAL_HANDOFF.json').read_bytes()
   assert a['predecessor_commit_at_packaging'] is None and a['no_new_hosted_result_claimed'] is True
   for flag in ['local_lean_run','kernel_verified','independently_accepted','new_source_acceptance','full_arithmetic_theorem_proved']:assert a[flag] is False
  changes=[];sources={};before={};spaces=0
  for n in d['order']:
   f=n+'.lean';bb=(q/f).read_bytes();aa=(p/f).read_bytes();bh=sha(q/f);ah=sha(p/f);sources[f]=ah;before[f]=bh
   assert ah==d['files'][f]['sha256'] and bh==pd['files'][f]['sha256']
   if aa!=bb:
    changes.append(n);v=reviewed[n];assert bh==v['before_sha256'] and ah==v.get('candidate_sha256',v.get('after_sha256'))
    assert re.findall(rb'^\s*set_option\s+.*$',aa,re.M)==re.findall(rb'^\s*set_option\s+.*$',bb,re.M)
    if not GEO:
     assert re.sub(rb'\s',b'',aa)==re.sub(rb'\s',b'',bb);spaces+=len(aa)-len(bb)
     assert cp['changed_sources'][f]=={'before_sha256':bh,'after_sha256':ah,'classification':'PREVENTIVE_UNOBSERVED'}
  assert set(changes)==set(reviewed);assert a['sources']==sources
  if not GEO:assert spaces==17;assert set(a['preventive_modules'])==set(reviewed);assert (p/'ScalarPolePreparation318.lean').read_bytes()==(q/'ScalarPolePreparation318.lean').read_bytes()
  (t/name).symlink_to(p,target_is_directory=True);(t/old).mkdir()
  for f in ['intake.json']+list(pd['files']):shutil.copy2(q/f,t/old/f)
  ce.packet(name,plan,t);negative=[]
  for k in ['changed_modules','revised_modules','modified_predecessor_modules','reused_modules','unchanged_predecessor_modules','exact_predecessor_modules','unchanged_producer_modules','new_modules']:
   if k not in d:continue
   bad=copy.deepcopy(d);bad[k]=bad[k]+['FalseIndependentControl318'] if isinstance(bad[k],list) else bad[k]+1
   try:ce.check_revision_classifications(t/name,bad,t)
   except ValueError:negative.append(k)
   else:raise AssertionError(('false alias accepted',name,k))
  rows=a['obligations'];rows=list(rows.values()) if isinstance(rows,dict) else rows;assert len(rows)==9
  for row in rows:
   assert all(row.get(k) for k in ['required_input','constructed_input','justification','evidence'])
   refs=row.get('source_references',row.get('source_refs'));assert refs
   for ref in refs+row['evidence']:assert (p/ref.split(':',1)[0]).is_file(),(name,ref)
  for f,h in a['bindings'].items():assert sha(p/f)==h,(name,f)
  own={}
  if GEO:
   rr=p/'HOSTED-43588277165/center-RESULT.json';j=json.loads(rr.read_text());assert j['packet']==old and j['packet_sha256']==sha(q/'intake.json') and j['status']=='FAILED';own={'path':str(rr.relative_to(p)),'sha256':sha(rr),'packet_sha256':j['packet_sha256']}
   assert sha(p/'INHERITANCE.json')==a['bindings']['INHERITANCE.json'];assert a['local_lean_run'] is False and a['full_arithmetic_theorem_proved'] is False
  else:
   # Historical results must not masquerade as results for the unpublished immediate predecessor/new successor.
   for f in p.rglob('*RESULT*.json'):
    try:j=json.loads(f.read_text())
    except (ValueError,UnicodeError):continue
    if isinstance(j,dict):assert j.get('packet') not in [old,name],(name,'fabricated own result',str(f))
  snap=O/(prefix.lower()+'-propagation-snapshots')/name;snap.mkdir(parents=True,exist_ok=True)
  for f in ['APPLICATION.json','intake.json','README.md']+(['INHERITANCE.json'] if GEO else ['APPLICATION.md','SOURCE-COPIES.json']):shutil.copy2(p/f,snap/f)
  result['packets'].append({'name':name,'predecessor':old,'source_count':len(sources),'changed_modules':changes,'unchanged_count':len(sources)-len(changes),'sources':sources,'predecessor_sources':before,'application_sha256':sha(p/'APPLICATION.json'),'intake_sha256':sha(p/'intake.json'),'readme_sha256':sha(p/'README.md'),'predecessor_intake_sha256':sha(q/'intake.json'),'predecessor_application_sha256':sha(q/'APPLICATION.json'),'obligations':a['obligations'],'bindings':a['bindings'],'schema_alias_negative_controls':negative,'own_result':own,'inserted_spaces':spaces if not GEO else None,'native_packet_check':'PASS','actual_predecessor_publication_still_required':not GEO})
  print('PASS',name,len(sources),'changed',len(changes),'controls',len(negative),flush=True)
(O/(prefix+'-PROPAGATION-CHECK.json')).write_text(json.dumps(result,indent=2)+'\n')
print('COMPLETE',prefix,flush=True)
