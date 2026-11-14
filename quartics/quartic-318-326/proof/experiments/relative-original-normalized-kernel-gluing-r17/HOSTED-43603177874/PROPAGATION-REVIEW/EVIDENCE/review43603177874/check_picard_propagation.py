import sys, json, hashlib, subprocess, re, copy, tempfile, shutil
from pathlib import Path
BASE=Path('/workspace/scratch/41c6d5925c0e')
REPO=BASE/'pel-integration43597228569/repo'
OUT=BASE/'review43603177874'
REL='quartics/quartic-318-326/proof/experiments'
HEAD='57227e167abe49436d651b932ff75d5bdf9b5898'
CURRENT=HEAD
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def blob(rel): return subprocess.check_output(['git','show',f'{HEAD}:{rel}'],cwd=REPO)
sys.dont_write_bytecode=True
sys.path.insert(0,str(REPO/'scripts'))
import check_progress_experiment as ce
plan=ce.ci.derive_plan()
lane=sys.argv[1]; root=BASE/sys.argv[2]; names=sys.argv[3:]
assert names, 'No packet names supplied; refusing empty review'
frozen=json.loads((OUT/'PICARD-PROPAGATION-TARGETS.json').read_text())[lane]
expected_apps={x['name']:x['application_sha256'] for x in frozen}
expected_changes={x['name']:x['changed'] for x in frozen}
reviewed={'ContactCoefficientRestrictionSquares318':'3d46e39faea16541608a7bc9d9480722f0c8dd47c2f9a1382bdda0aee1aa4e84','DualUnitFactorization318':'6199358cd87d2a4947db1175a8c39548117f85f955b16b445a8bcd15176a2373'}
result={'lane':lane,'review_kind':'SOURCE_AND_PROVENANCE_ONLY','head':HEAD,'run':43603177874,'integration_base':CURRENT,'local_lean_run':False,'kernel_acceptance':False,'packets':[],'baseline_modules':len(plan['module_order'])}
with tempfile.TemporaryDirectory(prefix='propagation-',dir=OUT) as t:
 vr=Path(t)
 for name in names:
  folder=root/name; a=json.loads((folder/'APPLICATION.json').read_text()); d=json.loads((folder/'intake.json').read_text()); old=a.get('predecessor',a.get('revision_source',d.get('revision_of',d.get('revision_source'))))
  assert sha(folder/'APPLICATION.json')==expected_apps[name],(name,'frozen APP changed')
  prior=REPO/REL/old
  pb=blob(f'{REL}/{old}/intake.json'); pd=json.loads(pb)
  assert (prior/'intake.json').read_bytes()==pb
  assert subprocess.check_output(['git','rev-parse',HEAD+':'+REL+'/'+old],cwd=REPO)==subprocess.check_output(['git','rev-parse',CURRENT+':'+REL+'/'+old],cwd=REPO),(name,'whole predecessor tree differs')
  assert d['order']==pd['order'],(name,'order')
  assert {p.name for p in folder.glob('*.lean')}==set(d['files'])==set(pd['files'])
  assert d['revision_classification_schema']==1
  changed=[]; sourcehash={}; oldhash={}
  for n in d['order']:
   fn=n+'.lean'; before=prior/fn; after=folder/fn
   assert sha(before)==pd['files'][fn]['sha256'],(name,fn,'prior byte mismatch')
   assert sha(after)==d['files'][fn]['sha256']
   oldhash[fn]=sha(before); sourcehash[fn]=sha(after)
   if before.read_bytes()!=after.read_bytes():
    changed.append(n)
    pat=r'^\s*set_option\s+.*$'
    old_options=re.findall(pat,before.read_text(),re.M); new_options=re.findall(pat,after.read_text(),re.M)
    if False:
     assert [x for x in new_options if x.strip() not in ['set_option profiler true in','set_option profiler.threshold 1 in']]==old_options,(name,fn,'unexpected diagnostic options')
    else:
     assert old_options==new_options,(name,fn,'options')
  assert set(changed)==set(expected_changes[name]) and all(sourcehash[n+'.lean']==reviewed[n] for n in changed),(name,'reviewed exact delta')
  if not (vr/name).exists(): (vr/name).symlink_to(folder,target_is_directory=True)
  if not (vr/old).exists():
   (vr/old).mkdir()
   for fn in ['intake.json']+list(pd['files']): shutil.copy2(prior/fn,vr/old/fn)
  ce.packet(name,plan,vr)
  rejected=[]
  for key in ['changed_modules','revised_modules','modified_predecessor_modules','reused_modules','unchanged_predecessor_modules','exact_predecessor_modules','unchanged_producer_modules','new_modules']:
   bad=copy.deepcopy(d)
   if key not in bad:bad[key]=['BogusIndependentControl318']
   elif isinstance(bad[key],list):bad[key]=bad[key]+['BogusIndependentControl318']
   else:bad[key]+=1
   try:ce.check_revision_classifications(vr/name,bad,vr)
   except ValueError:rejected.append(key)
   else:raise AssertionError((name,key,'accepted false classification'))
  assert a.get('sources',sourcehash)==sourcehash,(name,'APP sources')
  obs=a['obligations']
  if isinstance(obs,dict): obs=list(obs.values())
  assert len(obs)==9 and {o['name'] for o in obs}=={'hypotheses','objects','coverage','transitions','identity','coefficients','local_conditions','exceptional_cases','downstream'},(name,'nine obligations')
  refkey='source_refs' if lane=='GEOMETRY' else 'source_references'
  assert all(all(o.get(k) for k in ['required_input','constructed_input','justification',refkey,'evidence']) for o in obs)
  for o in obs:
   for k in [refkey,'evidence']:
    for ref in o[k]:
     assert isinstance(ref,str) and (folder/ref.split(':',1)[0]).is_file(),(name,k,ref)
  bindings=a.get('bindings',{})
  applicable=['PEL-FIRST-TWO','PEL-RESIDUE'] if lane=='PEL' else ['BICANONICAL'] if lane=='GEOMETRY' else ['PICARD-GLUING' if 'gluing' in name else 'PICARD-FIVE']
  for pre in applicable:
   bm=OUT/(pre+'-SOURCE-BINDINGS.json');sm=json.loads(bm.read_text())
   needed=set(sm['source_bindings'].values())|set(sm.get('reviewer_evidence',{}).values())|{sha(bm),sha(OUT/(pre+'-SOURCE-REVIEW.md'))}
   assert needed<=set(bindings.values()),(name,pre,'missing exact source-review companion',needed-set(bindings.values()))
  for fn,h in bindings.items():assert sha(folder/fn)==h,(name,fn,'binding')

  if lane=='PEL':
   assert a['public_telescopes_changed'] is False
   for o in obs: assert set(o['scope_modules'])==set(changed)
   if name.startswith('height-'): assert a['geometry_sources_changed'] is False and a['trace_dependency_caveat']
  snap=OUT/'propagation-snapshots'/name
  snap.mkdir(parents=True,exist_ok=True)
  for fn in ['APPLICATION.json','intake.json','README.md']: shutil.copy2(folder/fn,snap/fn)
  if isinstance(a.get('source_review'),dict):
   sr=a['source_review']
   if sr.get('application_before_binding'):
    assert sha(folder/sr['application_before_binding'])==sr['application_before_binding_sha256']

  sr=a['source_review']; raw=json.loads((folder/sr['reviewed_application_snapshot']).read_text())
  if 'five' in name:
   correction=json.loads((folder/'HOSTED-43603177874/PRE-CONTRACT-LOCATOR-CORRECTION-APPLICATION.json').read_text())
   assert correction['obligations']==raw['obligations']
   for o in raw['obligations']:
    o['source_references']=[{'FifthDualUnitNorm318.lean':'DualUnitNormConstruction318.lean','CharacterDualUnitNorm318.lean':'OriginalOpenDualCoordinates318.lean'}.get(v,v) for v in o['source_references']]
    if o['name']=='downstream':
     assert o['required_input']=='FifthDualUnitNorm and CharacterDualUnitNorm consume the same actual log/factorization.'
     assert o['constructed_input']=='Their qualified use of existing DualUnitFactorization declarations is unchanged.'
     assert o['justification']=='Source identity is checked, not a claim these later modules or the whole packet have passed.'
     o['required_input']='DualUnitNormConstruction and OriginalOpenDualCoordinates consume the same actual logarithm/factorization.'
     o['constructed_input']='Their qualified or opened-namespace use of existing coefficient_unit, log_mul, factorization and lift_natural is unchanged.'
     o['justification']='Source consumer identity is checked, not a claim these later modules or the whole packet have passed.'
   assert all(correction[k]==a[k] for k in correction if k not in ['obligations','bindings'])
  assert all(raw[k]==a[k] for k in raw if k not in ['bindings','source_review','status']), (name,'unexpected source-bind/corrected-reference delta')
  # Every native declared evidence byte is checked by packet(). Record full bindings.
  current_results={}
  for p in (folder/'HOSTED-43603177874').rglob('*RESULT*.json'):
   j=json.loads(p.read_text())
   if j.get('packet')==old:
    assert j['packet_sha256']==hashlib.sha256(pb).hexdigest(),(name,'own result intake')
    assert j['status']=='FAILED'
    current_results[str(p.relative_to(folder))]={'sha256':sha(p),'packet_sha256':j['packet_sha256'],'last_command':j['commands'][-1]}
  assert current_results,(name,'missing own result')
  for key in ['local_lean_run','full_arithmetic_theorem_proved','independent_acceptance','independent_mathematical_acceptance','kernel_verified','independently_accepted','new_source_acceptance','resources_changed']:
   if key in a:assert a[key] is False,(name,key)
  result['packets'].append({'name':name,'predecessor':old,'source_count':len(sourcehash),'changed_modules':changed,'unchanged_count':len(sourcehash)-len(changed),'intake_sha256':sha(folder/'intake.json'),'readme_sha256':sha(folder/'README.md'),'application_sha256':sha(folder/'APPLICATION.json'),'predecessor_intake_sha256':hashlib.sha256(pb).hexdigest(),'source_sha256':sourcehash,'predecessor_source_sha256':oldhash,'application_bindings':bindings,'own_results':current_results,'native_packet_check':'PASS','schema_alias_negative_controls':rejected,'obligations':a['obligations'],'options_unchanged':True,'diagnostic_profiler_options_added':False})
  print(name,len(sourcehash),'changed',changed,'controls',len(rejected),'APP',sha(folder/'APPLICATION.json'),flush=True)
(OUT/f'{lane}-PROPAGATION-CHECK.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS',lane,'baseline',len(plan['module_order']),'source count',sum(x['source_count'] for x in result['packets']))
