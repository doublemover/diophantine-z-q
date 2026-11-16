import sys, json, hashlib, subprocess, re, copy, tempfile, shutil
from pathlib import Path
BASE=Path('/workspace/scratch/41c6d5925c0e')
REPO=BASE/'pel-integration43592150561/repo'
OUT=BASE/'review43597228569'
REL='quartics/quartic-318-326/proof/experiments'
HEAD='2af419e128047c483b3cdc0ba5e4d65c09d7c4ce'
CURRENT=HEAD
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def blob(rel): return subprocess.check_output(['git','show',f'{HEAD}:{rel}'],cwd=REPO)
sys.dont_write_bytecode=True
sys.path.insert(0,str(REPO/'scripts'))
import check_progress_experiment as ce
plan=ce.ci.derive_plan()
lane=sys.argv[1]; root=BASE/sys.argv[2]; names=sys.argv[3:]
assert names, 'No packet names supplied; refusing empty review'
frozen=json.loads((OUT/'PROPAGATION-TARGETS.json').read_text())[lane]
expected_apps={x['name']:x['application_sha256'] for x in frozen}
expected_changes={x['name']:x['changed'] for x in frozen}
reviewed={'IntegralRationalFiveChartGeometry318': '0afdb6deba6dabce71d1f58e4eb441fa86347ca69148269f2e96ee96c271497b', 'FourRootNormalizedSignAction318': 'dbe546f1c943efbaa446ad7bbc596f53e00b8050989f35f8a97535170e7050d7', 'PELOriginalSiegelCoercivity318': '76735d65ed572489d6299a4d25395e267c64521ac953c0e388998d65d2388948', 'PELPrimeLatticeResidues318': 'cac16b1f9eb8d07b11cfb945281dfd341d52e571d1f25bacf68772770b6d6ffe', 'ContactCoefficientRestrictionSquares318': 'd4f90fcaf38ccf0becb7915e5bc8728eed6562f5f968e609be85251a76599ee8', 'OriginalDualAlgebraNormTrace318': '8b19a47a053a220969f9903878c985a04c15178523eeae48e21488d4de365882'}
result={'lane':lane,'review_kind':'SOURCE_AND_PROVENANCE_ONLY','head':HEAD,'run':43597228569,'integration_base':CURRENT,'local_lean_run':False,'kernel_acceptance':False,'packets':[],'baseline_modules':len(plan['module_order'])}
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
   if key not in d:continue
   bad=copy.deepcopy(d)
   if isinstance(bad[key],list):bad[key]=bad[key]+['BogusIndependentControl318']
   else:bad[key]+=1
   try:ce.check_revision_classifications(vr/name,bad,vr)
   except ValueError:rejected.append(key)
   else:raise AssertionError((name,key,'accepted false classification'))
  assert a.get('sources',sourcehash)==sourcehash,(name,'APP sources')
  obs=a['obligations']
  if isinstance(obs,dict): obs=list(obs.values())
  assert len(obs)==9,(name,'nine obligations')
  refkey='source_refs' if lane=='GEOMETRY' else 'source_references'
  assert all(all(o.get(k) for k in ['required_input','constructed_input','justification',refkey,'evidence']) for o in obs)
  for o in obs:
   for k in [refkey,'evidence']:
    for ref in o[k]:
     assert isinstance(ref,str) and (folder/ref.split(':',1)[0]).is_file(),(name,k,ref)
  bindings=a.get('bindings',{})
  applicable=['PEL-FIRST-TWO','PEL-RESIDUE'] if lane=='PEL' else ['GEOMETRY-FIVECHART'] if lane=='GEOMETRY' else ['PICARD-GLUING' if 'gluing' in name else 'PICARD-FIVE']
  for pre in applicable:
   bm=OUT/(pre+'-SOURCE-BINDINGS.json');sm=json.loads(bm.read_text())
   needed=set(sm['source_bindings'].values())|{sha(bm),sha(OUT/(pre+'-SOURCE-REVIEW.md'))}
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

  # Every native declared evidence byte is checked by packet(). Record full bindings.
  current_results={}
  for p in (folder/'HOSTED-43597228569').rglob('*RESULT*.json'):
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
