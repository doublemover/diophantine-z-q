import sys, json, hashlib, subprocess, re, copy, tempfile, shutil
from pathlib import Path
BASE=Path('/workspace/scratch/41c6d5925c0e')
REPO=BASE/'pel-integration43582938856/repo'
OUT=BASE/'review43586414080'
REL='quartics/quartic-318-326/proof/experiments'
HEAD='f89bd0a3cb8a788d6c7f2f494a21d7d103a893cb'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def blob(rel): return subprocess.check_output(['git','show',f'{HEAD}:{rel}'],cwd=REPO)
sys.path.insert(0,str(REPO/'scripts'))
import check_progress_experiment as ce
plan=ce.ci.derive_plan()
lane=sys.argv[1]; root=BASE/sys.argv[2]; names=sys.argv[3:]
assert names, 'No packet names supplied; refusing empty review'
expected_apps={'contact-original-positive-generators-r75':'e17b2bff79ef3af124ad76e5b39c81275bfb1b07182b22d4db077c4916ad96fa','forward-actual-two-descent-root-divisor-orders-r14':'f6ebbda2a1aad630ddbefb4eb747b6a0713ca63cba76ee25dfb0fbe788e54a9c','forward-original-weighted-weyl-r22-replay-r14':'88a521fc4f063400cb04d8ae18aae2e8a8e43ae42dcf06ed4b74c4ffdc94db22','original-finite-quotient-reconstruction-r70':'57c99d35de143718bf1020322c27cc706ff671af0c1488b280a7e280b42ed5db','relative-original-normalized-kernel-gluing-r14':'413a95dc26f3cf64bf61a7888a939bdbcfeff988dff21ead9475d2b29ec4b3e9','original-five-kernel-norm-equivalence-r18':'6083e3ce39ed28dbf8a20bf4a1374b9f49fac5995e89c812a3485d535311b503'}
reviewed={}
for path in ['FIRST-SOURCE-CHECK.json','NEXT-SOURCE-CHECK.json']:
 for v in json.loads((OUT/path).read_text()).values():reviewed[v['module']]=v['after_sha256']
result={'lane':lane,'review_kind':'SOURCE_AND_PROVENANCE_ONLY','head':HEAD,'run':43586414080,'local_lean_run':False,'kernel_acceptance':False,'packets':[],'baseline_modules':len(plan['module_order'])}
with tempfile.TemporaryDirectory(prefix='propagation-',dir=OUT) as t:
 vr=Path(t)
 for name in names:
  folder=root/name; a=json.loads((folder/'APPLICATION.json').read_text()); d=json.loads((folder/'intake.json').read_text()); old=a.get('predecessor',a.get('revision_source',d.get('revision_of',d.get('revision_source'))))
  assert sha(folder/'APPLICATION.json')==expected_apps[name],(name,'frozen APP changed')
  prior=REPO/REL/old
  pb=blob(f'{REL}/{old}/intake.json'); pd=json.loads(pb)
  assert (prior/'intake.json').read_bytes()==pb
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
  assert len(changed)==1 and sourcehash[changed[0]+'.lean']==reviewed[changed[0]],(name,'reviewed exact delta')
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
  assert all(all(o.get(k) for k in ['required_input','constructed_input','justification','source_references','evidence']) for o in obs)
  for o in obs:
   for k in ['source_references','evidence']:
    for ref in o[k]:
     assert isinstance(ref,str) and (folder/ref.split(':',1)[0]).is_file(),(name,k,ref)
  bindings=a.get('bindings',{})
  snap=OUT/'propagation-snapshots'/name
  snap.mkdir(parents=True,exist_ok=True)
  for fn in ['APPLICATION.json','intake.json','README.md']: shutil.copy2(folder/fn,snap/fn)
  if isinstance(a.get('source_review'),dict):
   sr=a['source_review']
   if sr.get('application_before_binding'):
    assert sha(folder/sr['application_before_binding'])==sr['application_before_binding_sha256']

  # Every native declared evidence byte is checked by packet(). Record full bindings.
  current_results={}
  for p in (folder/'HOSTED-43586414080').rglob('*RESULT*.json'):
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
(OUT/f'{lane}-PROPAGATION-BINDINGS.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS',lane,'baseline',len(plan['module_order']),'source count',sum(x['source_count'] for x in result['packets']))
