import sys,json,hashlib,subprocess,copy,tempfile,shutil,zipfile,re
from pathlib import Path
B=Path('/workspace/scratch/41c6d5925c0e'); R=B/'pel-followup43603177874/repo'; O=B/'review43603177874'; H='4c5562395a9891e0d79fa5808926ebf9b2781470';REL='quartics/quartic-318-326/proof/experiments';N='original-regular-coordinate-injectivity-r2';OLD='original-regular-coordinate-injectivity-r1';P=B/'picard-run43605497804/experiments'/N;RAW=B/'picard-run43605497804/raw/producer'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def gh(p):return subprocess.check_output(['git','show',H+':'+p],cwd=R)
def shab(b):return hashlib.sha256(b).hexdigest()
sys.dont_write_bytecode=True;sys.path.insert(0,str(R/'scripts'));import check_progress_experiment as ce
plan=ce.ci.derive_plan();a=json.loads((P/'APPLICATION.json').read_text());d=json.loads((P/'intake.json').read_text());pd=json.loads(gh(f'{REL}/{OLD}/intake.json'))
assert sha(P/'APPLICATION.json')=='c778fd56591ae0f1b8de59f2cf0f6849b7ce22fcf833668cb2c55bc01d51a260'
assert len(d['order'])==489 and d['order']==pd['order'];assert set(d['files'])==set(pd['files'])=={p.name for p in P.glob('*.lean')};assert d['revision_classification_schema']==1
expected={'FourRootCoordinateRingSigns318.lean':'5e2cb890b77513f26f374584b2773ca286494a90143bc36b60fff031139c0b91','PELPrimeLatticeResidues318.lean':'b0aa4b29255731863e72c8d4d665f7ebee3fb11a831fc2901cafe33c4436f4a3'}
changes={};hashes={};before={}
for fn,row in d['files'].items():
 bs=gh(f'{REL}/{OLD}/{fn}');before[fn]=shab(bs);hashes[fn]=sha(P/fn);assert before[fn]==pd['files'][fn]['sha256'];assert hashes[fn]==row['sha256']
 if bs!=(P/fn).read_bytes():
  assert fn in expected and hashes[fn]==expected[fn];changes[fn]={'before_sha256':before[fn],'after_sha256':hashes[fn]}
  assert re.findall(r'^\s*set_option.*$',bs.decode(),re.M)==re.findall(r'^\s*set_option.*$',(P/fn).read_text(),re.M)
assert changes==a['changed_sources'] and set(changes)==set(expected) and a['sources']==hashes and a['new_sources']=={}
assert len(a['original_five_sources_unchanged'])==5
for fn,h in a['original_five_sources_unchanged'].items():assert hashes[fn]==before[fn]==h
assert a['predecessor_application_sha256']==shab(gh(f'{REL}/{OLD}/APPLICATION.json'))
for flag in ['local_lean_run','kernel_verified','independent_acceptance','full_arithmetic_theorem_proved']:assert a[flag] is False
assert a['co_publication_with_canonical_pel_repairs_required'] is True
with tempfile.TemporaryDirectory(prefix='r2-review-',dir=O) as td:
 t=Path(td);(t/N).symlink_to(P,target_is_directory=True);prior=t/OLD;prior.mkdir();(prior/'intake.json').write_bytes(gh(f'{REL}/{OLD}/intake.json'))
 for fn in pd['files']:(prior/fn).write_bytes(gh(f'{REL}/{OLD}/{fn}'))
 _,_,direct,external=ce.packet(N,plan,t);baseline=ce.required_baseline(plan,direct);assert len(baseline)==73
 controls=[]
 for key in ['changed_modules','revised_modules','modified_predecessor_modules','reused_modules','unchanged_predecessor_modules','exact_predecessor_modules','unchanged_producer_modules','new_modules']:
  bad=copy.deepcopy(d)
  if key not in bad:bad[key]=['BogusIndependentControl318']
  elif isinstance(bad[key],list):bad[key].append('BogusIndependentControl318')
  else:bad[key]+=1
  try:ce.check_revision_classifications(t/N,bad,t)
  except ValueError:controls.append(key)
  else:raise AssertionError(('false classification accepted',key))
assert len(controls)==8
obs=a['obligations'];assert len(obs)==9 and {o['name'] for o in obs}=={'hypotheses','objects','coverage','transitions','identity','coefficients','local_conditions','exceptional_cases','downstream'}
for o in obs:
 for k in ['required_input','constructed_input','justification','source_references','evidence']:assert o[k]
 for k in ['source_references','evidence']:
  for ref in o[k]:assert (P/ref.split(':',1)[0]).is_file()
for fn,h in a['bindings'].items():assert sha(P/fn)==h,(fn,'binding')
for pre in ['PEL-SIGNS','PEL-RESIDUE']:
 m=O/(pre+'-SOURCE-BINDINGS.json');j=json.loads(m.read_text());needed={sha(m),sha(O/(pre+'-SOURCE-REVIEW.md'))}|set(j['source_bindings'].values())|set(j.get('reviewer_evidence',{}).values());assert needed<=set(a['bindings'].values()),(pre,'companions')
rawapp=json.loads((P/a['source_review']['raw_application_snapshot']).read_text())
# Only attached source-review metadata, plus the explicit honest unreached-wording correction.
if rawapp['obligations']!=obs:
 oldsentence='Further source algebraization research may depend only on the exact tested evaluator/injectivity endpoint.'
 newsentence='Further source algebraization research must retain the exact evaluator/injectivity endpoint; hosted verification is still required before treating it as accepted.'
 assert next(x for x in rawapp['obligations'] if x['name']=='downstream')['required_input']==oldsentence
 next(x for x in rawapp['obligations'] if x['name']=='downstream')['required_input']=newsentence
 assert rawapp['obligations']==obs
else:raise AssertionError('Requested misleading tested-endpoint wording not yet corrected')
assert all(rawapp[k]==a[k] for k in rawapp if k not in ['bindings','source_review','status'])
meta=json.loads((RAW/'ARTIFACT.json').read_text());assert meta['id']==14117648691 and meta['workflow_run']['id']==43605497804 and meta['workflow_run']['head_sha']==H;assert meta['digest']=='sha256:'+sha(RAW/'artifact.zip')
assert sha(P/'HOSTED-43605497804/ARTIFACT.json')==sha(RAW/'ARTIFACT.json')
with zipfile.ZipFile(RAW/'artifact.zip') as z:
 assert z.testzip() is None
 for fn in z.namelist():
  if not fn.endswith('/'):assert (RAW/fn).read_bytes()==z.read(fn),(fn,'extraction')
resultpath=RAW/'progress-experiments'/OLD/'RESULT.json';res=json.loads(resultpath.read_text());assert (P/'HOSTED-43605497804/RESULT.json').read_bytes()==resultpath.read_bytes();assert res['packet_sha256']==shab(gh(f'{REL}/{OLD}/intake.json'));assert res['verified_predecessors_reused']==73
assert len(res['commands'])==33 and [x['module'] for x in res['commands']]==pd['order'][:33] and all(x['exit_code']==0 for x in res['commands'][:-1]);assert res['commands'][-1]=={'exit_code':1,'module':'FourRootCoordinateRingSigns318','seconds':2.52};assert res['new_source_acceptance'] is False
assert not ({x['module']+'.lean' for x in res['commands']}&set(a['original_five_sources_unchanged']))
log=RAW/'progress-experiments'/OLD/'logs/FourRootCoordinateRingSigns318.log';assert log.read_bytes()==(P/'HOSTED-43605497804/FAILURE.log').read_bytes()
prov=json.loads((P/'HOSTED-43605497804/PROVENANCE.json').read_text());assert prov['new_five_sources_reached'] is False and prov['classification']['PELPrimeLatticeResidues318'].startswith('PREVENTIVE_UNREACHED_IN_OWN_PACKET')
snap=O/'producer-r2-propagation-snapshots';snap.mkdir(exist_ok=True)
for fn in ['APPLICATION.json','intake.json','README.md']:
 shutil.copy2(P/fn,snap/fn)
for p in (P/'HOSTED-43605497804').glob('*.json'):shutil.copy2(p,snap/p.name)
shutil.copy2(log,snap/'FAILURE.log');shutil.copy2(RAW/'artifact.zip',snap/'artifact.zip')
record={'status':'PASS_SOURCE_CONTRACT_PROPAGATION_ONLY','packet':N,'head':H,'run':43605497804,'source_count':489,'changed':changes,'unchanged_count':487,'source_hashes':hashes,'before_hashes':before,'original_five_unchanged':a['original_five_sources_unchanged'],'application_sha256':sha(P/'APPLICATION.json'),'intake_sha256':sha(P/'intake.json'),'readme_sha256':sha(P/'README.md'),'bindings':a['bindings'],'obligations':obs,'baseline_modules':baseline,'baseline_total':len(plan['module_order']),'false_alias_controls':controls,'artifact':meta,'own_result':res,'co_publication_gate_required':True,'local_lean_run':False,'candidate_kernel_acceptance':False,'full_compiled_axiom_audit':False}
(O/'PRODUCER-R2-PROPAGATION-CHECK.json').write_text(json.dumps(record,indent=2)+'\n');print('PASS: 489 roots, 2 exact inherited changes, 487 unchanged, all five foundational sources unchanged; 73 required baseline; 8 false aliases rejected; 9 obligations, all bindings exact. Own 32 passes then Signs failure; foundational sources unreached. Co-publication gate remains.')
