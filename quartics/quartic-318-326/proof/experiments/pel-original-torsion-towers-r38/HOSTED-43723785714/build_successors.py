from pathlib import Path
import json,hashlib,shutil,re,sys,subprocess
W=Path('/workspace/scratch/41c6d5925c0e');R=W/'pel-43723785714';REPO=W/'resume-20261115-repo';EX=REPO/'quartics/quartic-318-326/proof/experiments';OUT=R/'successors';C=R/'canonical-current';HEAD='964435f03d8c11dbb6b52b8453fa0c4140a445d9';RUN=43723785714;EV='HOSTED-'+str(RUN)
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,d):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2)+'\n')
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip()==HEAD
sys.path.insert(0,str(REPO/'scripts'));import check_progress_lean as ci,check_progress_experiment as pe
M={'pel-original-character-ordered-biholomorph-r29':'pel-original-character-ordered-biholomorph-r30','pel-original-zero-local-length-r56':'pel-original-zero-local-length-r57','pel-original-cotangent-hzero-forty-r62':'pel-original-cotangent-hzero-forty-r63','pel-original-torsion-towers-r36':'pel-original-torsion-towers-r37','height-original-normal-infinity-trace-r29':'height-original-normal-infinity-trace-r30','original-infinity-range-extension-r11':'original-infinity-range-extension-r12'}
ENVS={tag:(R/tag,'sources','SOURCE-APPLICATION.json') for tag in ['projection','branch','representatives','conjugation','unitlifts']}
ENVS.update({'infinity-connected':(W/'pel-resume-436801/infinity-connected-preventive','after','APPLICATION.json'),'generic-point':(W/'resume-geometry/generic-point-43723785714','sources','SOURCE-APPLICATION.json'),'evaluated-chart':(W/'resume-geometry/evaluated-chart-43723785714','sources','SOURCE-APPLICATION.json')})
REVIEWS=[W/'picard-peer-reviews-437237/PEL-FOUR-CANONICAL-SOURCE-REVIEW.json',W/'resume-independent-review/BRANCH-SCALAR-ACTIONS-43723785714-REVIEW.md',W/'picard-resume-436801/INFINITY-CONNECTED-PREVENTIVE-REVIEW.json',W/'resume-independent-review/GENERIC-POINT-THREE-SOURCE-43723785714-REVIEW.md',W/'resume-independent-review/TRACE-EVALUATED-CHART-43723785714-REVIEW.md']
assert not C.exists();records={};cl={}
for tag,(env,folder,contract) in ENVS.items():
 shutil.copytree(env,C/'envelopes'/tag)
 app=json.loads((env/contract).read_text());assert len(app['obligations'])==9
 for p in (env/folder).glob('*.lean'):
  b=env/'before'/p.name;assert b.exists();n=p.stem
  records[n]={'before_sha256':h(b),'after_sha256':h(p),'contract':f'envelopes/{tag}/{contract}','envelope':tag,'public_type_scope_changed':tag in ['infinity-connected','generic-point','evaluated-chart']}
  cl[n]=['; '.join(str(x.get(k,'')) for k in ['required_input','constructed_input','justification']) for x in app['obligations']]
  for sub,f in [('before',b),('after',p)]:
   (C/sub).mkdir(exist_ok=True);shutil.copyfile(f,C/sub/p.name)
for p in REVIEWS:
 (C/'reviews').mkdir(exist_ok=True);shutil.copyfile(p,C/'reviews'/p.name)
dump(C/'SOURCE-HASHES.json',records);assert len(records)==13
ids=['required_inputs','constructed_objects','index_and_domain_coverage','transition_maps','coefficient_and_scalar_factors','local_and_exceptional_cases','identity_with_consumed_object','downstream_dependency_effects','honesty_boundary']
disclosure='Actual-frontier fixes retain original maps/coefficient data: categorical AlgHom overlap identity, explicit existing A/P/C scalar actions with independent R actions, qualified lattice action, native inverse-unit/norm APIs, unchanged81 finite mod3 branches with ordinary decide tails and native unit-power coercion. Preventive infinity4 explicitly retains17 original hb binders and derived-prime result type; this changes public telescope presentation, not original mathematical distinctness. Geometry4 shares the actual single Scheme universe only in geometric producer/consumer sections; ring APIs retain independent universes, original evaluation algebra is explicitly installed, and eval_C uses expected-type simp. These public universe/telescope adjustments are disclosed, not blanket unchanged signatures. No new external mathematical premise, research root, scalar substitution, resource/trust increase, or local Lean.'
rows=[];checks=[]
for old,new in M.items():
 src=EX/old;dst=OUT/new;own=W/'resume-20261115-integration'/('hosted-'+str(RUN))/('experiment-'+old)/'progress-experiments'/old
 assert not dst.exists();d=json.loads((src/'intake.json').read_text());res=json.loads((own/'RESULT.json').read_text());assert res['packet_sha256']==h(src/'intake.json');assert [x['module'] for x in res['commands']]==d['order'][:len(res['commands'])];fail=res['commands'][-1];assert fail['exit_code']!=0
 shutil.copytree(src,dst);ev=dst/EV;ev.mkdir()
 for p in src.iterdir():
  if p.is_file() and p.suffix!='.lean':
   q=ev/'PREDECESSOR-METADATA'/p.name;q.parent.mkdir(exist_ok=True);shutil.copyfile(p,q)
 shutil.copytree(own,ev/'own-hosted');shutil.copytree(C,ev/'canonical');shutil.copyfile(Path(__file__),ev/'build_successors.py')
 actual=[];copies={}
 for n in d['order']:
  p=src/(n+'.lean');assert h(p)==d['files'][p.name]['sha256']
  if n in records:
   assert h(p)==records[n]['before_sha256'],(old,n,h(p),records[n]['before_sha256'])
   shutil.copyfile(C/'after'/p.name,dst/p.name);actual.append(n);copies[n]=records[n]
   assert re.findall(r'^.*set_option.*$',p.read_text(),re.M)==re.findall(r'^.*set_option.*$',(dst/p.name).read_text(),re.M)
 unchanged=[n for n in d['order'] if n not in actual];observed=[n for n in actual if n==fail['module']];preventive=[n for n in actual if n not in observed];assert observed
 passed={x['module'] for x in res['commands'] if x['exit_code']==0};assert not passed.intersection(preventive),(old,passed.intersection(preventive))
 types=[n for n in actual if records[n]['public_type_scope_changed']]
 d.update(packet=new,status='UNACCEPTED_SOURCE_REPAIRS_HOSTED_PENDING',revision_classification_schema=1,new_modules=[],observed_failure_modules=observed,preventive_unobserved_modules=preventive)
 for key in ['revision_of','revision_source']:
  if key in d:d[key]=old
 if not any(k in d for k in ['revision_of','revision_source']):d['revision_of']=old
 for key in ['changed_modules','revised_modules','modified_predecessor_modules','changed_producer_modules']:d[key]=actual
 for key in ['exact_predecessor_modules','unchanged_predecessor_modules','reused_modules','unchanged_upstream_modules','unchanged_producer_modules']:
  if key in d:d[key]=unchanged if isinstance(d[key],list) else len(unchanged)
 for name,row in d['files'].items():
  row['sha256']=h(dst/name)
  if Path(name).stem in actual:row['imports']=sorted(ci.import_names((dst/name).read_text()))
 dump(dst/'intake.json',d)
 binding={'predecessor':old,'successor':new,'copies':copies,'full_order_count':len(d['order']),'unchanged_count':len(unchanged),'own_result_sha256':h(own/'RESULT.json'),'own_predecessor_intake_sha256':h(src/'intake.json'),'own_successful_drafts':len(res['commands'])-1,'own_failed_module':fail['module'],'observed_failure_repair_modules':observed,'preventive_unreached_modules':preventive,'public_type_scope_modules':types,'resources_changed':False}
 dump(dst/'COPY-BINDINGS.json',binding)
 row={'predecessor':old,'successor':new,'changed':actual,'order_count':len(d['order']),'intake_sha256':h(dst/'intake.json'),'own_failure':fail};dump(dst/'NEXT-ROW.json',row)
 (dst/'README.md').write_text(f'# {new}\n\nExact source-only successor to {old}, own run{RUN} at{HEAD}: {len(res["commands"])-1} full draft passes then {fail["module"]} fails{fail["seconds"]}s. {len(d["order"])} roots unchanged order; {len(actual)} changed copies/{len(unchanged)} unchanged.\n\nObserved own failure repair: '+', '.join(observed)+'. Preventive/unreached matching copies: '+', '.join(preventive)+'. All matching13 canonical roots in these six packets are propagated exactly. Own receipt, predecessor metadata and historical source maps preserved; older SOURCE-MAP classifications are historical, current COPY-BINDINGS/intake govern this revision.\n\n'+disclosure+'\n\nNo repaired module is claimed to pass. Complete packet/declaration audit requires hosted replay. Omitted finite-flat and inactive Picard/obstruction research remain outside this unchanged root scope. No root/import/accepted baseline/toolchain/budget change.\n')
 refs=[n+'.lean' for n in actual]+[EV+'/canonical/before/'+n+'.lean' for n in actual];contracts={n:EV+'/canonical/'+records[n]['contract'] for n in actual};evidence=['README.md','COPY-BINDINGS.json',EV+'/own-hosted/RESULT.json',EV+'/canonical/SOURCE-HASHES.json']+list(dict.fromkeys(contracts.values()))
 obligations=[{'id':id,'required_input':'Exact original objects/domains/maps/scalars and native interfaces specified separately in each canonical clause.','constructed_input':'\n\n'.join(n+': '+cl[n][j] for n in actual),'justification':'Exact reviewed before/after matched to this own source copy. Observed failure versus preventive/unreached status comes from own packet receipt; no sibling success substitutes. Public retained-binder/universe changes disclosed.','scope_modules':actual,'source_references':refs,'evidence':evidence,'canonical_clauses':{n:{'contract':contracts[n],'clause_number':j+1} for n in actual}} for j,id in enumerate(ids)]
 app={'packet':new,'predecessor':old,'status':'CURRENT_PROPAGATION_REVIEW_PENDING','source_commit':HEAD,'run_id':RUN,'local_lean_run':False,'kernel_verified':False,'resources_changed':False,'full_arithmetic_theorem_proved':False,'public_type_scope_modules':types,'public_type_scope_disclosure':disclosure,'modified_predecessor_modules':actual,'observed_failure_repair_modules':observed,'preventive_unreached_modules':preventive,'new_modules':[],'obligations':obligations,'canonical_source_contracts':contracts,'intake_sha256':h(dst/'intake.json'),'sources':{n:h(dst/n) for n in d['files']}}
 app['bindings']={str(p.relative_to(dst)):h(p) for p in sorted(dst.rglob('*')) if p.is_file() and p!=dst/'APPLICATION.json'};dump(dst/'APPLICATION.json',app)
 prior=OUT/old;prior.mkdir(exist_ok=True);shutil.copyfile(src/'intake.json',prior/'intake.json')
 for n in d['order']:shutil.copyfile(src/(n+'.lean'),prior/(n+'.lean'))
 pe.packet(new,ci.derive_plan(),OUT);row['application_sha256']=h(dst/'APPLICATION.json');rows.append(row);checks.append({'packet':new,'source_structure':'PASS','bindings':len(app['bindings']),'changed':len(actual)});print('PASS',new,len(actual),flush=True)
dump(R/'NEXT-SUCCESSOR-MAP.json',{'base':HEAD,'run':RUN,'packets':rows,'local_lean_run':False});dump(R/'STRUCTURAL-CHECK.json',{'checks':checks,'kernel_verified':False,'local_lean_run':False})
