from pathlib import Path
import json,hashlib,shutil,re,sys,subprocess
W=Path('/workspace/scratch/41c6d5925c0e');R=W/'pel-resume-436801';REPO=W/'resume-20261115-repo';EX=REPO/'quartics/quartic-318-326/proof/experiments';OUT=R/'successors';HOST=W/'resume-20261115-integration/hosted-43680185849';C=R/'canonical';HEAD='4ce7eda322f507e43be0c9be1be2e97449e82189';RUN=43680185849;EV='HOSTED-'+str(RUN)
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,d):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2)+'\n')
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip()==HEAD
sys.path.insert(0,str(REPO/'scripts'));import check_progress_lean as ci,check_progress_experiment as pe
M={'pel-original-character-ordered-biholomorph-r28':'pel-original-character-ordered-biholomorph-r29','pel-original-zero-local-length-r55':'pel-original-zero-local-length-r56','pel-original-cotangent-hzero-forty-r61':'pel-original-cotangent-hzero-forty-r62','pel-original-torsion-towers-r35':'pel-original-torsion-towers-r36','height-original-normal-infinity-trace-r28':'height-original-normal-infinity-trace-r29','original-infinity-range-extension-r10':'original-infinity-range-extension-r11'}
ENVS={'projective-level':R/'PROJECTIVE-LEVEL-43680185849-SOURCE-REVIEWED','branch-localization':R/'BRANCH-LOCALIZATION-43680185849-SOURCE-REVIEWED','finite-ramification':R/'PICARD-FINITE-RAMIFICATION-PAIR-436801-SOURCE-REVIEWED/picard-finite-ramification-43680185849','automorphy-representatives':W/'resume-20261115-restored/diophantine-automorphy-representatives-reviewed-43680185849','automorphy-preventive':W/'resume-20261115-restored/diophantine-automorphy-adjacent-preventive-reviewed-43680185849'}
C.mkdir(exist_ok=True);records={}
for k,env in ENVS.items():
 target=C/'sources'/k
 shutil.copytree(env,target,dirs_exist_ok=True)
 contract=next(p for p in [env/'APPLICATION.json',env/'APPLICATION.md'] if p.exists())
 for source in sorted((env/'after').glob('*.lean')):
  name=source.stem;before=env/'before'/source.name
  row={'before_sha256':h(before),'after_sha256':h(source),'contract':f'sources/{k}/{contract.name}','source_envelope':k,'existing_public_telescopes_changed':k=='finite-ramification'}
  if k=='branch-localization':row['alternate_before_sha256']=[h(env/'baseline'/source.name)]
  records[name]=row
  for sub,p in [('before',before),('after',source)]:
   (C/sub).mkdir(exist_ok=True);shutil.copyfile(p,C/sub/source.name)
review=W/'resume-independent-review/AUTOMORPHY-FIVE-CANONICAL-REVIEW.md';(C/'reviews').mkdir(exist_ok=True);shutil.copyfile(review,C/'reviews'/review.name)
dump(C/'SOURCE-HASHES.json',records);assert len(records)==9
ids=['required_inputs','constructed_objects','index_and_domain_coverage','transition_maps','coefficient_and_scalar_factors','local_and_exceptional_cases','identity_with_consumed_object','downstream_dependency_effects','honesty_boundary']
def clauses(rel):
 p=C/rel
 if p.suffix=='.json':
  d=json.loads(p.read_text());return ['; '.join(str(x.get(k,'')) for k in ['required_input','constructed_input','justification']) for x in d['obligations']]
 parts=re.findall(r'^([1-9])\. (.*?)(?=\n[1-9]\. |\Z)',p.read_text(),re.M|re.S);assert len(parts)==9,(p,len(parts));return [s.strip() for _,s in parts]
cl={n:clauses(r['contract']) for n,r in records.items()};assert all(len(v)==9 for v in cl.values())
OUT.mkdir(exist_ok=True);rows=[];checks=[]
for old,new in M.items():
 own=HOST/('experiment-'+old)/'progress-experiments'/old;src=EX/old;dst=OUT/new
 assert not dst.exists(),dst
 d=json.loads((src/'intake.json').read_text());result=json.loads((own/'RESULT.json').read_text());assert result['packet_sha256']==h(src/'intake.json'),old
 shutil.copytree(src,dst);ev=dst/EV;ev.mkdir()
 for p in src.iterdir():
  if p.is_file() and p.suffix!='.lean':
   q=ev/'PREDECESSOR-METADATA'/p.name;q.parent.mkdir(exist_ok=True);shutil.copyfile(p,q)
 shutil.copytree(own,ev/'own-hosted');shutil.copytree(C,ev/'canonical');shutil.copyfile(Path(__file__),ev/'build_packets.py')
 actual=[];percopy={}
 for n in d['order']:
  p=src/(n+'.lean');assert h(p)==d['files'][p.name]['sha256']
  if n in records:
   allowed=[records[n]['before_sha256']]+records[n].get('alternate_before_sha256',[])
   assert h(p) in allowed,(old,n,h(p),allowed)
   shutil.copyfile(C/'after'/p.name,dst/p.name);actual.append(n);percopy[n]={**records[n],'actual_before_sha256':h(p)}
   assert re.findall(r'^.*set_option.*$',p.read_text(),re.M)==re.findall(r'^.*set_option.*$',(dst/p.name).read_text(),re.M),(old,n)
 assert actual;unchanged=[n for n in d['order'] if n not in actual]
 d.update(packet=new,status='DRAFT_SOURCE_REPAIR_HOSTED_PENDING',revision_classification_schema=1,new_modules=[])
 for key in ['revision_of','revision_source']:
  if key in d:d[key]=old
 if not any(k in d for k in ['revision_of','revision_source']):d['revision_of']=old
 for key in ['changed_modules','revised_modules','modified_predecessor_modules']:d[key]=actual
 for key in ['exact_predecessor_modules','unchanged_predecessor_modules','reused_modules','unchanged_upstream_modules','unchanged_producer_modules']:
  if key in d:d[key]=unchanged if isinstance(d[key],list) else len(unchanged)
 for n,row in d['files'].items():
  row['sha256']=h(dst/n)
  if Path(n).stem in actual:row['imports']=sorted(ci.import_names((dst/n).read_text()))
 dump(dst/'intake.json',d)
 failed=[x for x in result['commands'] if x['exit_code']];assert failed;ownfail=failed[0]
 observed=[n for n in actual if n==ownfail['module']];preventive=[n for n in actual if n not in observed];telescope=[n for n in actual if records[n]['existing_public_telescopes_changed']]
 assert observed,(old,ownfail)
 disclosure='FiniteRamification and OffBranchRamification retain original hb in five public theorem telescopes and explicitly let-bind existing prime witnesses in two separability result types. These are disclosed public type-scope changes, not blanket unchanged-signature edits. BranchLocalization adds an abstract opaque scalar-tower helper and derives its premise from the original sourceMap_on_polynomial without replacing existing scalar actions. Cotangent loses exactly19 #check observers; other copies use the separately bound observer-free predecessor. ProjectiveLevel exposes the same forgetful-map function application. Automorphy repairs retain the actual quotient, lattice, positive parameter, chart domains, factors and all branches; four adjacent consumers are preventive and unreached. No new public external premise, resource/trust change or research root.'
 bind={'predecessor':old,'successor':new,'copies':percopy,'unchanged_count':len(unchanged),'full_order_count':len(d['order']),'own_result_sha256':h(own/'RESULT.json'),'own_predecessor_intake_sha256':h(src/'intake.json'),'resources_changed':False,'public_telescopes_changed':bool(telescope),'explicit_type_or_retained_binder_modules':telescope,'observed_failure_repair_modules':observed,'preventive_unreached_modules':preventive,'diagnostic_only_modules':[],'candidate_repair_modules':actual,'diagnostic_observers_removed':19 if old=='pel-original-cotangent-hzero-forty-r61' else 0}
 dump(dst/'COPY-BINDINGS.json',bind)
 (dst/'README.md').write_text(f'''# {new}\n\nSource-only successor to {old}, exact own hosted run{RUN} at {HEAD}. Own first failed module: {ownfail['module']} ({ownfail['seconds']}s). Full {len(d['order'])} roots remain in unchanged order; {len(actual)} changed copies and {len(unchanged)} unchanged.\n\nOwn observed repair: {', '.join(observed)}. Preventive/unreached matching source copies: {', '.join(preventive)}. All matching canonical roots in this six-packet scope are propagated byte-identically. Historical metadata and own outputs are preserved, not rewritten.\n\n{disclosure}\n\nRun{RUN} verified PrimeIsogenyFibers and InnerRelations before ProjectiveLevel in trace/character/infinity; actual zero55 completed OrderGalois before FiniteRamification; torsion35 completed DescendedMetric before Representatives. Cotangent61's authentic error locates a kernel deterministic timeout in sourceTower, followed by180.103s wall limit. Opaque helper staging is only a source candidate, not a demonstrated timeout fix. No repaired-module or complete successor pass is claimed.\n\nNo imports or roots are added, no accepted baseline, toolchain, resource ceiling or trust setting changes, and no local Lean/Lake runs. Existing predecessor limitations remain; unrelated lattice16 and new inactive research are outside this packet. Native planning and review are source/structure only. Hosted full-module completion and recursive new-declaration audits remain required.\n''')
 refs=[n+'.lean' for n in actual]+[EV+'/canonical/before/'+n+'.lean' for n in actual]
 contracts={n:EV+'/canonical/'+records[n]['contract'] for n in actual}
 evidence=['README.md','COPY-BINDINGS.json',EV+'/own-hosted/RESULT.json',EV+'/canonical/SOURCE-HASHES.json']+list(dict.fromkeys(contracts.values()))
 obligations=[]
 for i,id in enumerate(ids):
  obligations.append({'id':id,'required_input':'Exact original objects, domains, native interfaces, exceptional cases and full input coverage are specified in the bound canonical clauses for each source present here.','constructed_input':'\n\n'.join(n+': '+cl[n][i] for n in actual),'justification':'Propagate only independently source-reviewed exact source bytes after checking this copy against an explicitly bound predecessor. Distinguish own first failure from preventive sibling propagation. No desired endpoint becomes an assumption.','scope_modules':actual,'source_references':refs,'evidence':evidence,'canonical_clauses':{n:{'contract':contracts[n],'clause_number':i+1} for n in actual}})
 app={'packet':new,'predecessor':old,'status':'DRAFT_SOURCE_REPAIR_HOSTED_PENDING','source_commit':HEAD,'integration_base_commit':HEAD,'run_id':RUN,'local_lean_run':False,'kernel_verified':False,'independently_accepted':False,'resources_changed':False,'full_arithmetic_theorem_proved':False,'public_telescopes_changed':bool(telescope),'public_telescope_disclosure':disclosure,'explicit_type_or_retained_binder_modules':telescope,'modified_predecessor_modules':actual,'observed_failure_repair_modules':observed,'preventive_unreached_modules':preventive,'diagnostic_only_modules':[],'candidate_repair_modules':actual,'new_modules':[],'obligations':obligations,'canonical_source_contracts':contracts,'intake_sha256':h(dst/'intake.json'),'sources':{n:h(dst/n) for n in d['files']},'machine_contract_status':'DRAFT_REQUIRES_INDEPENDENT_PROPAGATION_REVIEW'}
 app['bindings']={str(p.relative_to(dst)):h(p) for p in dst.rglob('*') if p.is_file() and (p.parent!=dst or p.name in ['README.md','COPY-BINDINGS.json'])};dump(dst/'APPLICATION.json',app)
 if not (OUT/old).exists():(OUT/old).symlink_to(src,target_is_directory=True)
 row={'predecessor':old,'successor':new,'changed':actual,'order_count':len(d['order']),'intake_sha256':h(dst/'intake.json'),'application_sha256':h(dst/'APPLICATION.json'),'own_failure':ownfail};dump(dst/'NEXT-ROW.json',row);rows.append(row)
 # Validate against exact-head immutable predecessor via local materialization, not symlink escape.
 prior=OUT/old
 if prior.is_symlink():
  prior.unlink();prior.mkdir();shutil.copyfile(src/'intake.json',prior/'intake.json')
  for n in d['order']:shutil.copyfile(src/(n+'.lean'),prior/(n+'.lean'))
 pe.packet(new,ci.derive_plan(),OUT);checks.append({'packet':new,'native_source_check':'PASS','roots':len(d['order']),'changed':actual,'binding_count':len(app['bindings'])});print('PACKET_SOURCE_PASS',new,len(actual),flush=True)
dump(R/'NEXT-SUCCESSOR-MAP.json',{'base':HEAD,'run':RUN,'mapping':M,'packets':rows,'local_lean_run':False});dump(R/'STRUCTURAL-CHECK.json',{'checks':checks,'local_lean_run':False,'kernel_verified':False})
