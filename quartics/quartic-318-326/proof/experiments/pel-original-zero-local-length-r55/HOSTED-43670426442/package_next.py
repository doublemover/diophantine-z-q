from pathlib import Path
import json,hashlib,shutil,re,subprocess,sys
R=Path(__file__).resolve().parent;W=R.parents[1];REPO=W/'integration-20261114/repo';EX=REPO/'quartics/quartic-318-326/proof/experiments';OUT=R/'successors';HOST=W/'integration-next-43667489535/hosted-43670426442';C=R/'canonical';HEAD='7cbf02dd9bed3447c5d46502ebeb4f4c7aa7221b'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
M={'pel-original-character-ordered-biholomorph-r25':'pel-original-character-ordered-biholomorph-r26','pel-original-zero-local-length-r52':'pel-original-zero-local-length-r53','pel-original-cotangent-hzero-forty-r58':'pel-original-cotangent-hzero-forty-r59','pel-original-torsion-towers-r32':'pel-original-torsion-towers-r33','height-original-normal-infinity-trace-r25':'height-original-normal-infinity-trace-r26','original-infinity-range-extension-r7':'original-infinity-range-extension-r8'}
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip()==HEAD
sys.path.insert(0,str(REPO/'scripts'));import check_progress_lean as ci,check_progress_experiment as pe
records=json.loads((C/'SOURCE-HASHES.json').read_text());assert len(records)==7 and 'PELPositiveNormPeriodMap318' in records
OUT.mkdir(exist_ok=True);rows=[];checks=[]
ids=['required_inputs','constructed_objects','index_and_domain_coverage','transition_maps','coefficient_and_scalar_factors','local_and_exceptional_cases','identity_with_consumed_object','downstream_dependency_effects','honesty_boundary']
def clauses(rel):
 p=C/rel
 if p.suffix=='.json':
  d=json.loads(p.read_text());return ['; '.join(str(x.get(k,'')) for k in ['required_input','constructed_input','justification']) for x in d['obligations']]
 text=p.read_text();parts=re.findall(r'^([1-9])\. (.*?)(?=\n[1-9]\. |\Z)',text,re.M|re.S)
 assert len(parts)==9,(p,len(parts));return [s.strip() for _,s in parts]
cl={n:clauses(r['contract']) for n,r in records.items()};assert all(len(v)==9 for v in cl.values())
for old,new in M.items():
 own=HOST/('experiment-'+old)/'progress-experiments'/old;src=EX/old;dst=OUT/new
 assert not dst.exists(),dst
 d=json.loads((src/'intake.json').read_text());result=json.loads((own/'RESULT.json').read_text());assert result['packet_sha256']==h(src/'intake.json')
 shutil.copytree(src,dst);ev=dst/'HOSTED-43670426442';ev.mkdir()
 for p in src.iterdir():
  if p.is_file() and p.suffix!='.lean':
   q=ev/'PREDECESSOR-METADATA'/p.name;q.parent.mkdir(exist_ok=True);shutil.copyfile(p,q)
 shutil.copytree(own,ev/'own-hosted');shutil.copytree(C,ev/'canonical');shutil.copyfile(Path(__file__),ev/'package_next.py')
 actual=[]
 for n in d['order']:
  p=src/(n+'.lean');assert h(p)==d['files'][p.name]['sha256']
  if n in records:
   assert h(p)==records[n]['before_sha256'],(old,n)
   shutil.copyfile(C/'after'/p.name,dst/p.name);actual.append(n)
   assert re.findall(r'^.*set_option.*$',p.read_text(),re.M)==re.findall(r'^.*set_option.*$',(dst/p.name).read_text(),re.M)
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
 telescope=[n for n in actual if n=='IntegralGlobalLocalCompletion318']
 observed=[n for n in actual if n==ownfail['module']];preventive=[n for n in actual if n not in observed]
 disclosure='Original hypotheses remain. IntegralGlobalLocalCompletion, where present, changes two local instances to named exposed hR-based constructions and uses letI domain/DVR in Completion and public theorem types/bodies; this is explicitly a type/instance-scope change, not blanket unchanged signatures. PositiveNormPeriodMap removes two invalid anonymous section-local DiscreteTopology instances and supplies those same constructions proof-locally; existing public telescopes are unchanged. OrderAutomorphisms adds a proved exact sign-map helper. BranchLocalization preserves actual scalar dictionaries with a direct smul_assoc proof. ResidueFrobenius adds the pinned native finite-field import for symbolic pow_card; no new hypotheses. All resource options and original domains remain unchanged.'
 bind={'predecessor':old,'successor':new,'copies':{n:records[n] for n in actual},'unchanged_count':len(unchanged),'full_order_count':len(d['order']),'own_result_sha256':h(own/'RESULT.json'),'own_predecessor_intake_sha256':h(src/'intake.json'),'resources_changed':False,'public_telescopes_changed':bool(telescope),'explicit_type_or_retained_binder_modules':telescope,'observed_failure_repair_modules':observed,'preventive_unreached_modules':preventive}
 dump(dst/'COPY-BINDINGS.json',bind)
 (dst/'README.md').write_text(f'''# {new}\n\nSource-only successor to {old}, exact hosted run43670426442 at {HEAD}. Own first failed module: {ownfail['module']} ({ownfail['seconds']}s). Full {len(d['order'])} roots in unchanged order; {len(actual)} changed copies and {len(unchanged)} unchanged.\n\nCanonical scope present: {', '.join(actual)}. Own observed failed-source repair: {', '.join(observed)}. Preventive/unreached matching repairs: {', '.join(preventive)}.\n\n{disclosure}\n\nActual full-module advances in this run include IntegralPeriodMap in character and trace, ReductionAction in infinity, and LevelThetaFourier plus Independence in torsion. Current own failures remain PositiveNormPeriodMap, ResidueFrobenius, OrderAutomorphisms, BranchLocalization and MetricSmoothCoefficient. Current source repairs address exact proof-local discreteness, symbolic conjugation/Frobenius, actual sign-map carrier identity, existing scalar-tower dictionary compatibility, and typed real smoothness staging. IntegralGlobalLocalCompletion and DVRTwistSquareNormalization are preventive and unreached in trace only; trace's own PositiveNormPeriodMap failure remains its evidence. No timing improvement or full module acceptance is asserted for any current candidate.\n\nEvery matching canonical root is propagated byte-identically. Each source has its own exact independently reviewed nine-obligation contract; packet obligations below include only clauses for sources present here. Own predecessor metadata and authentic outputs are preserved, not rewritten. Older distinct Restrictions, other lattice lanes and new analytic/quartic research remain outside scope. No added roots or new research activation in the 535-root infinity packet, no local Lean/Lake, resource/trust changes or endpoint acceptance claim.\n''')
 refs=[n+'.lean' for n in actual]+['HOSTED-43670426442/canonical/before/'+n+'.lean' for n in actual]
 contracts={n:'HOSTED-43670426442/canonical/'+records[n]['contract'] for n in actual}
 evidence=['README.md','COPY-BINDINGS.json','HOSTED-43670426442/own-hosted/RESULT.json','HOSTED-43670426442/canonical/SOURCE-HASHES.json']+list(dict.fromkeys(contracts.values()))
 obligations=[]
 for index,id in enumerate(ids):
  obligations.append({'id':id,'required_input':'Exact original inputs and native APIs are specified per canonical source in the bound source contracts. No source outside scope_modules is included.','constructed_input':'\n\n'.join(n+': '+cl[n][index] for n in actual),'justification':'Use only the exact reviewed source under its original hypotheses and own observed/preventive status. No research construction or desired endpoint becomes a premise.','scope_modules':actual,'source_references':refs,'evidence':evidence,'canonical_clauses':{n:{'contract':contracts[n],'clause_number':index+1} for n in actual}})
 app={'packet':new,'predecessor':old,'status':'DRAFT_SOURCE_REPAIR_HOSTED_PENDING','source_commit':HEAD,'integration_base_commit':HEAD,'run_id':43670426442,'local_lean_run':False,'kernel_verified':False,'independently_accepted':False,'resources_changed':False,'full_arithmetic_theorem_proved':False,'public_telescopes_changed':bool(telescope),'public_telescope_disclosure':disclosure,'explicit_type_or_retained_binder_modules':telescope,'modified_predecessor_modules':actual,'observed_failure_repair_modules':observed,'preventive_unreached_modules':preventive,'new_modules':[],'obligations':obligations,'canonical_source_contracts':contracts,'intake_sha256':h(dst/'intake.json'),'sources':{n:h(dst/n) for n in d['files']},'machine_contract_status':'DRAFT_REQUIRES_INDEPENDENT_PROPAGATION_REVIEW'}
 app['bindings']={str(p.relative_to(dst)):h(p) for p in dst.rglob('*') if p.is_file() and (p.parent!=dst or p.name in ['README.md','COPY-BINDINGS.json'])};dump(dst/'APPLICATION.json',app)
 if not (OUT/old).exists():shutil.copytree(src,OUT/old)
 row={'predecessor':old,'successor':new,'changed':actual,'order_count':len(d['order']),'intake_sha256':h(dst/'intake.json'),'application_sha256':h(dst/'APPLICATION.json')};dump(dst/'NEXT-ROW.json',row);rows.append(row)
 pe.packet(new,ci.derive_plan(),OUT);checks.append({'packet':new,'native_source_check':'PASS','roots':len(d['order']),'changed':actual,'binding_count':len(app['bindings'])});print('PACKET_SOURCE_PASS',new,len(actual),flush=True)
dump(R/'NEXT-SUCCESSOR-MAP.json',{'base':HEAD,'mapping':M,'packets':rows,'local_lean_run':False});dump(R/'STRUCTURAL-CHECK.json',{'checks':checks,'local_lean_run':False,'kernel_verified':False})
