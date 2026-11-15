from pathlib import Path
import json,hashlib,shutil,re,subprocess,sys
R=Path(__file__).resolve().parent;REPO=R.parent/'integration-20261114/repo';EX=REPO/'quartics/quartic-318-326/proof/experiments';OUT=R/'next-successors';HOST=R.parent/'integration-20261114/hosted-43652368511';C=R/'next-canonical';HEAD='2e4471d08710d58a1fdc2353b62a30023d88e94e'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
M={'pel-original-character-ordered-biholomorph-r19':'pel-original-character-ordered-biholomorph-r20','pel-original-zero-local-length-r46':'pel-original-zero-local-length-r47','pel-original-cotangent-hzero-forty-r52':'pel-original-cotangent-hzero-forty-r53','pel-original-torsion-towers-r26':'pel-original-torsion-towers-r27','height-original-normal-infinity-trace-r19':'height-original-normal-infinity-trace-r20','original-regular-coordinate-injectivity-r3':'original-regular-coordinate-injectivity-r4'}
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip()==HEAD
records=json.loads((C/'SOURCE-HASHES.json').read_text()); OUT.mkdir(exist_ok=True);rows=[]
ids=['required_inputs','constructed_objects','index_and_domain_coverage','transition_maps','coefficient_and_scalar_factors','local_and_exceptional_cases','identity_with_consumed_object','downstream_dependency_effects','honesty_boundary']
texts=[
('Original quaternionic τ with 0<τ.im and scaled a with 0<a; arbitrary four-bit sign group g and b:Fin4→C.','Explicit existing positivity binders retained in23 theta declarations (37 binders where entire set present). Generic sign split matches native g i=1 simplification.','Public theta telescopes change; no desired summability, holomorphy, independence or equivariance result is inserted as an assumption.'),
('Actual full original theta functions and derivatives; independent affine ring, tensor order and generic coefficient embedding.','All intended definitions/maps unchanged. Ten whitespace token separations permit intended absolute-value multiplication; two Gaussian target lambdas are exposed.','No surrogate function, new lattice, abstract action or field component replacement.'),
('Every integer-pair frequency, arbitrary fixed predicate, positive scale and nonzero level; all four sign indices and all affine ring elements.','Same exact source domains and exhaustive sign cases, full Fourier sum, norm bounds and characteristic functions.','No finite truncation, sampled point, generic-locus-only restriction or selected summand.'),
('Original derivatives/Fourier maps and exact tensor equivalence/coefficient embedding.','Generic base-coordinate proof specifies original signEquiv and Polynomial.X; both sides expose the existing affineEmbedding composition.','No map direction, identity, multiplication convention or scalar is changed.'),
('Gaussian exponent -pi*((a*coercive τ)*n^2-2*S*abs n) and k0/k1; scalar signs+1/-1.','Positive product a*coercive τ uses exact ha,hτ. Closing absolute bars are separated from multiplication tokens.','No half-factor, coefficient, root sign, gauge or energy bound is removed.'),
('Positivity, nonzero level and arbitrary fixed DecidablePred are retained; all zero frequencies and sign cases remain.','Termwise identities not needing positivity remain unconditional; three audited false positives retain hτ already in their dependent types.','No new excluded points, inverse-zero assumption or additional mathematical premise outside existing section positivity.'),
('The exact full original sums feed holomorphy, Fourier coefficients, independence and C1 consumers; affineEmbedding feeds the original generic sign action.','Same literal named producer results; retained public binders match existing calls; coordinate proofs target the original maps.','Residue lift/residueHom/surjectivity/kernel producers stay identical; four concrete carrier branches have no new premise. Only mathematically required theta section premises are retained; no target conclusion or replacement object is assumed.'),
('Every matching canonical source in each successor must receive exact reviewed bytes with own predecessor evidence.','Only listed scope_modules change; full order, imports and options preserved. Old metadata and own hosted RESULT are bound separately.','Five evaluator producers and geometry sources stay untouched; no inference of evaluator or geometry acceptance from these repairs.'),
('Source/structural review differs from hosted Lean and full declaration audit.','Actual run43652368511 passed Stabilizers and unscaled Convergence in their own lanes; failed GenericSigns, scaled convergence or Residues. Residues now exposes concrete prime carriers in four symbolic-vector branches; the previous simplifier-only attempt failed. Other theta files are preventive/unreached.','No local Lean/Lake, new trust/resource settings or admitted proof. All successor checks are pending hosted kernel acceptance; original/Table period research is not in this batch.')]
for old,new in M.items():
 own=HOST/('experiment-'+old)/'progress-experiments'/old
 if not (own/'RESULT.json').exists():print('WAIT_OWN_EVIDENCE',old,flush=True);continue
 src=EX/old;dst=OUT/new
 if dst.exists():
  rows.append(json.loads((dst/'NEXT-ROW.json').read_text()));continue
 d=json.loads((src/'intake.json').read_text());result=json.loads((own/'RESULT.json').read_text());assert result['packet_sha256']==h(src/'intake.json')
 shutil.copytree(src,dst);ev=dst/'HOSTED-43652368511';ev.mkdir()
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
 for n,row in d['files'].items():row['sha256']=h(dst/n)
 dump(dst/'intake.json',d)
 failed=[x for x in result['commands'] if x['exit_code']];assert failed
 ownfail=failed[0]
 bind={'predecessor':old,'successor':new,'copies':{n:records[n] for n in actual},'unchanged_count':len(unchanged),'full_order_count':len(d['order']),'own_result_sha256':h(own/'RESULT.json'),'own_predecessor_intake_sha256':h(src/'intake.json'),'resources_changed':False}
 dump(dst/'COPY-BINDINGS.json',bind)
 (dst/'README.md').write_text(f'''# {new}\n\nSource-only successor to {old} from exact hosted run43652368511 at {HEAD}. Own first failed module: {ownfail['module']} ({ownfail['seconds']}s). Original full {len(d['order'])} roots remain in exact order; {len(actual)} changed copies and {len(unchanged)} unchanged.\n\nCanonical repairs present here: {', '.join(actual)}.\n\nThe complete theta set retains37 existing positivity binders in23 public telescopes, exposes2 Gaussian target lambdas, and separates10 absolute-value multiplication tokens. Per-packet scope is explicit and not every packet contains this entire set. Residues keeps all13 ordinary modular facts and the same symbolic z, with explicit four literal prime carriers; previous repair was not accepted. GenericSigns has3 proof-only changes matching native errors: matching the native sign predicate, explicit base Algebra instance, and the exact original affineEmbedding composition. No mathematical definitions, map directions, frequency domains or intended scalars change.\n\nOwn predecessor metadata and hosted output are immutable dated evidence; current contracts are separate. Source acceptance is not Lean acceptance. No local Lean/Lake, admissions, resource changes or declaration audit claims. Other theta consumers are preventive/unreached in the earlier lane; geometry and new evaluator production are unchanged. The five new full-period research modules are not included.\n''')
 refs=[n+'.lean' for n in actual]+['HOSTED-43652368511/canonical/before/'+n+'.lean' for n in actual]
 evidence=['README.md','COPY-BINDINGS.json','HOSTED-43652368511/own-hosted/RESULT.json','HOSTED-43652368511/canonical/SOURCE-HASHES.json']
 app={'packet':new,'predecessor':old,'status':'DRAFT_SOURCE_REPAIR_HOSTED_PENDING','source_commit':HEAD,'integration_base_commit':HEAD,'run_id':43652368511,'local_lean_run':False,'kernel_verified':False,'independently_accepted':False,'resources_changed':False,'full_arithmetic_theorem_proved':False,'public_telescopes_changed':any('ScaledTheta' in n or 'LevelTheta' in n or 'ThetaContinuousDerivative' in n for n in actual),'public_telescope_disclosure':'Where present23 declarations retain37 existing hτ/ha positive premises; unscaled Holomorphy only whitespace, GenericSigns only proofs.','modified_predecessor_modules':actual,'new_modules':[],'obligations':[{'id':i,'required_input':a,'constructed_input':b,'justification':c,'scope_modules':actual,'source_references':refs,'evidence':evidence} for i,(a,b,c) in zip(ids,texts)],'intake_sha256':h(dst/'intake.json'),'sources':{n:h(dst/n) for n in d['files']},'machine_contract_status':'DRAFT_REQUIRES_INDEPENDENT_PROPAGATION_REVIEW'}
 app['bindings']={str(p.relative_to(dst)):h(p) for p in dst.rglob('*') if p.is_file() and (p.parent!=dst or p.name in ['README.md','COPY-BINDINGS.json'])};dump(dst/'APPLICATION.json',app)
 if not (OUT/old).exists():shutil.copytree(src,OUT/old)
 row={'predecessor':old,'successor':new,'changed':actual,'order_count':len(d['order']),'intake_sha256':h(dst/'intake.json'),'application_sha256':h(dst/'APPLICATION.json')};dump(dst/'NEXT-ROW.json',row);rows.append(row);print('PREPARED',new,len(actual),flush=True)
dump(R/'NEXT-SUCCESSOR-MAP.json',{'base':HEAD,'mapping':{r['predecessor']:r['successor'] for r in rows},'packets':rows,'local_lean_run':False})
sys.path.insert(0,str(REPO/'scripts'));import check_progress_experiment as pe,check_progress_lean as ci
plan=ci.derive_plan()
for row in rows:pe.packet(row['successor'],plan,OUT);print('PACKET_SOURCE_PASS',row['successor'],flush=True)
