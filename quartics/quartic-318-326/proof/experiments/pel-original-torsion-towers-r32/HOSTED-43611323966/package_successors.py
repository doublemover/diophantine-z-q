from pathlib import Path
import json,hashlib,shutil,zipfile,re,sys,subprocess
R=Path(__file__).resolve().parent;REPO=R.parent/'integration-20261114/repo';EX=REPO/'quartics/quartic-318-326/proof/experiments';OUT=R/'successors';C=R/'repair';HEAD='2428de0d42f12dc71e2bc6f19495025a5912d41c'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,a):p.write_text(json.dumps(a,indent=2)+'\n')
records=json.loads((C/'SOURCE-HASHES.json').read_text())
M={'character':('pel-original-character-ordered-biholomorph-r18','pel-original-character-ordered-biholomorph-r19'),'zero':('pel-original-zero-local-length-r45','pel-original-zero-local-length-r46'),'cotangent':('pel-original-cotangent-hzero-forty-r51','pel-original-cotangent-hzero-forty-r52'),'torsion':('pel-original-torsion-towers-r25','pel-original-torsion-towers-r26'),'trace':('height-original-normal-infinity-trace-r18','height-original-normal-infinity-trace-r19'),'injectivity':('original-regular-coordinate-injectivity-r2','original-regular-coordinate-injectivity-r3')}
ids=['required_inputs','constructed_objects','index_and_domain_coverage','transition_maps','coefficient_and_scalar_factors','local_and_exceptional_cases','identity_with_consumed_object','downstream_dependency_effects','honesty_boundary']
texts=[
('Residues: every i:Fin4 and arbitrary z:Fin2→ZMod(prime i). Stabilizers: arbitrary b, group elements and points. Theta: integer Gaussian source requires positive T; actual hτ:0<τ.im.','Same original inputs, explicitly specialized dependent prime carrier, separated Prod.ext goals, and T=coercive τ with coercive_positive τ hτ.','No caller premise is added to residue/stabilizers. Six immediate theta modules explicitly retain the existing positivity premise in 21 public telescopes; this changes their public signatures and is not unconditional summability/holomorphy.'),
('Original integral lift/residue maps, actual sign action on original finite/infinity charts, original omega/complex theta series and derivative/tori.','All definitions remain byte-identical; summands are explicitly eta-expanded only within proof goals.','No surrogate lattice, finite theta truncation, new action or substitute analytic function.'),
('All four norm primes 2,3,5,7, both coordinates and symbolic residue vectors; both finite and infinity charts; full ℤ² theta and all complex vectors.','Same fin_cases/ext coverage and full original theorem quantifiers. Every original index order and root source closure retained.','No generic-locus restriction, sampled vector or positive-frequency-only replacement.'),
('Native integer val/cast into each ZMod, original sign multiplication, original theta derivative evaluation and real-torus comparison maps.','Normalize dependent prime type before coefficient rewrites; original maps remain exact; actual callers already provide τ hτ.','Changing proof presentation/section-variable retention does not change map direction, multiplication or identity.'),
('Exact closed modular coefficients including -97 modulo7, original complex gauge and Gaussian energy constants.','All thirteen ordinary decide facts retained. sub_eq_add_neg exposes the existing negative coefficient; k=0,1,2 and coercive τ unchanged.','No coefficient, Euler factor, gauge, norm or scalar dropped.'),
('All zero residue coordinates, ramified branch fixed loci, infinity signs, zero integer frequency and arbitrary real representative. Theta requires the upper-half-plane condition.','Original exceptional cases retained. hτ is now explicitly retained on six immediate consumers where only proofs depend on it.','No new excluded point/frequency or hypothetical positivity theorem.'),
('residue_lift must feed residue_surjective/orderResidue/kernel; action laws and exact stabilizer statements feed original inertia; theta sums feed derivatives, Fourier coefficient and gauged value.','Same named producer targets and original maps/definitions. The only signature changes are 21 retained positivity binders; immediate source calls already supply them.','Explicit sum goals are definitional unfoldings of oneBound/weightedOne/weightedTwo; Prod.ext proves original coordinate pair equality.'),
('All active PEL and evaluator copies of each changed source need exact propagation, while geometric and evaluator producer claims remain separate.','Every matching source in these six successors receives byte-identical canonical repair. Remaining roots, imports, order and resource options are unchanged.','Signs remains the previously hosted-passed version. The five evaluator modules are unchanged and were not reached in own r2. Geometry trace remains unverified and inherits the earlier center-only Global pass/Common failure boundary.'),
('Distinguish source-level repair review, structural validation, authentic first failures and kernel acceptance.','Observed Convergence, Stabilizers and Residues failures bind own run43611323966 results. Six theta consumers are preventive, unreached and not represented as observed failures.','No local Lean/Lake, no admission/trust/resource change, no full packet or arithmetic theorem pass. Later theta binder candidates remain deferred in canonical DEFERRED-THETA-AUDIT.md.')]
OUT.mkdir(exist_ok=True);rows=[]
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip()==HEAD
for lane,(old,new) in M.items():
 src=EX/old;dst=OUT/new
 assert not dst.exists(),dst
 # Copy immutable historical evidence exactly, moving current metadata to a dated snapshot below before replacing it.
 shutil.copytree(src,dst)
 ev=dst/'HOSTED-43611323966';ev.mkdir()
 for p in src.iterdir():
  if p.is_file() and p.suffix!='.lean':
   target=ev/'PREDECESSOR-METADATA'/p.name;target.parent.mkdir(exist_ok=True);shutil.copyfile(p,target)
 d=json.loads((src/'intake.json').read_text());actual=[]
 for n in d['order']:
  assert h(src/(n+'.lean'))==d['files'][n+'.lean']['sha256']
  if n in records:
   assert h(src/(n+'.lean'))==records[n]['before_sha256'],(old,n)
   shutil.copyfile(C/'after'/(n+'.lean'),dst/(n+'.lean'));actual.append(n)
   assert re.findall(r'^.*set_option.*$',(src/(n+'.lean')).read_text(),re.M)==re.findall(r'^.*set_option.*$',(dst/(n+'.lean')).read_text(),re.M)
 unchanged=[n for n in d['order'] if n not in actual]
 d.update(packet=new,status='DRAFT_SOURCE_REPAIR_HOSTED_PENDING',revision_classification_schema=1,new_modules=[])
 for key in ['revision_of','revision_source']:
  if key in d:d[key]=old
 if not any(k in d for k in ['revision_of','revision_source']):d['revision_of']=old
 for key in ['changed_modules','revised_modules','modified_predecessor_modules']:d[key]=actual
 for key in ['exact_predecessor_modules','unchanged_predecessor_modules','reused_modules','unchanged_upstream_modules']:
  if key in d:d[key]=unchanged if isinstance(d[key],list) else len(unchanged)
 if 'unchanged_producer_modules' in d:d['unchanged_producer_modules']=unchanged if isinstance(d['unchanged_producer_modules'],list) else len(unchanged)
 for n,row in d['files'].items():row['sha256']=h(dst/n)
 dump(dst/'intake.json',d)
 z=zipfile.ZipFile(R/'latest'/(lane+'.zip'));prefix='progress-experiments/'+old+'/'
 for n in z.namelist():
  if n.startswith(prefix) and not n.endswith('/'):
   out=ev/'own-hosted'/n[len(prefix):];out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(z.read(n))
 result=json.loads((ev/'own-hosted/RESULT.json').read_text());assert result['packet_sha256']==h(src/'intake.json')
 shutil.copytree(C,ev/'canonical');shutil.copyfile(Path(__file__),ev/'package_successors.py')
 shutil.copytree(R/'theta-preflight',ev/'RECOVERED-THETA-PREFLIGHT')
 changed={n:records[n] for n in actual}
 dump(dst/'COPY-BINDINGS.json',{'predecessor':old,'successor':new,'copies':changed,'unchanged_count':len(unchanged),'full_order_count':len(d['order']),'own_result_sha256':h(ev/'own-hosted/RESULT.json'),'own_predecessor_intake_sha256':h(src/'intake.json'),'new_evaluator_modules_reached':False if lane=='injectivity' else None,'resources_changed':False})
 own_fail=[x for x in result['commands'] if x['exit_code']][0]
 body=f'''# {new}

Source-only successor to {old}, based on actual hosted run 43611323966 at {HEAD}. Own first failed module: {own_fail['module']} ({own_fail['seconds']} seconds). Original full {len(d['order'])}-root order preserved; {len(actual)} changed copies, {len(unchanged)} unchanged.

Changes: {', '.join(actual)}. Residue proof normalizes dependent prime carriers and negative coefficients while retaining the full original map and symbolic inputs. Stabilizers separates three product extensionality subgoals. Convergence explicitly presents the native summand and corrects doc/include ordering. Where present, six immediate theta consumers receive 21 explicit existing positivity binders; weighted Gaussian goals are eta-exposed and doc ordering remains valid. These are disclosed public telescope changes, not unconditional results. The six consumer modules were not reached and are preventive source candidates.

All predecessor metadata and history are preserved verbatim under dated evidence; current application is separate. Exact own results/intake match. Signs remains unchanged and previously passed in this run. Every other source, import, resource option and baseline closure remains exact. No local Lean, declaration audit or native evaluator ran. Source/propagation review is not kernel acceptance. Later theta binder scope is explicitly deferred. No complete packet, arithmetic theorem, original scheme algebraization, rational descent or four-invariant result is claimed.
'''
 if lane=='injectivity':body+='\nAll five new evaluator/injectivity producer files remain byte-identical and were not reached before the residue failure.\n'
 if lane=='trace':body+='\nAll trace geometry sources remain unchanged and unreached. Earlier GlobalComparison success belongs to the center context only; production CommonRestriction failed. This is not trace geometry acceptance.\n'
 (dst/'README.md').write_text(body)
 refs=[n+'.lean' for n in actual]+['HOSTED-43611323966/canonical/before/'+n+'.lean' for n in actual]
 evidence=['README.md','COPY-BINDINGS.json','HOSTED-43611323966/own-hosted/RESULT.json','HOSTED-43611323966/canonical/SOURCE-HASHES.json']
 obligations=[{'id':i,'required_input':a,'constructed_input':b,'justification':c,'scope_modules':actual,'source_references':refs,'evidence':evidence} for i,(a,b,c) in zip(ids,texts)]
 app={'packet':new,'predecessor':old,'status':'DRAFT_SOURCE_REPAIR_HOSTED_PENDING','source_commit':HEAD,'integration_base_commit':HEAD,'run_id':43611323966,'claim':'Observed source repair plus explicitly preventive immediate theta consumer readiness; not kernel acceptance.','local_lean_run':False,'kernel_verified':False,'independently_accepted':False,'full_arithmetic_theorem_proved':False,'resources_changed':False,'public_telescopes_changed':any('ThetaHolomorphy318'==n[-18:] for n in actual),'public_telescope_disclosure':'Where present, six theta consumer modules retain existing hτ in 21 public theorem telescopes; observed Convergence already retained hτ in predecessor. No other public signature changes.','modified_predecessor_modules':actual,'new_modules':[],'obligations':obligations,'intake_sha256':h(dst/'intake.json'),'sources':{n:h(dst/n) for n in d['files']},'machine_contract_status':'DRAFT_REQUIRES_INDEPENDENT_PROPAGATION_REVIEW'}
 app['public_telescopes_changed']='PELOriginalThetaHolomorphy318' in actual
 # Bind all immutable history and present evidence, excluding old top-level metadata now explicitly retained as history.
 app['bindings']={str(p.relative_to(dst)):h(p) for p in dst.rglob('*') if p.is_file() and (p.parent!=dst or p.name in ['README.md','COPY-BINDINGS.json'])}
 dump(dst/'APPLICATION.json',app)
 # Validation requires full immediate predecessor sources, not old acceptance evidence.
 if not (OUT/old).exists():shutil.copytree(src,OUT/old)
 rows.append({'lane':lane,'predecessor':old,'successor':new,'changed':actual,'order_count':len(d['order']),'intake_sha256':h(dst/'intake.json'),'application_sha256':h(dst/'APPLICATION.json')})
 print(new,len(d['order']),len(actual),flush=True)
dump(R/'SUCCESSOR-MAP.json',{'base':HEAD,'mapping':{a:b for a,b in M.values()},'packets':rows,'local_lean_run':False})
sys.path.insert(0,str(REPO/'scripts'));import check_progress_experiment as pe,check_progress_lean as ci
plan=ci.derive_plan()
for row in rows:pe.packet(row['successor'],plan,OUT);print('PACKET_SOURCE_PASS',row['successor'],flush=True)
