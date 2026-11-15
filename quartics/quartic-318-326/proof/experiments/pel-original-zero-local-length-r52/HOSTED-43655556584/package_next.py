from pathlib import Path
import json,hashlib,shutil,re,subprocess,sys
R=Path(__file__).resolve().parent;REPO=R.parent/'integration-20261114/repo';EX=REPO/'quartics/quartic-318-326/proof/experiments';OUT=R/'next-successors';HOST=R.parent/'integration-next-43652368511/hosted-43655556584';C=R/'canonical';HEAD='6b664f8406d512c50432425e3bd616447ff8ad8e'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
M={'pel-original-character-ordered-biholomorph-r20':'pel-original-character-ordered-biholomorph-r21','pel-original-zero-local-length-r47':'pel-original-zero-local-length-r48','pel-original-cotangent-hzero-forty-r53':'pel-original-cotangent-hzero-forty-r54','pel-original-torsion-towers-r27':'pel-original-torsion-towers-r28','height-original-normal-infinity-trace-r20':'height-original-normal-infinity-trace-r21','original-infinity-range-extension-r2':'original-infinity-range-extension-r3'}
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip()==HEAD
sys.path.insert(0,str(REPO/'scripts'));import check_progress_lean as ci
records=json.loads((C/'SOURCE-HASHES.json').read_text()); OUT.mkdir(exist_ok=True);rows=[]
ids=['required_inputs','constructed_objects','index_and_domain_coverage','transition_maps','coefficient_and_scalar_factors','local_and_exceptional_cases','identity_with_consumed_object','downstream_dependency_effects','honesty_boundary']
texts=[
('Original actual theta, native normed-space and derivative APIs; original generic sign map and full prime residue map.','Supply actual linearMap n as explicit opNorm theorem argument; typed derivative identity; native SmoothSeries public import; original tensor expression on both sides of GenericSigns base equation; eight explicit symbolic residue coordinate identities.','All five canonical repairs preserve original theorem statements and mathematical inputs; no positivity binder changes in this wave.'),
('Actual ComplexVectors=Fin2→C, frequencies Z×Z, full original order coordinates, z:Fin2→ZMod(prime i), original restricted generic map.','The unchanged definitions of linearMap, theta, derivative, residue and lift feed the rewritten proofs.','No new target outcome, lattice, function, scalar or sign convention is inserted as a premise.'),
('All four prime indices with literal carriers2,3,5,7; both coordinates; every symbolic residue vector; full theta sum in C².','Eight row identities are checked algebraically before natCast_zmod_val and typed modular facts; full preconnected-ball Frechet differentiation remains.','No vector enumeration, sampled finite-frequency substitute, one-variable restriction or generic-locus-only claim.'),
('Native theta derivative chain rule; unchanged toTensor/restrictedAlgHom/equivalence composition; exact original residue lift.','Expose term and derivative at their actual types, combine the same two scalar actions. GenericSigns uses explicit toTensor coordinate on both sides before original base normalization.','Directions of maps, signs, compositions and all constructed objects remain unchanged.'),
('Derivative coefficient term*(2*pi*I), same Gaussian bounds, exact prime lift row coefficients.','The derivative combines exp and2*pi*I via smul_smul; residues retain all13 original ordinary decidable modular coefficient facts.','No dropped factor, new normalization, changed lifting coefficients or guessed field action.'),
('Existing positive tau and scale premises, unchanged generic b/sign domains, all four primes and both vector coordinates.','The new fixed proofs add no mathematical assumption and exclude no points. Scaled derivative is structurally the same proof-only preventative edit.','Existing telescope corrections from earlier versions remain; none are added or silently removed now.'),
('Exact full theta and characteristic subseries consumers; actual original generic sign action; original orderResidue and rightMultiply kernel equality.','Same named declarations and types, actual source objects, all native maps unchanged.','No setwise surrogate, unrelated elliptic model, theorem wrapper or assumption of desired conclusion.'),
('Every matching canonical root in each current successor, own predecessor intake and own43655556584RESULT.','All matching roots are replaced byte-identically, complete root order retained. Active infinity535r2 receives only repairs as535r3; later539/540 research is not merged.','No claim that five evaluator producers or later535 infinity extension sources were reached. They remain unchanged after upstream residue failure.'),
('Independent source review and native structural checks must be separated from strict hosted kernel acceptance.','Own runs show scaled/unscaled convergence pass, then Holomorphy failure; GenericSigns coercion failure; or Residues cast/no-progress failure. Exact source fixes reviewed independently.','No local Lean/Lake, trust or resource increases, new admissions, active research-source additions or full arithmetic theorem claim. Hosted successor validation remains pending.')]
texts[7]=(texts[7][0],texts[7][1]+' Exact identical-before IntegralSourceArithmeticDomain318 also receives the independently reviewed coefficient-map proof repair wherever present (trace21 only), explicitly preventive/unreached there.',texts[7][2])
for old,new in M.items():
 own=HOST/('experiment-'+old)/'progress-experiments'/old
 assert (own/'RESULT.json').exists(),old
 src=EX/old;dst=OUT/new
 assert not dst.exists(),dst
 d=json.loads((src/'intake.json').read_text());result=json.loads((own/'RESULT.json').read_text());assert result['packet_sha256']==h(src/'intake.json')
 shutil.copytree(src,dst);ev=dst/'HOSTED-43655556584';ev.mkdir()
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
  if Path(n).stem in actual: row['imports']=sorted(ci.import_names((dst/n).read_text()))
 dump(dst/'intake.json',d)
 failed=[x for x in result['commands'] if x['exit_code']];assert failed
 ownfail=failed[0]
 bind={'predecessor':old,'successor':new,'copies':{n:records[n] for n in actual},'unchanged_count':len(unchanged),'full_order_count':len(d['order']),'own_result_sha256':h(own/'RESULT.json'),'own_predecessor_intake_sha256':h(src/'intake.json'),'resources_changed':False,'public_telescopes_changed':False}
 dump(dst/'COPY-BINDINGS.json',bind)
 (dst/'README.md').write_text(f'''# {new}\n\nSource-only successor to {old} from exact hosted run43655556584 at {HEAD}. Own first failed module: {ownfail['module']} ({ownfail['seconds']}s). Full {len(d['order'])} roots in exact order; {len(actual)} changed copies, {len(unchanged)} unchanged.\n\nCanonical scope present here: {', '.join(actual)}. Every matching canonical source is propagated. All theorem telescopes and resource options unchanged.\n\nTheta fixes supply the missing explicit continuous-linear-map argument, normalize the unchanged derivative by typed scalar-action equality, and import the exact native SmoothSeries theorem. The scaled derivative repair is preventive and was not reached. GenericSigns exposes both sides of the same tensor-coordinate/base equation before applying the same native algebra-map commutation theorem. Residues proves8 actual integer-coefficient row identities before explicit cast reduction and typed modular coefficients, avoiding the failing ring_nf no-progress path. All13 ordinary coefficient facts and arbitrary symbolic z remain.\n\nOwn predecessor metadata and actual hosted outputs are preserved, not rewritten. Source review is not Lean acceptance. No local Lean/Lake, admissions, resource changes or endpoint acceptance claims. Original infinity535 sources remain unchanged beyond upstream repairs; no539/540 research or separate quartic/period drafts are added.\n''')
 refs=[n+'.lean' for n in actual]+['HOSTED-43655556584/canonical/before/'+n+'.lean' for n in actual]
 evidence=['README.md','COPY-BINDINGS.json','HOSTED-43655556584/own-hosted/RESULT.json','HOSTED-43655556584/canonical/SOURCE-HASHES.json']
 app={'packet':new,'predecessor':old,'status':'DRAFT_SOURCE_REPAIR_HOSTED_PENDING','source_commit':HEAD,'integration_base_commit':HEAD,'run_id':43655556584,'local_lean_run':False,'kernel_verified':False,'independently_accepted':False,'resources_changed':False,'full_arithmetic_theorem_proved':False,'public_telescopes_changed':False,'public_telescope_disclosure':'All five canonical repairs are proof-only, with one explicit native library import. No theorem type changes in this wave.','modified_predecessor_modules':actual,'new_modules':[],'obligations':[{'id':i,'required_input':a,'constructed_input':b,'justification':c,'scope_modules':actual,'source_references':refs,'evidence':evidence} for i,(a,b,c) in zip(ids,texts)],'intake_sha256':h(dst/'intake.json'),'sources':{n:h(dst/n) for n in d['files']},'machine_contract_status':'DRAFT_REQUIRES_INDEPENDENT_PROPAGATION_REVIEW'}
 app['bindings']={str(p.relative_to(dst)):h(p) for p in dst.rglob('*') if p.is_file() and (p.parent!=dst or p.name in ['README.md','COPY-BINDINGS.json'])};dump(dst/'APPLICATION.json',app)
 if not (OUT/old).exists():shutil.copytree(src,OUT/old)
 row={'predecessor':old,'successor':new,'changed':actual,'order_count':len(d['order']),'intake_sha256':h(dst/'intake.json'),'application_sha256':h(dst/'APPLICATION.json')};dump(dst/'NEXT-ROW.json',row);rows.append(row);print('PREPARED',new,len(actual),flush=True)
dump(R/'NEXT-SUCCESSOR-MAP.json',{'base':HEAD,'mapping':{r['predecessor']:r['successor'] for r in rows},'packets':rows,'local_lean_run':False})
sys.path.insert(0,str(REPO/'scripts'));import check_progress_experiment as pe,check_progress_lean as ci
plan=ci.derive_plan()
for row in rows:pe.packet(row['successor'],plan,OUT);print('PACKET_SOURCE_PASS',row['successor'],flush=True)
