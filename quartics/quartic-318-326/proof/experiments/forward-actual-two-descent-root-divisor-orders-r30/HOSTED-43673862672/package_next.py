from pathlib import Path
import json,hashlib,shutil,subprocess,sys,re
R=Path(__file__).resolve().parent; REPO=R.parent/'integration-20261114/repo';EX=REPO/'quartics/quartic-318-326/proof/experiments';C=R/'prepared-two-three-source-43673862672';OUT=R/'scalar-successors-43673862672';HOST=R.parent/'integration-next-43670426442/hosted-43673862672';HEAD='55ee98101d4ff8da911dac6f79fde13bd30d13a8'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
M={'forward-actual-two-descent-root-divisor-orders-r24':('forward-actual-two-descent-root-divisor-orders-r25','PreparedTwoThreeSource318','SCALAR'),'forward-original-weighted-weyl-r22-replay-r24':('forward-original-weighted-weyl-r22-replay-r25','PreparedTwoThreeSource318','SCALAR')}
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip()==HEAD
OUT.mkdir(exist_ok=True);rows=[]
ids=['required_inputs','constructed_objects','index_and_domain_coverage','transition_maps','coefficient_and_scalar_factors','local_and_exceptional_cases','identity_with_consumed_object','downstream_dependency_effects','honesty_boundary']
for old,(new,module,kind) in M.items():
 src=EX/old;dst=OUT/new;own=HOST/('experiment-'+old)/'progress-experiments'/old
 d=json.loads((src/'intake.json').read_text());result=json.loads((own/'RESULT.json').read_text());assert result['packet_sha256']==h(src/'intake.json')
 assert h(src/(module+'.lean'))==h(C/'before'/(module+'.lean'))
 assert not dst.exists(),dst
 shutil.copytree(src,dst);ev=dst/'HOSTED-43673862672';ev.mkdir()
 for p in src.iterdir():
  if p.is_file() and p.suffix!='.lean':
   q=ev/'PREDECESSOR-METADATA'/p.name;q.parent.mkdir(exist_ok=True);shutil.copyfile(p,q)
 shutil.copytree(own,ev/'own-hosted');shutil.copytree(C,ev/'canonical');shutil.copyfile(Path(__file__),ev/'package_next.py')
 for n in d['order']:
  p=src/(n+'.lean');assert h(p)==d['files'][p.name]['sha256']
 shutil.copyfile(C/'after'/(module+'.lean'),dst/(module+'.lean'))
 assert re.findall(r'^.*set_option.*$',(src/(module+'.lean')).read_text(),re.M)==re.findall(r'^.*set_option.*$',(dst/(module+'.lean')).read_text(),re.M)
 actual=[module];unchanged=[n for n in d['order'] if n!=module]
 d.update(packet=new,status='DRAFT_SOURCE_REPAIR_HOSTED_PENDING',scope='OBSERVED_HOSTED_PROOF_NORMALIZATION_REPAIR',revision_classification_schema=1,new_modules=[])
 for k in ['revision_of','revision_source']:
  if k in d:d[k]=old
 if not any(k in d for k in ['revision_of','revision_source']):d['revision_of']=old
 for k in ['changed_modules','revised_modules','modified_predecessor_modules']:d[k]=actual
 for k in ['exact_predecessor_modules','unchanged_predecessor_modules','reused_modules','unchanged_upstream_modules','unchanged_producer_modules']:
  if k in d:d[k]=unchanged if isinstance(d[k],list) else len(unchanged)
 for n,row in d['files'].items():row['sha256']=h(dst/n)
 dump(dst/'intake.json',d)
 failed=[x for x in result['commands'] if x['exit_code']];assert failed[0]['module']==module
 bind={'predecessor':old,'successor':new,'changed_module':module,'before_sha256':h(src/(module+'.lean')),'after_sha256':h(dst/(module+'.lean')),'unchanged_count':len(unchanged),'full_order_count':len(d['order']),'own_result_sha256':h(own/'RESULT.json'),'own_predecessor_intake_sha256':h(src/'intake.json'),'resources_changed':False,'public_statements_changed':False}
 dump(dst/'COPY-BINDINGS.json',bind)
 note='Expose only the local let w at actual W-nonzero, detector37 and detector33 proof surfaces, using dsimp only and matching hH normalization. Same original eventual CRT witness, label1+6^21*d, modulus384/residue64, full valuation/depth support and realization/Anchor consumers remain unchanged.'
 (dst/'README.md').write_text(f'# {new}\n\nSuccessor of {old} at {HEAD}, addressing its own run43673862672 first failure at {module} ({failed[0]["seconds"]}s). Exact full order {len(d["order"])} roots, one changed and {len(unchanged)} unchanged.\n\n{note}\n\nPreparedCongruence now passes in each own current lane. PreparedTwoThreeSource fails at three hidden local-witness proof surfaces; no full PreparedTwoThreeSource pass is claimed. Own predecessor metadata/receipt and canonical nine-obligation contract/independent review are preserved under HOSTED-43673862672. No local Lean/Lake, resource/trust increase, module acceptance or research activation.\n')
 (dst/'APPLICATION.md').write_text((C/'APPLICATION.md').read_text()+f'\nCurrent packet: {new}. Actual scope: {module}. Own immutable hosted evidence and exact before/current copies are bound in APPLICATION.json and COPY-BINDINGS.json.\n')
 texts=[l.split('. ',1)[1] for l in (C/'APPLICATION.md').read_text().splitlines() if re.match(r'^[1-9]\. ',l)];assert len(texts)==9
 texts[7]=f'Own current evidence: {old} intake equals its RESULT packet hash at HEAD{HEAD}, run43673862672. The first failure is {module} at {failed[0]["seconds"]}s after {sum(x["exit_code"]==0 for x in result["commands"])} successful commands. All preceding successful modules remain separately recorded in own-hosted/RESULT.json. Historical canonical evidence timing is not substituted for this own lane receipt.'
 (dst/'APPLICATION.md').write_text('# Current packet application contract\n\n'+''.join(f'{i+1}. {t}\n\n' for i,t in enumerate(texts)))

 refs=[module+'.lean','HOSTED-43673862672/canonical/before/'+module+'.lean'];evidence=['README.md','APPLICATION.md','COPY-BINDINGS.json','HOSTED-43673862672/own-hosted/RESULT.json','HOSTED-43673862672/canonical/'+'APPLICATION.md']
 app={'packet':new,'predecessor':old,'status':'DRAFT_SOURCE_REPAIR_HOSTED_PENDING','source_commit':HEAD,'integration_base_commit':HEAD,'run_id':43673862672,'local_lean_run':False,'kernel_verified':False,'independently_accepted':False,'resources_changed':False,'full_arithmetic_theorem_proved':False,'public_telescopes_changed':False,'modified_predecessor_modules':actual,'new_modules':[],'obligations':[{'id':i,'required_input':t,'constructed_input':note,'justification':'Exact unchanged original mathematical inputs and consumed objects; proof-only source normalization described in canonical contract. Hosted acceptance remains pending.','scope_modules':actual,'source_references':refs,'evidence':evidence} for i,t in zip(ids,texts)],'intake_sha256':h(dst/'intake.json'),'sources':{n:h(dst/n) for n in d['files']},'machine_contract_status':'DRAFT_REQUIRES_INDEPENDENT_PROPAGATION_REVIEW'}
 app['bindings']={str(p.relative_to(dst)):h(p) for p in dst.rglob('*') if p.is_file() and (p.parent!=dst or p.name in ['README.md','APPLICATION.md','COPY-BINDINGS.json'])};dump(dst/'APPLICATION.json',app)
 if not (OUT/old).exists():shutil.copytree(src,OUT/old)
 row={'predecessor':old,'successor':new,'changed':actual,'order_count':len(d['order']),'intake_sha256':h(dst/'intake.json'),'application_sha256':h(dst/'APPLICATION.json')};rows.append(row);print('PREPARED',new,flush=True)
dump(R/'SCALAR-SUCCESSOR-MAP-43673862672.json',{'base':HEAD,'mapping':{r['predecessor']:r['successor'] for r in rows},'packets':rows,'local_lean_run':False})
sys.path.insert(0,str(REPO/'scripts'));import check_progress_experiment as pe
plan=pe.ci.derive_plan()
for row in rows:pe.packet(row['successor'],plan,OUT);print('PACKET_SOURCE_PASS',row['successor'],flush=True)
