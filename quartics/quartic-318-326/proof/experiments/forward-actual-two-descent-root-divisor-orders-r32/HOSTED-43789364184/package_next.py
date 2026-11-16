from pathlib import Path
import json,hashlib,shutil,subprocess
B=Path(__file__).resolve().parent;W=B.parent;C=B/'canonical';OUT=B/'packets';R=W/'resume-next-43723785714-repo';EX=R/'quartics/quartic-318-326/proof/experiments';HOST=W/'resume-next-43740410608/hosted-43789364184';HEAD='960090b9a5b895bc9350511ea373ed42bfeb475d';OWN='fa27b931b23aadbc02620bf23629777cc458219f';RUN=43789364184
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,d):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2)+'\n')
# Integration may publish independent lanes; bound source/intake commits are checked below.
texts=[(x['id'],x['statement']) for x in json.loads((C/'APPLICATION.json').read_text())['obligations']]
M={'forward-actual-two-descent-root-divisor-orders-r31':('forward-actual-two-descent-root-divisor-orders-r32','AnchorLocalSquareProduction318'),'forward-original-weighted-weyl-r22-replay-r31':('forward-original-weighted-weyl-r22-replay-r32','AnchorLocalSquareProduction318')}
rows=[];OUT.mkdir(exist_ok=True)
for old,(new,mod) in M.items():
 src=EX/old;dst=OUT/new;own=HOST/('experiment-'+old)/'progress-experiments'/old
 assert not dst.exists();d=json.loads((src/'intake.json').read_text());result=json.loads((own/'RESULT.json').read_text());assert result['packet_sha256']==H(src/'intake.json');assert result['commands'][-1]['module']==mod and result['commands'][-1]['exit_code']!=0
 assert H(src/(mod+'.lean'))==H(C/'before'/(mod+'.lean'))
 assert subprocess.check_output(['git','show',OWN+':'+str((src/(mod+'.lean')).relative_to(R))],cwd=R)==(src/(mod+'.lean')).read_bytes()
 for n,row in d['files'].items():assert H(src/n)==row['sha256']
 shutil.copytree(src,dst);ev=dst/f'HOSTED-{RUN}';ev.mkdir();meta=ev/'PREDECESSOR-METADATA';meta.mkdir()
 for p in list(dst.iterdir()):
  if p.is_file() and p.suffix!='.lean':
   shutil.copy2(p,meta/p.name);assert H(p)==H(meta/p.name)
   if p.name not in ['intake.json','APPLICATION.json','APPLICATION.md','README.md','COPY-BINDINGS.json']:p.unlink()
 shutil.copytree(own,ev/'own-hosted');shutil.copytree(C,ev/'canonical');shutil.copy2(Path(__file__),ev/'package_next.py');shutil.copy2(W/'resume-independent-review/ANCHOR-LOCAL-SQUARE-43789364184-SOURCE-REVIEW.json',ev/'SOURCE-REVIEW.json');shutil.copy2(C/'after'/(mod+'.lean'),dst/(mod+'.lean'))
 actual=[mod];unchanged=[n for n in d['order'] if n!=mod]
 d.update(packet=new,status='DRAFT_SOURCE_REPAIR_HOSTED_PENDING',scope='OBSERVED_HOSTED_ORIGINAL_SOURCE_REPAIR',revision_classification_schema=1,revision_of=old,new_modules=[],changed_modules=actual,revised_modules=actual,modified_predecessor_modules=actual,observed_failure_repair_modules=actual,preventive_unreached_modules=[])
 if 'revision_source' in d:d['revision_source']=old
 for k in ['exact_predecessor_modules','unchanged_predecessor_modules','reused_modules','unchanged_upstream_modules','unchanged_producer_modules']:
  if k in d:d[k]=unchanged if isinstance(d[k],list) else len(unchanged)
 for n,row in d['files'].items():row['sha256']=H(dst/n)
 dump(dst/'intake.json',d)
 passed=sum(x['exit_code']==0 for x in result['commands']);unreached=len(d['order'])-passed-1
 detail=f'Own {old} at {OWN}, run{RUN}; unchanged predecessor source reconciled to integration base {HEAD}: {passed} full draft modules pass, {mod} fails after {result["commands"][-1]["seconds"]} seconds; {unreached} roots unreached. New candidate {new} changes exactly {mod}, preserves {len(unchanged)} other root files and all {len(d["order"])} ordered roots. No candidate compilation or whole-packet acceptance is claimed.'
 (dst/'README.md').write_text(f'# {new}\n\n{detail}\n\nAll legacy root metadata is byte-preserved under HOSTED-{RUN}/PREDECESSOR-METADATA; current source and receipt classifications below replace its historical status only in this new successor. No old packet changes.\n')
 current=list(texts);current[-1]=(current[-1][0],current[-1][1]+' '+detail)
 (dst/'APPLICATION.md').write_text('# Current nine-clause application contract\n\n'+''.join(f'{i+1}. {t}\n\n' for i,(_,t) in enumerate(current)))
 dump(dst/'COPY-BINDINGS.json',{'predecessor':old,'successor':new,'changed_module':mod,'before_sha256':H(src/(mod+'.lean')),'after_sha256':H(dst/(mod+'.lean')),'unchanged_count':len(unchanged),'full_order_count':len(d['order']),'own_result_sha256':H(own/'RESULT.json'),'own_predecessor_intake_sha256':H(src/'intake.json'),'resources_changed':False,'public_telescopes_changed':False,'expose_attributes_added': ['monomialUnit','transitionUnit'] if mod.startswith('Contact') else []})
 refs=[mod+'.lean',f'HOSTED-{RUN}/canonical/before/{mod}.lean'];evidence=['README.md','APPLICATION.md','COPY-BINDINGS.json',f'HOSTED-{RUN}/own-hosted/RESULT.json',f'HOSTED-{RUN}/canonical/APPLICATION.md']
 app={'packet':new,'predecessor':old,'status':'DRAFT_SOURCE_REPAIR_HOSTED_PENDING','source_commit':HEAD,'integration_base_commit':HEAD,'own_receipt_head':OWN,'run_id':RUN,'local_lean_run':False,'kernel_verified':False,'independently_accepted':False,'resources_changed':False,'full_arithmetic_theorem_proved':False,'public_telescopes_changed':False,'modified_predecessor_modules':actual,'new_modules':[],'observed_failure_repair_modules':actual,'preventive_unreached_modules':[],'own_predecessor_passed_draft_count':passed,'own_predecessor_failed_module':mod,'own_predecessor_unreached_draft_roots':unreached,'obligations':[{'id':i,'required_input':t,'constructed_input':t,'justification':'Exact before/after and native primary interfaces bound below; scoped candidate only. '+detail,'scope_modules':actual,'source_references':refs,'evidence':evidence} for i,t in current],'intake_sha256':H(dst/'intake.json'),'sources':{n:H(dst/n) for n in d['files']},'machine_contract_status':'DRAFT_REQUIRES_INDEPENDENT_SOURCE_AND_PROPAGATION_REVIEW'}
 app['bindings']={str(p.relative_to(dst)):H(p) for p in dst.rglob('*') if p.is_file() and (p.parent!=dst or p.name in ['README.md','APPLICATION.md','COPY-BINDINGS.json'])};dump(dst/'APPLICATION.json',app)
 rows.append({'old':old,'new':new,'source':str(dst),'intake_sha256':H(dst/'intake.json'),'application_sha256':H(dst/'APPLICATION.json'),'roots':len(d['order']),'changed':actual,'source_review_pending':False});print('PREPARED',new,'bindings',len(app['bindings']),flush=True)
dump(B/'PROPOSED.json',rows)
