from pathlib import Path
import json,hashlib,shutil,subprocess
B=Path(__file__).resolve().parent;W=B.parent;C=B/'canonical';OUT=B/'packets';R=W/'resume-next-43723785714-repo';EX=R/'quartics/quartic-318-326/proof/experiments';INV=W/'resume-inventory-context-after-83fde/inventory-43818205337';HEAD='e51d8760f82415364f83792071135dfb71d3b462';OWN='15d7899cfa9bfa318f9a0ef1a399c1e24a5b0bc3';RUN=43818205337;MOD='Source150CRTWitness318'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,d):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2)+'\n')
texts=[(x['id'],x['statement']) for x in json.loads((C/'APPLICATION.json').read_text())['obligations']]
M={'forward-original-weighted-weyl-r22-replay-r34':'forward-original-weighted-weyl-r22-replay-r35','forward-actual-two-descent-root-divisor-orders-r34':'forward-actual-two-descent-root-divisor-orders-r35'}
rows=[];OUT.mkdir(exist_ok=True)
for old,new in M.items():
 src=EX/old;dst=OUT/new;own=INV/('inventory-'+old);assert not dst.exists();d=json.loads((src/'intake.json').read_text());result=json.loads((own/'INVENTORY.json').read_text());observed=result['modules'][MOD]
 assert result['packet_sha256']==H(src/'intake.json') and observed['status']=='compiler_error' and observed['exit_code']==1
 assert observed['source_sha256']==H(src/(MOD+'.lean'))==H(C/'before'/(MOD+'.lean'))
 for commit in [OWN,HEAD]:
  for n in ['intake.json',MOD+'.lean']:assert subprocess.check_output(['git','show',commit+':'+str((src/n).relative_to(R))],cwd=R)==(src/n).read_bytes()
 for n,row in d['files'].items():assert H(src/n)==row['sha256']
 shutil.copytree(src,dst);ev=dst/f'INVENTORY-{RUN}';ev.mkdir();meta=ev/'PREDECESSOR-METADATA';meta.mkdir()
 for p in list(dst.iterdir()):
  if p.is_file() and p.suffix!='.lean':
   shutil.copy2(p,meta/p.name);assert H(p)==H(meta/p.name)
   if p.name not in ['intake.json','APPLICATION.json','APPLICATION.md','README.md','COPY-BINDINGS.json']:p.unlink()
 shutil.copytree(own,ev/'own-inventory');shutil.copytree(C,ev/'canonical');shutil.copy2(Path(__file__),ev/'package_next.py');shutil.copy2(W/'resume-independent-review/SOURCE150-43818205337-PROBE-SOURCE-REVIEW.json',ev/'SOURCE-REVIEW.json');shutil.copy2(C/'after'/(MOD+'.lean'),dst/(MOD+'.lean'))
 changed=[MOD];unchanged=[n for n in d['order'] if n!=MOD]
 d.update(packet=new,status='DRAFT_SOURCE_REPAIR_HOSTED_PENDING',scope='OBSERVED_INVENTORY_ORIGINAL_SOURCE_REPAIR',revision_classification_schema=1,revision_of=old,new_modules=[],changed_modules=changed,revised_modules=changed,modified_predecessor_modules=changed,observed_failure_repair_modules=changed,preventive_unreached_modules=[],observed_failure_modules=changed,observed_failed_root_delta_modules=changed,changed_producer_modules=changed,mathematical_repair_modules=changed,preventive_unobserved_modules=[],experiment_purpose='Repair separately observed Source150CRTWitness318 inventory compiler error only; PreparedAnchorSource318 production failure unchanged; no candidate acceptance')
 if 'revision_source' in d:d['revision_source']=old
 for k in ['exact_predecessor_modules','unchanged_predecessor_modules','reused_modules','unchanged_upstream_modules','unchanged_producer_modules']:
  if k in d:d[k]=unchanged if isinstance(d[k],list) else len(unchanged)
 for n,row in d['files'].items():row['sha256']=H(dst/n)
 dump(dst/'intake.json',d)
 counts=result['counts'];detail=f'Own {old} dependency-ready inventory run {RUN} at marker {HEAD}, requested immutable source {OWN}: {counts["compile_pass"]} compile_pass, {counts["compiler_error"]} compiler_error, {counts["blocked_by_import"]} blocked_by_import. Observed {MOD} fails after {observed["seconds"]} seconds. Successful-subset audit passes on 117 modules/4188 declarations only. Separate production run43817651313 still stops at PreparedAnchorSource318, which is unchanged here. Candidate {new} changes exactly {MOD}, preserves {len(unchanged)} other root sources/all {len(d["order"])} ordered roots. No candidate compilation or whole-packet acceptance claimed.'
 (dst/'README.md').write_text(f'# {new}\n\n{detail}\n\nAll prior root metadata and complete historical evidence are preserved byte-for-byte. This is an observed inventory error repair, not a preventive/unreached edit and not a production pass.\n')
 current=list(texts);current[-1]=(current[-1][0],current[-1][1]+' '+detail)
 (dst/'APPLICATION.md').write_text('# Current nine-clause application contract\n\n'+''.join(f'{i+1}. {t}\n\n' for i,(_,t) in enumerate(current)))
 dump(dst/'COPY-BINDINGS.json',{'predecessor':old,'successor':new,'changed_module':MOD,'before_sha256':H(src/(MOD+'.lean')),'after_sha256':H(dst/(MOD+'.lean')),'unchanged_count':len(unchanged),'full_order_count':len(d['order']),'own_inventory_sha256':H(own/'INVENTORY.json'),'own_predecessor_intake_sha256':H(src/'intake.json'),'own_inventory_head':HEAD,'own_source_commit':OWN,'resources_changed':False,'public_telescopes_changed':False,'prepared_anchor_unchanged':H(src/'PreparedAnchorSource318.lean')==H(dst/'PreparedAnchorSource318.lean')})
 refs=[MOD+'.lean',f'INVENTORY-{RUN}/canonical/before/{MOD}.lean'];evidence=['README.md','APPLICATION.md','COPY-BINDINGS.json',f'INVENTORY-{RUN}/own-inventory/INVENTORY.json',f'INVENTORY-{RUN}/canonical/APPLICATION.md']
 app={'packet':new,'predecessor':old,'status':'DRAFT_SOURCE_REPAIR_HOSTED_PENDING','source_commit':HEAD,'integration_base_commit':HEAD,'own_source_commit':OWN,'own_inventory_head':HEAD,'run_id':RUN,'evidence_kind':'DEPENDENCY_READY_INVENTORY_NOT_PRODUCTION_ACCEPTANCE','local_lean_run':False,'kernel_verified':False,'independently_accepted':False,'resources_changed':False,'full_arithmetic_theorem_proved':False,'public_telescopes_changed':False,'modified_predecessor_modules':changed,'new_modules':[],'observed_failure_repair_modules':changed,'preventive_unreached_modules':[],'own_inventory_counts':counts,'own_inventory_observed_failed_module':MOD,'own_successful_subset_audit':{'modules':117,'declarations':4188,'status':'audit_pass'},'production_unresolved_module':'PreparedAnchorSource318','obligations':[{'id':i,'required_input':t,'constructed_input':t,'justification':'Exact before/after and native primary interfaces bound below; scoped candidate only. '+detail,'scope_modules':changed,'source_references':refs,'evidence':evidence} for i,t in current],'intake_sha256':H(dst/'intake.json'),'sources':{n:H(dst/n) for n in d['files']},'machine_contract_status':'DRAFT_REQUIRES_INDEPENDENT_SOURCE_AND_PROPAGATION_REVIEW'}
 app['bindings']={str(p.relative_to(dst)):H(p) for p in dst.rglob('*') if p.is_file() and (p.parent!=dst or p.name in ['README.md','APPLICATION.md','COPY-BINDINGS.json'])};dump(dst/'APPLICATION.json',app)
 rows.append({'old':old,'new':new,'source':str(dst),'intake_sha256':H(dst/'intake.json'),'application_sha256':H(dst/'APPLICATION.json'),'roots':len(d['order']),'changed':changed,'source_review_pending':False,'evidence_kind':'DEPENDENCY_READY_INVENTORY_NOT_PRODUCTION_ACCEPTANCE'});print('PREPARED',new,'bindings',len(app['bindings']),flush=True)
dump(B/'PROPOSED.json',rows)
