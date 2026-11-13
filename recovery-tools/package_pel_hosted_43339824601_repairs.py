from pathlib import Path
import json,hashlib,shutil,sys
r=Path(__file__).resolve().parents[1];proof=r/'quartics/quartic-318-326/proof';b=proof/'experiments';repair=proof/'recovery/pel-hosted-43339824601-repairs'
sys.path.insert(0,str(r/'scripts'));import check_progress_lean as ci;import check_progress_experiment as ce
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[('pel-original-zero-local-length-r29','pel-original-zero-local-length-r30'),('pel-original-cotangent-hzero-forty-r35','pel-original-cotangent-hzero-forty-r36'),('pel-original-torsion-towers-r9','pel-original-torsion-towers-r10'),('height-original-normal-infinity-trace-r2','height-original-normal-infinity-trace-r3'),('pel-original-character-ordered-biholomorph-r2','pel-original-character-ordered-biholomorph-r3')]
summary=[]
for old,new in rows:
 o=b/old;p=b/new
 if p.exists():raise RuntimeError('Refuse existing '+new)
 shutil.copytree(o,p)
 d=json.loads((o/'intake.json').read_text());prior=d['order'];changed=[];exact=[]
 for n in prior:
  after=repair/'after'/(n+'.lean')
  if after.exists():
   assert (o/(n+'.lean')).read_bytes()==(repair/'before'/(n+'.lean')).read_bytes(),(old,n)
   shutil.copy2(after,p/(n+'.lean'));changed.append(n)
  else:exact.append(n)
 q=p/'HOSTED-43339824601';shutil.copytree(repair,q)
 def put(n,v):(p/n).write_text(json.dumps(v,indent=2)+'\n')
 d.update(packet=new,revision_of=old,status='BOUNDED_HOSTED_SOURCE_REPAIR_PENDING_REVIEW_AND_KERNEL',new_modules=[],modified_predecessor_modules=changed,revised_modules=changed,changed_modules=changed,exact_predecessor_modules=exact,unchanged_producer_modules=len(exact))
 d['files']={n+'.lean':{'sha256':sha(p/(n+'.lean')),'imports':sorted(ci.import_names((p/(n+'.lean')).read_text()))} for n in prior};put('intake.json',d)
 (p/'README.md').write_text(f'''# Bounded successor for hosted run 43339824601\n\nFrozen predecessor: {old}. Same {len(prior)}-module ordered closure. Exactly {len(changed)} source repairs: {', '.join(changed)}. The other {len(exact)} modules are byte-identical. No new mathematical claim, lane, resource setting or local Lean execution.\n\nHOSTED-43339824601 contains full diagnostics, complete before/after sources, patches, evidence pins and explanation. The deltas make the existing complex projection types explicit, push integer-negation casts in the semicharacter goal, and expose killed-by-3 membership equations in the same original torsion subgroup. No statement, carrier, quantifier or map changes.\n\nDistinct source review and GitHub replay are pending. The failed torsion definition's downstream metavariable errors are preserved rather than claimed separately resolved. Frozen predecessors and separately reviewed CM reconstruction packets remain unchanged.\n''')
 copies=[]
 for n in prior:
  isexact=(p/(n+'.lean')).read_bytes()==(o/(n+'.lean')).read_bytes();assert isexact==(n in exact)
  copies.append({'source':old+'/'+n+'.lean','consumer':n+'.lean','source_sha256':sha(o/(n+'.lean')),'consumer_sha256':sha(p/(n+'.lean')),'exact_copy':isexact,'bounded_source_repair':n in changed})
 put('COPY_BINDINGS.json',{'copies':copies})
 evidence={str(f.relative_to(p)):sha(f) for f in q.rglob('*') if f.is_file()}
 obs=[('source_hypotheses','Actual hosted failing terms and full Lean diagnostics','Complete logs and exact before sources preserved','No error inferred from summaries alone'),('constructed_objects','Same analytic projection, quadratic refinement and original torsion subgroup','Only type annotations, cast normalization and definitional membership exposure','No mathematical object changed'),('index_domain_coverage','All original module indices and every original hypothesis','Ordered closure retained and every unchanged source compared','No source dropped or skipped'),('transition_maps','Complex projection composition, integer-to-complex cast and torsion subgroup inclusion','The same maps are elaborated explicitly','No added input assumption or alternative scalar action'),('limiting_object_identity','The function q -> q.2 k, same integralForm and same Torus','Declaration statements and definition carriers unchanged','Proof repair rather than numerical substitute'),('coefficient_conventions','Complex scalars and the integer sign in phase_add; integer 3 scalar in torsion','Explicit CLM and snd types, push_cast at goal, typed 3-smul change','No sign or finite-field convention changed'),('local_conditions','Existing denominator/root hypotheses and h_tau unchanged','No local hypothesis is weakened or invented','Only already available exact equations are exposed'),('exceptional_cases','Full subgroup closure and downstream failure cascade','Both add and neg closure fixed; all cascade diagnostics retained','No claim of successful downstream replay'),('downstream_consumption','Five active hosted closures consuming these declarations','Only present repair modules changed in each successor','GitHub Lean replay remains required; no local build')]
 put('APPLICATION.json',{'packet':new,'producer':'/root/pel_restart','status':d['status'],'claim':'Bounded proof repairs from full hosted diagnostics with unchanged mathematical declarations.','run_id':43339824601,'intake_sha256':sha(p/'intake.json'),'copy_bindings_sha256':sha(p/'COPY_BINDINGS.json'),'local_lean_run':False,'kernel_verified':False,'resources_changed':False,'new_modules':[],'modified_predecessor_modules':changed,'sources':{n+'.lean':sha(p/(n+'.lean')) for n in prior},'bindings':dict({n:sha(p/n) for n in ['README.md','intake.json','COPY_BINDINGS.json']},**evidence),'primary_sources':evidence,'obligations':[{'name':n,'required_input':a,'constructed_input':bb,'justification':c,'source_references':[x+'.lean' for x in changed]+['HOSTED-43339824601/README.md'],'evidence':[x+'.lean' for x in changed]+['HOSTED-43339824601/README.md']} for n,a,bb,c in obs]})
 _,diag,_,_=ce.packet(new,ci.derive_plan(early_depth=7))
 row={'packet':new,'predecessor':old,'structural_modules':len(diag['order']),'exact_modules':len(exact),'changed_modules':changed,'application_sha256':sha(p/'APPLICATION.json'),'intake_sha256':sha(p/'intake.json')};summary.append(row);print(json.dumps(row))
(proof/'recovery/pel-hosted-43339824601-repair-packets.json').write_text(json.dumps(summary,indent=2)+'\n')
