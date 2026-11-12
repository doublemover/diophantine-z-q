from pathlib import Path
import json,hashlib,shutil,sys
r=Path(__file__).resolve().parents[1];proof=r/'quartics/quartic-318-326/proof';b=proof/'experiments';repair=proof/'recovery/pel-audit-repairs-20261112'
sys.path.insert(0,str(r/'scripts'));import check_progress_lean as ci;import check_progress_experiment as ce
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[('pel-original-cm-integral-order-rebuild-r1','pel-original-cm-integral-order-rebuild-r2'),('pel-original-cm-minkowski-bound-rebuild-r1','pel-original-cm-minkowski-bound-rebuild-r2')]
for old,new in rows:
 o=b/old;p=b/new
 if p.exists():raise RuntimeError('Refuse existing '+new)
 shutil.copytree(o,p)
 d=json.loads((o/'intake.json').read_text());prior=d['order'];changed=[];exact=[]
 for n in prior:
  if (repair/'after'/(n+'.lean')).exists():
   assert (o/(n+'.lean')).read_bytes()==(repair/'before'/(n+'.lean')).read_bytes(),(old,n)
   shutil.copy2(repair/'after'/(n+'.lean'),p/(n+'.lean'));changed.append(n)
  else:exact.append(n)
 q=p/'AUDIT-20261112';shutil.copytree(repair,q)
 review=proof/'independent-reviews/resume-20261112/pel-audit-three-repairs-review.json';shutil.copy2(review,q/review.name)
 def put(n,v):(p/n).write_text(json.dumps(v,indent=2)+'\n')
 d.update(packet=new,revision_of=old,status='BOUNDED_FULL_LOG_AUDIT_REPAIR_SOURCE_REVIEWED_KERNEL_PENDING',new_modules=[],modified_predecessor_modules=changed,revised_modules=changed,changed_modules=changed,exact_predecessor_modules=exact,unchanged_producer_modules=len(exact))
 d['files']={n+'.lean':{'sha256':sha(p/(n+'.lean')),'imports':sorted(ci.import_names((p/(n+'.lean')).read_text()))} for n in prior};put('intake.json',d)
 (p/'README.md').write_text(f'''# Bounded full-log PEL audit successor\n\nPredecessor: {old}. Same {len(prior)}-module closure, no new mathematical claim, lane, resource cap, or local Lean run. Exactly {len(changed)} reviewed source repairs: {', '.join(changed)}. All other {len(exact)} predecessor source files are byte-exact. Frozen predecessor remains untouched.\n\nFull uploaded audit logs, before/after files, exact patches, native evidence and distinct source review are copied under AUDIT-20261112. The source review covers these deltas, not kernel acceptance or all downstream elaboration. Quotient mk' normalization, explicit finite-atlas projection typing and intended hb binder, and Hermitian scalar/component/goal-closure proofs preserve mathematical statements and intended existing callers. See copied README for exact diagnostic correspondence and the corrected second Hermitian branch.\n\nThis bounded successor does not confer acceptance on new reconstruction packets or transfer historical kernel status. Hosted replay is pending. No original numerical j, class-number or reciprocity claim is added.\n''')
 copies=[]
 for n in prior:
  isexact=(p/(n+'.lean')).read_bytes()==(o/(n+'.lean')).read_bytes();assert isexact==(n in exact)
  copies.append({'source':old+'/'+n+'.lean','consumer':n+'.lean','source_sha256':sha(o/(n+'.lean')),'consumer_sha256':sha(p/(n+'.lean')),'exact_copy':isexact,'bounded_reviewed_repair':n in changed})
 put('COPY_BINDINGS.json',{'copies':copies,'review_sha256':sha(review)})
 obs=[('source_hypotheses','Actual uploaded failed goals','Full raw logs and exact audited source bytes','No omitted diagnostics guessed'),('constructed_objects','Same declarations and carriers','Only specified proof normalization and intended binder','No new object substitution'),('index_domain_coverage','Same prior closure','Exact unchanged ordered source list','No source omitted'),('transition_maps','Existing callers and maps','hb already explicitly supplied by callers','No new downstream assumption'),('limiting_object_identity','Same quotient/atlas/Hermitian form','Definition bodies outside repairs unchanged','No mathematical conclusion strengthened'),('coefficient_conventions','Original real/complex scalars','Typed projection and native I squared identity','No transported scalar structure'),('local_conditions','Actual branch injectivity and all components','Restore hb and explicit component rewrites','Root binder issue not hidden'),('exceptional_cases','Rewrites may close goals','Both Hermitian branches use robust sequencing','Exact observed second-branch failure fixed'),('downstream_consumption','Same original audit lane','Bounded successor ready for hosted replay','Source acceptance does not imply kernel success')]
 put('APPLICATION.json',{'packet':new,'producer':'advance_pel_identification','status':d['status'],'claim':'Bounded reviewed proof repairs matching complete uploaded audit diagnostics; same mathematical closure.','intake_sha256':sha(p/'intake.json'),'copy_bindings_sha256':sha(p/'COPY_BINDINGS.json'),'local_lean_run':False,'kernel_verified':False,'resources_changed':False,'new_modules':[],'modified_predecessor_modules':changed,'sources':{n+'.lean':sha(p/(n+'.lean')) for n in prior},'bindings':{n:sha(p/n) for n in ['README.md','intake.json','COPY_BINDINGS.json']},'primary_sources':{str(f.relative_to(p)):sha(f) for f in q.rglob('*') if f.is_file()},'obligations':[{'name':n,'required_input':a,'constructed_input':bb,'justification':c,'source_references':[x+'.lean' for x in changed]+['AUDIT-20261112/README.md'],'evidence':[x+'.lean' for x in changed]+['AUDIT-20261112/README.md']} for n,a,bb,c in obs]})
 _,diag,_,_=ce.packet(new,ci.derive_plan(early_depth=7));print(new,'STATIC',len(diag['order']),'EXACT',len(exact),'APP',sha(p/'APPLICATION.json'),'INTAKE',sha(p/'intake.json'))
