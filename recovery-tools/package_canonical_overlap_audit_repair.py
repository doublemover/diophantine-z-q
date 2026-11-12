from pathlib import Path
import hashlib,json,shutil,sys
repo=Path(__file__).resolve().parents[1];proof=repo/'quartics/quartic-318-326/proof';base=proof/'experiments'
sys.path.insert(0,str(repo/'scripts'));import check_progress_lean as ci;import check_progress_experiment as ce
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old='contact-relative-site-descent-r71';new='contact-relative-site-descent-r72';src=base/old;dst=base/new
if dst.exists():raise RuntimeError('Refuse overwrite: '+new)
shutil.copytree(src,dst)
candidate=repo/'build/audit-repairs-20261112/actual-canonical-overlap';name='ActualCanonicalOverlap318.lean'
assert sha(src/name)==sha(candidate/'ActualCanonicalOverlap318.before.lean')
shutil.copy2(candidate/name,dst/name)
evidence=dst/'AUDIT-REPAIR';shutil.copytree(candidate,evidence)
review=proof/'independent-reviews/resume-20261112/actual-canonical-overlap-repair-review.json';shutil.copy2(review,evidence/review.name)
d=json.loads((src/'intake.json').read_text());order=d['order'];exact=[]
for n in order:
 if n+'.lean'!=name:assert (src/(n+'.lean')).read_bytes()==(dst/(n+'.lean')).read_bytes();exact.append(n)
d.update(packet=new,revision_of=old,status='BOUNDED_SOURCE_REPAIR_REVIEWED_KERNEL_PENDING',new_modules=[],changed_modules=[name[:-5]],unchanged_producer_modules=exact)
d['files']={n+'.lean':{'sha256':sha(dst/(n+'.lean')),'imports':sorted(ci.import_names((dst/(n+'.lean')).read_text()))} for n in order}
(dst/'intake.json').write_text(json.dumps(d,indent=2)+'\n')
(dst/'SOURCE_SHA256SUMS').write_text(''.join(sha(dst/(n+'.lean'))+'  '+n+'.lean\n' for n in order))
(dst/'README.md').write_text(f'''# Actual canonical overlap: bounded audit repair

This is a successor of {old}, retaining its entire {len(order)}-module closure. Exactly one source is changed: the actual canonical overlap theorem now normalizes abstract affine paths before substituting the large original nerve. The final theorem uses the unchanged generic canonical transport and an exact transitivity step instead of broad concrete simplification.

The original public statement, scheme maps, line objects, imports and all resource settings are unchanged. {len(exact)} predecessor Lean sources remain byte-exact. The frozen predecessor is untouched. Full source before/after, patch and independent scoped source review are under AUDIT-REPAIR.

This addresses the reported kernel deterministic timeout structurally. It does NOT establish that replay succeeds or that runtime has improved: no Lean was run. Downstream errors remain possible. Historical metadata copied from the predecessor is background, not a new acceptance claim. The current intake and APPLICATION are authoritative for this candidate.
''')
(dst/'COPY_BINDINGS.json').write_text(json.dumps({'predecessor':old,'exact_sources':exact,'changed_sources':{name:{'before':sha(src/name),'after':sha(dst/name)}},'review_sha256':sha(review)},indent=2)+'\n')
keys=['hypotheses','objects','coverage','transitions','identity','coefficients','local_conditions','exceptional_cases','downstream']
app={'packet':new,'status':'BOUNDED_SOURCE_REPAIR_REVIEWED_KERNEL_PENDING','revision_of':old,'claim':'Same actual canonical overlap theorem, factored through an abstract affine path bridge.','local_lean_run':False,'kernel_verified':False,'resource_changes':False,'new_modules':[],'changed_modules':[name[:-5]],'intake_sha256':sha(dst/'intake.json'),'sources':{n+'.lean':sha(dst/(n+'.lean')) for n in order},'obligations':[{'name':k,'source_references':[name],'evidence':['README.md','AUDIT-REPAIR/REPAIR.json'],'justification':'Exact bounded source delta and original actual maps retained; no measured replay result claimed.'} for k in keys]}
app['bindings']={str(f.relative_to(dst)):sha(f) for f in dst.rglob('*') if f.is_file() and f.name!='APPLICATION.json'}
(dst/'APPLICATION.json').write_text(json.dumps(app,indent=2)+'\n')
_,checked,_,_=ce.packet(new,ci.derive_plan(early_depth=7))
print(new,'structural',len(checked['order']),'exact',len(exact),'APP',sha(dst/'APPLICATION.json'),'intake',sha(dst/'intake.json'))
