from pathlib import Path
import json,hashlib,sys,subprocess,shutil
r=Path(__file__).resolve().parents[1];b=r/'quartics/quartic-318-326/proof/experiments';o=b/'pel-original-cm-integral-order-rebuild-r1';p=b/'pel-original-cm-minkowski-bound-rebuild-r1'
sys.path.insert(0,str(r/'scripts'));import check_progress_lean as ci
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
def put(n,d):(p/n).write_text(json.dumps(d,indent=2)+'\n')
new=['PELOriginalCM210IntegralTraceMatrix318','PELOriginalCM210NativeDiscriminant318','PELOriginalCM210NativeSignature318','PELOriginalCM210MinkowskiBound318','PELOriginalCM210BoundedClassRepresentatives318']
(p/'README.md').write_text('''# Original CM210 native discriminant, signature and Minkowski bound

NEW reconstruction, not recovered old bytes. Five sources extend all 1,174 exact sources of integral-order-rebuild-r1. The SAME original quadratic carrier and the freshly constructed full native ring-of-integers equivalence are retained.

Compute the literal full integer-basis trace Gram matrix diag(2,-420), then transport its discriminant to NumberField.discr K=-840. Native rank-two and discriminant sign give zero real places and one complex place. Apply the native Minkowski class-representative theorem with these actual invariants: its bound is 2*sqrt(840)/pi < 19. Thus EVERY native ClassGroup O_K class has a nonzero integral ideal representative of norm at most 18.

This is a universal native representative bound, not a finite enumeration standing in for a proof. Classification of these ideals, production of eight distinct classes and full class-number exhaustion remain separate reconstruction work. No Hilbert class field, Artin reciprocity, CM residue-field or original/published model conclusion follows here. No local Lean build, profiling or resource-cap changes. Fresh independent review and hosted kernel replay are pending.
''')
(p/'DERIVATION.md').write_text('''# Full-order invariant and native bound chain

The preceding packet constructs the full native integer ring, not merely a quadratic suborder. Its ring equivalence is promoted to an integer algebra equivalence using map_intCast. The integral basis is the actual native QuadraticAlgebra basis, with both basis vectors explicitly unfolded in the matrix computations. Multiplication by r+s*theta has matrix [[r,-210s],[s,r]]. The native algebra trace is 2r. The trace Gram matrix of the full integer basis is diag(2,-420), determinant -840.

Map this basis along the actual full integer algebra equivalence. Native discriminant invariance under algebra equivalence and NumberField.discr_eq_discr identify the field discriminant with -840. This avoids assuming the order is maximal or inferring the field discriminant from an arbitrary rank-two lattice.

The actual quadratic algebra has native rational finrank two. The native relation r1+2r2=2 leaves r2=0 or1. NumberField.sign_discr rules out r2=0 because the already constructed field discriminant is negative. Therefore r2=1 and r1=0.

Substitute these actual values into NumberField.exists_ideal_in_class_of_norm_le. Its real bound simplifies to 2sqrt(840)/pi. The exact native sqrt identity gives sqrt(840)<29; Real.pi_gt_d2 gives pi>3.14, hence 2sqrt(840)<19pi. For each native class, the native theorem supplies an actual nonzero integral ideal I with norm at most that bound. Its natural norm is less than19, hence at most18. No enumeration of ideals or binary forms is used in this proof, and no class-group exhaustion is asserted.

The old lost native class-number eight chain is a reconstruction guide only. These five sources have new hashes and need fresh independent source review and hosted elaboration. The audit-repair investigation remains separate; no frozen inherited source is silently changed here.
''')
(p/'regress_cm_minkowski_rebuild.py').write_text('''from pathlib import Path
from fractions import Fraction as Q
import json
count=0
for r in range(-20,21):
 for s in range(-20,21):
  m=((r,-210*s),(s,r))
  assert m[0][0]+m[1][1]==2*r
  assert m[0][0]*m[1][1]-m[0][1]*m[1][0]==r*r+210*s*s
  count+=1
assert 2*(-420)==-840
sigs=[(a,b) for a in range(3) for b in range(2) if a+2*b==2 and (-1)**b==-1]
assert sigs==[(0,1)]
assert 840<29**2 and 2*29<19*Q(314,100)
assert all(n<=18 for n in range(100) if n<19)
# Negative controls: the nonmaximal scaled basis and wrong signature cannot be substituted.
assert 2*(-1680)!=-840
assert (-1)**0!= -1
out={'status':'PASS','exact_multiplication_trace_norm_cases':count,'trace_gram_determinant':-840,'signature_cases':6,'rational_bound_checks':2,'natural_rounding_cases':100,'negative_controls':2,'scope':'Exact regression, not Lean or class-group classification.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(out,indent=2)+'\\n');print(out)
''')
subprocess.run([sys.executable,str(p/'regress_cm_minkowski_rebuild.py')],check=True)
q=p/'MINKOWSKI-PRIMARY';shutil.copy2(o/'INTEGER-PRIMARY/QuadDefsRebuild.lean',q/'QuadDefsRebuild.lean')
put('PRIMARY-PROVENANCE.json',{'mathlib_commit':'56a005855ea17e0b0958f73ec801ae140b0a1679','native_files':{'NFDiscrRebuild.lean':'Mathlib/NumberTheory/NumberField/Discriminant/Defs.lean','AlgDiscrRebuild.lean':'Mathlib/RingTheory/Discriminant.lean','TraceRebuild.lean':'Mathlib/RingTheory/Trace/Defs.lean','NFInfiniteRebuild.lean':'Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean','DiscrSignRebuild.lean':'Mathlib/NumberTheory/NumberField/Discriminant/Basic.lean','ClassNumberRebuild.lean':'Mathlib/NumberTheory/NumberField/ClassNumber.lean','PiBoundsRebuild.lean':'Mathlib/Analysis/Real/Pi/Bounds.lean','ToLinRebuild.lean':'Mathlib/LinearAlgebra/Matrix/ToLin.lean','QuadDefsRebuild.lean':'Mathlib/Algebra/QuadraticAlgebra/Defs.lean'}})
d=json.loads((o/'intake.json').read_text());prior=d['order'];d.update(packet=p.name,revision_of=o.name,status='DRAFT_CM_NATIVE_MINKOWSKI_RECONSTRUCTION_REVIEW_PENDING',order=prior+new,new_modules=new,modified_predecessor_modules=[],revised_modules=[],changed_modules=new,exact_predecessor_modules=prior,unchanged_producer_modules=len(prior));d['files']={n+'.lean':{'sha256':sha(p/(n+'.lean')),'imports':sorted(ci.import_names((p/(n+'.lean')).read_text()))} for n in d['order']};put('intake.json',d)
c=[]
for n in prior:
 assert (p/(n+'.lean')).read_bytes()==(o/(n+'.lean')).read_bytes()
 c.append({'source':o.name+'/'+n+'.lean','consumer':n+'.lean','source_sha256':sha(o/(n+'.lean')),'consumer_sha256':sha(p/(n+'.lean')),'exact_copy':True})
put('COPY_BINDINGS.json',{'copies':c})
obs=[('source_hypotheses','Actual original quadratic field and full integer ring','Exact prior integerEquiv','No maximal-order assumption'),('constructed_objects','Native full basis, trace, discriminant, signature','Literal mapped quadratic basis and native invariants','No proxy basis discriminant'),('index_domain_coverage','Every native ideal class','Native exists_ideal_in_class_of_norm_le applied to arbitrary C','No enumeration substitute'),('transition_maps','R to full O_K','Exact integerAlgEquiv and basis.map','No changed carrier'),('limiting_object_identity','NumberField.discr K','Native discr_eq_discr and AlgEquiv transport','Full ring essential'),('coefficient_conventions','theta squared=-210','Matrix [[r,-210s],[s,r]], Gram diag(2,-420)','Signed discriminant -840'),('local_conditions','Signature and norm bound','Native sign_discr and rank relation, pi lower bound','All native hypotheses retained'),('exceptional_cases','Potential r2=0 and norm19','Negative discriminant excludes r2=0, strict bound excludes19','No approximate decimal numerical proof'),('downstream_consumption','Class-group exhaustion prerequisite','Actual nonzero ideal of norm at most18 in every class','Classification and reciprocity still absent')]
put('APPLICATION.json',{'packet':p.name,'producer':'advance_pel_identification','status':d['status'],'claim':'Actual original CM210 full integer-basis discriminant and signature, then native ideal-class representative norm bound18.','intake_sha256':sha(p/'intake.json'),'copy_bindings_sha256':sha(p/'COPY_BINDINGS.json'),'local_lean_run':False,'new_source_acceptance':False,'historical_bytes_recovered':False,'class_number_restored':False,'artin_reciprocity_proved':False,'sources':{n+'.lean':sha(p/(n+'.lean')) for n in d['order']},'bindings':{n:sha(p/n) for n in ['README.md','DERIVATION.md','intake.json','COPY_BINDINGS.json','PRIMARY-PROVENANCE.json','regress_cm_minkowski_rebuild.py','REGRESSION.json']},'primary_sources':{str(f.relative_to(p)):sha(f) for f in q.iterdir()},'obligations':[{'name':n,'required_input':a,'constructed_input':bb,'justification':c,'source_references':[x+'.lean' for x in new]+['DERIVATION.md'],'evidence':[x+'.lean' for x in new]+['DERIVATION.md']} for n,a,bb,c in obs]})
print('APP',sha(p/'APPLICATION.json'));print('INTAKE',sha(p/'intake.json'));print('NEWLINES',sum(len((p/(n+'.lean')).read_text().splitlines()) for n in new))
import check_progress_experiment as ce
_,diag,_,_=ce.packet(p.name,ci.derive_plan(early_depth=7));print('STATIC PASS',len(diag['order']))
