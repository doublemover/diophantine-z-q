from pathlib import Path
import json,hashlib,sys,shutil,subprocess
r=Path(__file__).resolve().parents[1]; b=r/'quartics/quartic-318-326/proof/experiments';o=b/'pel-original-character-ordered-biholomorph-r1';p=b/'pel-original-cm-integral-order-rebuild-r1'
sys.path.insert(0,str(r/'scripts'));import check_progress_lean as ci
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
def put(n,d):(p/n).write_text(json.dumps(d,indent=2)+'\n')
new=['PELOriginalCM210IntegralConjugation318','PELOriginalCM210IntegralTraceData318','PELOriginalCM210DenominatorCongruences318','PELOriginalCM210FullIntegralCoordinates318','PELOriginalCM210NativeIntegerOrder318']
(p/'README.md').write_text('''# Reconstruct the full original CM210 integer order

This is a NEW reconstruction checkpoint on the actual surviving branch at d44cf363, not recovery of the lost old packet bytes. Five modules extend the exact1169-source ordered-biholomorph predecessor. The source uses the SAME original PELInertiaQuadraticEmbeddings.Quadratic4, with its unchanged map to the original quaternion algebra and unchanged inertia element.

Construct R=Z[sqrt(-210)] and its injective coordinate map into the actual K. For every algebraic integer z in K, the existing native quadratic trace and norm results supply T=2re(z), U=420im(z), N=re(z)^2+210im(z)^2, with210T^2+U^2=840N. Complete native finite congruence checks at8,3,5,7 prove2 divides T and420 divides U. Thus every algebraic integer has integer coordinates, giving a bijective ring map R to the FULL native RingOfIntegers K. The same original quaternion realization is retained explicitly for every integer.

This restores the full-integer-order prerequisite only. It does not restore or assume the later native discriminant, class-number8, radical tower, unramifiedness, Hilbert maximality, Artin reciprocity or CM residue-field theorem. Earlier retained proof notes guide reconstruction but do not certify these new bytes. New independent review and hosted Lean replay remain separate.

No local Lean build, profiling, resource-cap changes or new dependency installation.
''')
(p/'DERIVATION.md').write_text('''# Exact original carrier and universal integral closure

The surviving original quadratic embedding has literal carrier QuadraticAlgebra Q (-(discriminant4))0, discriminant4=210, and sends omega to the unchanged original quaternion element. Its actual negativity supplies the field structure. R is the integral quadratic algebra with parameter-210. Native mapRingHom casts each coordinate; its injectivity is checked on the two projections. Every R element is integral because the integral quadratic algebra is a finite free Z-module.

Reuse the SURVIVING PELQuadraticIntegralInvariants.trace_integral and norm_integral, whose proofs apply conjugation inside a genuinely commutative quadratic carrier and reflect scalar integrality through an injective algebra map. The trace of omega*z is-420im(z); negating its integer gives U=420im(z). The exact norm formula gives N. Direct rational polynomial normalization yields210T^2+U^2=840N, then exact integer casting yields the integer identity.

Reduce the identity modulo8. The complete64-case ZMod8 lemma gives the actual reductions of T modulo2 and U modulo4 by native castHom maps. Reduce modulo3,5,7: complete finite quadratic-zero checks force each prime to divide U. Use the actual Bezout identities4-3=1, -2*12+5*5=1, and2*60-17*7=1 to combine the divisibilities into420|U. No bounded search over algebraic integers substitutes for this universal argument.

Write T=2r,U=420s with integer r,s and use exact rational equalities to recover re(z)=r,im(z)=s. This proves the reverse direction of full integral closure. Package the literal coordinate map into RingOfIntegers K and use its proved bijectivity to construct the native ring equivalence. All downstream maps retain the SAME original quaternion realization; no abstract quadratic copy is substituted.

History: a related full-integer-order checkpoint was independently source-reviewed before the workspace loss. Those original five source files were not recovered. This route is newly reconstructed from actual surviving originals and exact pinned Mathlib APIs, so the old acceptance hash is not reused. The full class group and candidate unramified extension still require reconstruction in dependency order.
''')
(p/'regress_cm_integral_rebuild.py').write_text('''from pathlib import Path
from fractions import Fraction as Q
from itertools import product
import json
finite=0
for t,u in product(range(8),repeat=2):
 if (210*t*t+u*u)%8==0:assert t%2==0 and u%4==0
 finite+=1
for p in [3,5,7]:
 for t,u in product(range(p),repeat=2):
  if (210*t*t+u*u)%p==0:assert u==0
  finite+=1
assert 4-3==1 and -2*12+5*5==1 and 2*60-17*7==1
for t,u in product(range(840),repeat=2):
 if (210*t*t+u*u)%840==0:assert t%2==0 and u%420==0
count=0
for d,r,s in product(range(1,25),range(-16,17),range(-16,17)):
 x,y=Q(r,d),Q(s,d);T=2*x;U=420*y;N=x*x+210*y*y
 assert 210*T*T+U*U==840*N
 if T.denominator==N.denominator==1:assert x.denominator==y.denominator==1
 count+=1
# The tempting half-integer basis is not integral for discriminant -840.
assert (Q(1,2)**2+210*Q(1,2)**2).denominator!=1
out={'status':'PASS','finite_congruence_cases':finite,'full_residue_grid_mod840':840**2,'rational_integrality_and_identity_cases':count,'bezout_checks':3,'negative_half_integer_control':1,'scope':'Exact regression only, not hosted Lean or a class-number/unramifiedness proof.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(out,indent=2)+'\\n');print(out)
''')
subprocess.run([sys.executable,str(p/'regress_cm_integral_rebuild.py')],check=True)
q=p/'INTEGER-PRIMARY'
for n in ['PELInertiaQuadraticEmbeddings318','PELInertiaNormalizerData318','PELQuadraticIntegralInvariants318']:shutil.copy2(o/(n+'.lean'),q/(n+'.lean'))
put('PRIMARY-PROVENANCE.json',{'mathlib_commit':'56a005855ea17e0b0958f73ec801ae140b0a1679','native_files':{'QuadDefsRebuild.lean':'Mathlib/Algebra/QuadraticAlgebra/Defs.lean','QuadBasicRebuild.lean':'Mathlib/Algebra/QuadraticAlgebra/Basic.lean','NumberBasicRebuild.lean':'Mathlib/NumberTheory/NumberField/Basic.lean','ZModBasicRebuild.lean':'Mathlib/Data/ZMod/Basic.lean','CoprimeBasicRebuild.lean':'Mathlib/RingTheory/Coprime/Basic.lean'},'history':'New reconstruction, not byte recovery; original literal carrier and trace/norm producers survive unchanged.'})
d=json.loads((o/'intake.json').read_text());prior=d['order'];d.update(packet=p.name,revision_of=o.name,status='DRAFT_CM_INTEGRAL_ORDER_RECONSTRUCTION_REVIEW_PENDING',order=prior+new,new_modules=new,modified_predecessor_modules=[],revised_modules=[],changed_modules=new,exact_predecessor_modules=prior,unchanged_producer_modules=len(prior));d['files']={n+'.lean':{'sha256':sha(p/(n+'.lean')),'imports':sorted(ci.import_names((p/(n+'.lean')).read_text()))} for n in d['order']};put('intake.json',d)
c=[]
for n in prior:
 assert (p/(n+'.lean')).read_bytes()==(o/(n+'.lean')).read_bytes()
 c.append({'source':o.name+'/'+n+'.lean','consumer':n+'.lean','source_sha256':sha(o/(n+'.lean')),'consumer_sha256':sha(p/(n+'.lean')),'exact_copy':True})
put('COPY_BINDINGS.json',{'copies':c})
obs=[('source_hypotheses','Integral z in actual K','Surviving quadratic trace/norm plus omega integral','No assumed full integer order'),('constructed_objects','Actual Quadratic4 and native RingOfIntegers','Literal integral coordinate ring and map','Same original carrier'),('index_domain_coverage','Every algebraic integer','Universal trace/norm and finite congruence implications','Regression is not coverage proof'),('transition_maps','Integer coordinate casting and old quaternion map','Exact mapRingHom and original realization','No abstract replacement'),('limiting_object_identity','Full native RingOfIntegers K','Surjective nativeMap proved from every integral z','Not a finite-index suborder'),('coefficient_conventions','theta squared=-210 and trace sign','T=2re,U=420im,N=re²+210im²','Secondary trace is negated explicitly'),('local_conditions','All possible denominators','Mod8,3,5,7 and actual Bezout factors','No missing prime2 condition'),('exceptional_cases','Even and odd denominators','Native castHom reduces8 to2 and4','Half-integer false basis rejected'),('downstream_consumption','Foundation for class group/discriminant reconstruction','Native integerEquiv and literal original realization','Later lost results are not assumed')]
put('APPLICATION.json',{'packet':p.name,'producer':'advance_pel_identification','status':d['status'],'claim':'Reconstruct full native integer-ring equivalence for SAME original CM210 quadratic carrier from universal integral coordinates.','intake_sha256':sha(p/'intake.json'),'copy_bindings_sha256':sha(p/'COPY_BINDINGS.json'),'local_lean_run':False,'new_source_acceptance':False,'historical_bytes_recovered':False,'class_number_restored':False,'unramified_extension_restored':False,'artin_reciprocity_proved':False,'sources':{n+'.lean':sha(p/(n+'.lean')) for n in d['order']},'bindings':{n:sha(p/n) for n in ['README.md','DERIVATION.md','intake.json','COPY_BINDINGS.json','PRIMARY-PROVENANCE.json','regress_cm_integral_rebuild.py','REGRESSION.json']},'primary_sources':{str(f.relative_to(p)):sha(f) for f in q.iterdir()},'obligations':[{'name':n,'required_input':a,'constructed_input':bb,'justification':c,'source_references':[x+'.lean' for x in new]+['DERIVATION.md'],'evidence':[x+'.lean' for x in new]+['DERIVATION.md']} for n,a,bb,c in obs]})
print('APP',sha(p/'APPLICATION.json'));print('INTAKE',sha(p/'intake.json'));print('NEWLINES',sum(len((p/(n+'.lean')).read_text().splitlines()) for n in new))
import check_progress_experiment as ce
_,diag,_,_=ce.packet(p.name,ci.derive_plan(early_depth=7));print('STATIC PASS',len(diag['order']))
