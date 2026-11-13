from pathlib import Path
import json,hashlib,sys,subprocess,shutil
r=Path(__file__).resolve().parents[1]; b=r/'quartics/quartic-318-326/proof/experiments'
o=b/'pel-original-cm-prime-products-rebuild-r1'; p=b/'pel-original-cm-class-exhaustion-rebuild-r1'
sys.path.insert(0,str(r/'scripts')); import check_progress_lean as ci
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
def put(n,d):(p/n).write_text(json.dumps(d,indent=2)+'\n')
new=["PELOriginalCM210SmallPrimePowers318","PELOriginalCM210MaximalTheta318","PELOriginalCM210PrimeResidueExclusions318","PELOriginalCM210BoundedMaximalIdeals318","PELOriginalCM210BoundedIdealFactors318","PELOriginalCM210NativeClassGeneration318","PELOriginalCM210BinaryClassWords318","PELOriginalCM210BinaryIdealWords318","PELOriginalCM210NativeClassNumberEight318"]
(p/'README.md').write_text("""# Native full class-group exhaustion for the original CM field

Nine new modules extend all 1,197 exact predecessor modules. They classify EVERY maximal ideal of native norm at most18 as one of the same four original coordinate kernels, prove full native ClassGroup generation using actual nonzero-ideal factorization and the already constructed Minkowski representative, then produce an explicit bijection from Bool cubed to the entire native ClassGroup. The endpoint is NumberField.classNumber K=8 for the SAME original m=210 field, via its already proved full ring of integers.

The lower bound is not an analytic label count: each nonempty Boolean word is represented by an actual product ideal, whose norm is one of2,3,5,6,10,15,30. Universal native element-norm nonprincipality excludes its being the identity class. The all-four principal relation removes the fourth generator for the upper bound.

Fresh reconstruction, not exact recovery of lost historical bytes. Distinct source review and Lean replay remain pending. No local Lean, new caps or lane changes. Class-field maximality, unramified extensions, CM algebraicity, Artin reciprocity, original CM residue fields and original/published numerical j remain separate.
""")
(p/'DERIVATION.md').write_text("""# Every native class, with exact prime kernels

## Actual prime ideal classification
The pinned native theorem Ideal.exists_prime_and_absNorm_eq_pow applies to every maximal ideal of the full native O_K, which is finite free over Z. It supplies an actual integer prime p in the ideal and norm p^n with n positive. Elementary inequalities reduce p to2,3,5,7,11,13,17.

For each ramified p=2,3,5,7, p in P and p dividing210 imply theta squared=-210 lies in P. P is prime, so theta lies in P. The already proved UNIVERSAL two-generator expression for the original coordinate kernel gives containment of that exact native kernel in P. Its native nonzero-prime/maximal status then gives equality, not just equality of norm or residue cardinality.

For p=11,13,17, norm at most18 forces exponent1. Finite-quotient instances are supplied from the actual finite Z-module. ZMod.ringEquivOfPrime identifies the actual residue ring with ZMod p. The inverse image of actual theta would square to -210. All41 finite residues are excluded by native decidable proofs. This proves exhaustive classification of every maximal ideal in the bound.

## Actual ideal factorization and full class generation
UniqueFactorizationMonoid.induction_on_prime is applied to the monoid of ideals of the actual Dedekind ring. The induction motive retains nonzero and norm at most18. Nonzero factor norms are positive; multiplicativity gives the same bound on EACH factor. Prime factors are actual maximal ideals, hence the classification applies. Native ClassGroup.mk0 multiplicativity then proves membership in any subgroup containing the four original classes. The old actual Minkowski representative supplies every class, yielding closure_eq_top.

## Exact eight-element bijection
Boolean triples evaluate to products of the first three actual classes. Their image is a genuine subgroup: multiplication is componentwise xor using the proved class squares, and each word is its own inverse. The actual all-four principal ideal relation supplies the fourth generator in that subgroup. Full native generation proves surjectivity.

Each word also has an actual nonzero integral product ideal with native norm given by its selected subset of2,3,5. For each nonempty word this is a nonsquare proper divisor of210. The prior universal native element-norm obstruction says such an ideal cannot be principal. Equality of two class words would make their xor word trivial, so the words agree. Equiv.ofBijective now gives an actual bijection with ALL native ideal classes; Nat.card and NumberField.classNumber yield8.

## History and boundaries
The lost later chain had source-reviewed class-number8, but its bytes and proof dependencies were not available after workspace loss. This is a fresh argument in new sources, using the present reviewed full-order/Minkowski/residue/square/nonprincipality/product chain. The earlier non-admitted exhaustion plan is incorporated through actual statements, maps, induction and consumers here, not cited as proof. No analytic action or external CM theorem is used. Neither equal cardinalities nor an abstract finite group replaces the native ClassGroup.

The source claim awaits distinct review and kernel replay. Arithmetic regression only checks exact finite identities and negative controls. No axiom, sorry, new option, assumed class-number or Galois/Artin action is introduced.
""")
(p/'regress_cm_class_exhaustion.py').write_text("""from pathlib import Path
from itertools import product
from math import isqrt
import json
primes=[2,3,5,7,11,13,17]
assert [p for p in range(2,19) if all(p%d for d in range(2,isqrt(p)+1))]==primes
primepowers=[(p,n,p**n) for p in primes for n in range(1,8) if p**n<=18]
assert all(p<=7 or n==1 for p,n,v in primepowers)
roots={p:[x for x in range(p) if (x*x+210)%p==0] for p in primes}
assert all(roots[p]==[] for p in [11,13,17])
assert all(roots[p]==[0] for p in [2,3,5,7])
words=list(product([False,True],repeat=3))
norms={a:(2 if a[0] else 1)*(3 if a[1] else 1)*(5 if a[2] else 1) for a in words}
assert sorted(norms.values())==[1,2,3,5,6,10,15,30]
for a in words:
 if any(a):
  d=norms[a]
  assert d<210 and isqrt(d)**2!=d and 210%d==0
for a,b in product(words,repeat=2):
 x=tuple(u!=v for u,v in zip(a,b))
 assert (not any(x))==(a==b)
 assert all((int(u)+int(v))%2==int(w) for u,v,w in zip(a,b,x))
# Independent theta-stable full rank lattices, HNF columns (a,0),(b,c).
hnf=[]
for a in range(1,19):
 for c in range(1,19):
  if a*c>18:continue
  for b in range(a):
   if a%c==0 and b%c==0 and (b*b+210*c*c)%(a*c)==0:
    hnf.append((a,b,c))
assert len(hnf)==15
assert sorted(a*c for a,b,c in hnf)==[1,2,3,4,5,6,7,8,9,10,12,14,15,16,18]
# Negative controls: ramified residues do have a root, and theta has norm210.
assert roots[7]==[0]
assert 0**2+210*1**2==210
out={'status':'PASS','prime_power_cases':len(primepowers),'excluded_residues':41,
 'ramified_residue_checks':17,'binary_words':8,'binary_pairs':64,
 'nonprincipal_word_norms':7,'independent_theta_stable_lattices':hnf,
 'negative_controls':2,'scope':'Exact regression, not Lean acceptance or CM reciprocity.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(out,indent=2)+'\\n')
print(out)
""")
subprocess.run([sys.executable,str(p/'regress_cm_class_exhaustion.py')],check=True)
q=p/'EXHAUSTION-PRIMARY'
plan=r/'quartics/quartic-318-326/proof/recovery/cm-class-exhaustion-plan-20261112'
native={"FiniteQuotients.lean":"Mathlib/RingTheory/Ideal/Quotient/HasFiniteQuotients/Basic.lean","DedekindIdeal.lean":"Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean","SubgroupBasic.lean":"Mathlib/Algebra/Group/Subgroup/Basic.lean","SubgroupDefs.lean":"Mathlib/Algebra/Group/Subgroup/Defs.lean","Prime.lean":"Mathlib/RingTheory/Ideal/Prime.lean","Maximal.lean":"Mathlib/RingTheory/Ideal/Maximal.lean","FiniteCardinal.lean":"Mathlib/SetTheory/Cardinal/Finite.lean"}
for n,path in {'AbsNorm.lean':'Mathlib/RingTheory/Ideal/Norm/AbsNorm.lean','UFDDefs.lean':'Mathlib/RingTheory/UniqueFactorizationDomain/Defs.lean','ZModBasic.lean':'Mathlib/Data/ZMod/Basic.lean'}.items():
 shutil.copy2(plan/n,q/n);native[n]=path
shutil.copy2(b/'pel-original-cm-minkowski-bound-rebuild-r2/MINKOWSKI-PRIMARY/ClassNumberRebuild.lean',q/'ClassNumber.lean')
native['ClassNumber.lean']='Mathlib/NumberTheory/NumberField/ClassNumber.lean'
shutil.copy2(o/'PRODUCT-PRIMARY/ClassGroupBasic.lean',q/'ClassGroupBasic.lean')
native['ClassGroupBasic.lean']='Mathlib/RingTheory/ClassGroup/Basic.lean'
put('PRIMARY-PROVENANCE.json',{'mathlib_commit':'56a005855ea17e0b0958f73ec801ae140b0a1679','native_files':native})
d=json.loads((o/'intake.json').read_text());prior=d['order']
d.update(packet=p.name,revision_of=o.name,status='DRAFT_CM_NATIVE_CLASS_EXHAUSTION_REVIEW_PENDING',order=prior+new,new_modules=new,modified_predecessor_modules=[],revised_modules=[],changed_modules=new,exact_predecessor_modules=prior,unchanged_producer_modules=len(prior))
d['files']={n+'.lean':{'sha256':sha(p/(n+'.lean')),'imports':sorted(ci.import_names((p/(n+'.lean')).read_text()))} for n in d['order']};put('intake.json',d)
copies=[]
for n in prior:
 assert (p/(n+'.lean')).read_bytes()==(o/(n+'.lean')).read_bytes()
 copies.append({'source':o.name+'/'+n+'.lean','consumer':n+'.lean','source_sha256':sha(o/(n+'.lean')),'consumer_sha256':sha(p/(n+'.lean')),'exact_copy':True})
put('COPY_BINDINGS.json',{'copies':copies})
obs=[
('source_hypotheses','Native maximal ideal prime-power norm theorem over finite free full O_K','Actual original full integer ring and every maximal P','No displayed suborder substitution'),
('constructed_objects','Prime factor ideal equal to a known original kernel','Theta square, prime radical property, actual universal generator expression, maximality','Same ideal equality before class map'),
('index_domain_coverage','Every maximal norm<=18 and every native class','All seven possible p and all positive exponents; ideal UFD; actual Minkowski representative','No sample ideal or analytic label restriction'),
('transition_maps','Actual residue quotient and ClassGroup.mk0','Native ZMod equivalence; exact nonzero ideal products and class multiplication','No scalar-field or residue-field conflation'),
('limiting_object_identity','Entire ClassGroup of the actual NumberField.RingOfIntegers K','Produced Bool-cube bijection and native classNumber definition','Not cardinality of a subgroup alone'),
('coefficient_conventions','Theta squared=-210, native ideal norm and product','Exact integer image, residue polynomial, subset norms2/3/5','Signed equation and original prime order retained'),
('local_conditions','Each prime factor bounded and nonzero','Positive native norms and multiplicativity bound BOTH factors','No unsupported divisibility-to-bound jump'),
('exceptional_cases','Zero ideal, unit ideal, excluded p11/13/17, empty Boolean word','Zero nonzero contradiction; unit class1; all41 roots excluded; zero word handled separately','210 principal ideal never fed into proper-divisor obstruction'),
('downstream_consumption','Class-number8 without CM reciprocity','Exact classEquiv and native_cardinality consumed by NumberField.classNumber','Unramified/HCF/Artin/CM residue-field identities remain separate')]
put('APPLICATION.json',{'packet':p.name,'producer':'advance_pel_identification','status':d['status'],
 'claim':'Full native class-group exhaustion and classNumber8 for the original m=210 field.',
 'intake_sha256':sha(p/'intake.json'),'copy_bindings_sha256':sha(p/'COPY_BINDINGS.json'),
 'local_lean_run':False,'new_source_acceptance':False,'historical_bytes_recovered':False,
 'class_number_source_producer_constructed':True,'class_number_kernel_verified':False,
 'artin_reciprocity_proved':False,
 'sources':{n+'.lean':sha(p/(n+'.lean')) for n in d['order']},
 'bindings':{n:sha(p/n) for n in ['README.md','DERIVATION.md','intake.json','COPY_BINDINGS.json','PRIMARY-PROVENANCE.json','regress_cm_class_exhaustion.py','REGRESSION.json']},
 'primary_sources':{str(f.relative_to(p)):sha(f) for f in q.iterdir()},
 'obligations':[{'name':n,'required_input':a,'constructed_input':bb,'justification':c,'source_references':[x+'.lean' for x in new]+['DERIVATION.md'],'evidence':[x+'.lean' for x in new]+['DERIVATION.md']} for n,a,bb,c in obs]})
print('APP',sha(p/'APPLICATION.json'));print('INTAKE',sha(p/'intake.json'))
print('NEWLINES',sum(len((p/(n+'.lean')).read_text().splitlines()) for n in new))
import check_progress_experiment as ce
_,diag,_,_=ce.packet(p.name,ci.derive_plan(early_depth=7));print('STATIC PASS',len(diag['order']))
