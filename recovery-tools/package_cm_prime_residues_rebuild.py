from pathlib import Path
import json,hashlib,sys,subprocess,shutil
r=Path(__file__).resolve().parents[1];b=r/'quartics/quartic-318-326/proof/experiments';o=b/'pel-original-cm-minkowski-bound-rebuild-r2';p=b/'pel-original-cm-prime-residues-rebuild-r1'
sys.path.insert(0,str(r/'scripts'));import check_progress_lean as ci
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
def put(n,d):(p/n).write_text(json.dumps(d,indent=2)+'\n')
new=['PELOriginalCM210PrimeReduction318','PELOriginalCM210PrimeSpan318','PELOriginalCM210NativePrimeResidue318','PELOriginalCM210NativePrimeNorm318','PELOriginalCM210FourNativePrimes318']
(p/'README.md').write_text('''# Reconstruct actual CM210 prime residues and native ideals

Five NEW sources extend the exact 1,179-source repaired Minkowski-bound-rebuild-r2 closure. They construct, for every natural p dividing210, the actual reduction R=Z[sqrt(-210)] to ZMod p by the real coordinate. Its kernel is exactly the ideal (p,theta), with a universal two-generator expression. Transport along the proved full native integer-ring equivalence constructs a literal ideal of O_K, an actual quotient RING equivalence to ZMod p, and its exact coordinate square.

For p nonzero the native ideal norm is p. If p is prime the native ideal is nonzero and prime. Specialize to the unchanged original prime labels 2,3,5,7. Thus these are actual prime ideals of the full original integer ring, not quaternionic right ideals or merely abstract residues of the same cardinality.

This restores prime-ideal prerequisites only. It does not prove their squares principal, nontrivial ideal classes, class-group generation, class-number8, CM point residue fields or Artin reciprocity. Those are separate reconstruction steps. All three reviewed audit repairs are inherited explicitly through the predecessor r2; no frozen packet is edited. No local Lean build, new resource caps or hosted acceptance claim.
''')
(p/'DERIVATION.md').write_text('''# Exact prime-ideal construction

Use the same original K and its freshly reconstructed FULL native integer ring O, not a chosen suborder. The literal integral quadratic algebra R has theta squared=-210. For p dividing210, the map z↦re(z) mod p is a ring homomorphism: the extra product term -210*im(z)*im(w) vanishes modulo p. Integer constants give a surjective map to ZMod p.

The kernel criterion is p|re(z), from the native integer-cast criterion. Write re(z)=p*a. Then z=a*p+im(z)*theta, proving universal inclusion in the two-generator ideal. Conversely both p and theta map to zero. This yields exact kernel equality, not just equality of norms.

Compose this reduction with integerEquiv.symm to obtain a ring homomorphism on the actual full native O_K. Surjectivity is the composition of the two actual surjections. Its native quotient equivalence is the first isomorphism theorem for this exact ring homomorphism. The commutative square sends the original integer element z to re(z) mod p literally. The native ideal membership criterion is retained on every O_K element.

The native ideal norm is the cardinality of the quotient, so the actual quotient equivalence proves norm p. Nonzero p rules out the zero ideal, whose norm is zero in the native infinite integer ring. Primality is supplied by the native Dedekind theorem that an ideal with irreducible absolute norm is prime. Finally specialize p to the existing PELPrimeNormalizerData prime labels 2,3,5,7, retaining their exact order. These ideals live in the commutative integer ring of the original CM quadratic field; no equation with the old quaternionic right ideals is inferred.

The preceding Minkowski theorem bounds representatives of every class. This packet supplies the actual small prime ideals needed for the next class-group construction; it does not yet classify every bounded-norm ideal or identify classes. External class field theory remains entirely separate.
''')
(p/'regress_cm_prime_residues_rebuild.py').write_text('''from pathlib import Path
from itertools import product
import json
mul=0;span=0
for p in [1,2,3,5,6,7,10,14,15,21,30,35,42,70,105,210]:
 assert 210%p==0
 for r,s,u,v in product(range(-4,5),repeat=4):
  assert (r*u-210*s*v)%p==(r%p)*(u%p)%p
  mul+=1
 for r,s in product(range(-60,61),repeat=2):
  if r%p==0:
   a=r//p;assert (a*p,s)==(r,s)
  span+=1
for p in [2,3,5,7]:
 assert len({r%p for r in range(p)})==p
# Negative: reducing by a nondivisor does not kill theta squared.
assert (-210)%11!=0 and (-210)%13!=0
out={'status':'PASS','multiplication_cases':mul,'universal_span_witness_tests':span,'actual_prime_quotient_counts':[2,3,5,7],'negative_nondivisor_controls':2,'scope':'Exact finite regression, not Lean or ideal-class exhaustion.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(out,indent=2)+'\\n');print(out)
''')
subprocess.run([sys.executable,str(p/'regress_cm_prime_residues_rebuild.py')],check=True)
q=p/'RESIDUE-PRIMARY';shutil.copy2(b/'pel-original-cm-integral-order-rebuild-r1/INTEGER-PRIMARY/ZModBasicRebuild.lean',q/'ZModBasic.lean');shutil.copy2(b/'pel-original-cm-integral-order-rebuild-r1/INTEGER-PRIMARY/QuadDefsRebuild.lean',q/'QuadDefs.lean')
put('PRIMARY-PROVENANCE.json',{'mathlib_commit':'56a005855ea17e0b0958f73ec801ae140b0a1679','native_files':{'QuotientOperations.lean':'Mathlib/RingTheory/Ideal/Quotient/Operations.lean','AbsNorm.lean':'Mathlib/RingTheory/Ideal/Norm/AbsNorm.lean','IdealOperations.lean':'Mathlib/RingTheory/Ideal/Operations.lean','ZModDefs.lean':'Mathlib/Data/ZMod/Defs.lean','ZModBasic.lean':'Mathlib/Data/ZMod/Basic.lean','QuadDefs.lean':'Mathlib/Algebra/QuadraticAlgebra/Defs.lean'}})
d=json.loads((o/'intake.json').read_text());prior=d['order'];d.update(packet=p.name,revision_of=o.name,status='DRAFT_CM_PRIME_RESIDUES_RECONSTRUCTION_REVIEW_PENDING',order=prior+new,new_modules=new,modified_predecessor_modules=[],revised_modules=[],changed_modules=new,exact_predecessor_modules=prior,unchanged_producer_modules=len(prior));d['files']={n+'.lean':{'sha256':sha(p/(n+'.lean')),'imports':sorted(ci.import_names((p/(n+'.lean')).read_text()))} for n in d['order']};put('intake.json',d)
c=[]
for n in prior:
 assert (p/(n+'.lean')).read_bytes()==(o/(n+'.lean')).read_bytes()
 c.append({'source':o.name+'/'+n+'.lean','consumer':n+'.lean','source_sha256':sha(o/(n+'.lean')),'consumer_sha256':sha(p/(n+'.lean')),'exact_copy':True})
put('COPY_BINDINGS.json',{'copies':c})
obs=[('source_hypotheses','p divides210, p nonzero/prime where used','Actual divisor and prime certificates for2,3,5,7','Generic proofs retain exact hypotheses'),('constructed_objects','Literal integral reduction and full O_K ideal','Actual ring homomorphism kernels and quotient equivalences','No abstract residue substitution'),('index_domain_coverage','All integer elements and four original labels','Universal two-generator expression and Fin4 proof','Finite regression not coverage proof'),('transition_maps','R to O_K to ZModp','Exact integerEquiv.symm composition and quotient square','Same original integer map'),('limiting_object_identity','Full native O_K and native Ideal.absNorm','Actual native integer equivalence and quotient cardinality','Not a quaternionic order ideal'),('coefficient_conventions','theta squared=-210','Real coordinate reduction with210=0','Correct sign and original prime order'),('local_conditions','Ring homomorphism requires p|210','Explicit native integer-cast divisibility','Nondivisors excluded'),('exceptional_cases','p zero or composite','Norm theorem requires NeZero, primality requires p.Prime','Generic divisor map does not assert field for composite'),('downstream_consumption','Native class-group prerequisites','Actual four nonzero prime ideals and norms','No principal-square or class exhaustion claim')]
put('APPLICATION.json',{'packet':p.name,'producer':'advance_pel_identification','status':d['status'],'claim':'Actual CM210 reduction kernels, full native integer-ring residue equivalences and four original nonzero prime ideals with exact norms.','intake_sha256':sha(p/'intake.json'),'copy_bindings_sha256':sha(p/'COPY_BINDINGS.json'),'local_lean_run':False,'new_source_acceptance':False,'historical_bytes_recovered':False,'class_number_restored':False,'artin_reciprocity_proved':False,'sources':{n+'.lean':sha(p/(n+'.lean')) for n in d['order']},'bindings':{n:sha(p/n) for n in ['README.md','DERIVATION.md','intake.json','COPY_BINDINGS.json','PRIMARY-PROVENANCE.json','regress_cm_prime_residues_rebuild.py','REGRESSION.json']},'primary_sources':{str(f.relative_to(p)):sha(f) for f in q.iterdir()},'obligations':[{'name':n,'required_input':a,'constructed_input':bb,'justification':c,'source_references':[x+'.lean' for x in new]+['DERIVATION.md'],'evidence':[x+'.lean' for x in new]+['DERIVATION.md']} for n,a,bb,c in obs]})
print('APP',sha(p/'APPLICATION.json'));print('INTAKE',sha(p/'intake.json'));print('NEWLINES',sum(len((p/(n+'.lean')).read_text().splitlines()) for n in new))
import check_progress_experiment as ce
_,diag,_,_=ce.packet(p.name,ci.derive_plan(early_depth=7));print('STATIC PASS',len(diag['order']))
