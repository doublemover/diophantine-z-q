from pathlib import Path
import json,hashlib,sys,subprocess,shutil
r=Path(__file__).resolve().parents[1];b=r/'quartics/quartic-318-326/proof/experiments'
o=b/'pel-original-cm-radical-extension-rebuild-r1';p=b/'pel-original-cm-constituent-orders-rebuild-r1'
sys.path.insert(0,str(r/'scripts'));import check_progress_lean as ci
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
def put(n,d):(p/n).write_text(json.dumps(d,indent=2)+'\n')
new=["PELCMQuadraticIntegralTraceData318","PELCMQuadraticNativeIntegerOrder318","PELCMQuadraticNativeDiscriminant318","PELCMOddQuadraticDenominators318","PELCMOddQuadraticFullCoordinates318","PELCMMinusTwoFullCoordinates318","PELCMQuadraticConstituentFields318","PELCMQuadraticConstituentOrders318"]
(p/'README.md').write_text("""# Full native integer rings and discriminants of all four constituents

Eight new modules extend all1,206 exact radical-extension predecessor sources. Universally prove full integral coordinates for the four quadratic rings with generator equations omega²=-2, omega²=omega-1, omega²=omega+1 and omega²=omega-2. Construct actual ring equivalences from these integral quadratic orders onto the FULL native NumberField.RingOfIntegers, not an assumed maximal order.

Transport the exact rank-two trace bases through these proved equivalences. Their native NumberField discriminants are exactly[-8,-3,5,-7]. The generic full-coordinate premise is explicit and is actually supplied for every one of the four concrete consumers.

This is a maximal-order prerequisite for the H/K unramifiedness reconstruction. The shifted constituent fields still require exact embeddings into the SAME H, compositum identification and the coprime-discriminant theorem. No full H discriminant, relative different, unramifiedness, Hilbert class-field or Artin/CM claim is made yet.

Fresh distinct source review and Lean replay pending. No local Lean, changed caps, or predecessor edits. The prior radical-extension review remains a separate dependency gate.
""")
(p/'DERIVATION.md').write_text("""# Full orders, with every denominator removed

## Generic trace and norm data
For F=Q[omega]/(omega²-b omega-a), the explicit integral quadratic order R=Z[omega] maps coordinatewise into F and every image is integral. Omega is integral from that actual map.

For an arbitrary integral z=r+s omega, native conjugation/integral-closure producers give integer trace T=2r+bs and integer norm N=r²+brs-a s². Apply the same trace producer to the actual integral product omega*z. If its trace is V, then U=2V-bT=(4a+b²)s is an integer. The universal identity is D T²-U²=4D N, D=4a+b².

## Three odd discriminants
For (a,b)=(-1,1),(1,1),(-2,1), D is-3,5,-7. Cast the identity to the ACTUAL prime residue ring ZMod3,5,7 respectively. Since D is zero there, U²=0; the native domain/pow-zero theorem forces U=0 there and hence D divides U in Z. Write U=D s with integer s. Cancel the nonzero D in the original identity to obtain T²-D s²=4N.

Each D is1 modulo4. The finite mod4 square-parity lemma then implies T-s is even. Thus T=2r+s with integer r. The original rational trace/weighted trace equations give actual integral coordinates of the arbitrary integral element z. No coordinate bound or chosen ideal is assumed.

## The even constituent
For omega²=-2 the traces T=2r and U=4s are integral. Their exact norm identity is2T²+U²=8N. Exhaustive mod8 square residues imply2 divides T and4 divides U. Therefore r and s are integers for every integral z. This proves the full order Z[sqrt(-2)].

## Actual full native rings and discriminants
The generic nativeMap sends R into the native ring of integers. Injectivity is coordinatewise; the supplied universal integral-coordinate theorem proves surjectivity. The resulting ring equivalence and its Z-algebra upgrade are literal, not index comparisons.

Compute the actual left multiplication matrix [[r,a s],[s,r+b s]], trace2r+bs, and integral trace Gram[[2,b],[b,2a+b²]]. Its determinant is4a+b². Explicitly unfold the native quadratic basis in BOTH coordinate computations, avoiding the nonexistent basis_apply_one shortcut. Transport this basis through the proved FULL native integer-ring equivalence and apply NumberField.discr_eq_discr. Every concrete row supplies the full-coordinate theorem, yielding native discriminants-8,-3,5,-7.

## Noncircularity and next consumers
The four field structures are established separately from root impossibility: negativity for three discriminants and the already produced rational nonsquare5 for the real constituent. Native NumberField instances come from actual quadratic finite bases. No discriminant or maximality assumption is used to establish the coordinate theorem.

Historical retained complementary-order statements guide this fresh reconstruction, but their missing bodies and approvals are not reused. The present full-order arguments and their exact native consumers require fresh review. Shifted half-generators in H and full compositum/discriminant transport are the next distinct producer, not inferred here. In particular the raw radical basis is not mistaken for the full integer basis.
""")
(p/'regress_cm_constituent_orders.py').write_text("""from pathlib import Path
from fractions import Fraction
from itertools import product
import json
rows=[(-2,0,-8),(-1,1,-3),(1,1,5),(-2,1,-7)]
identity=0
for a,b in product(range(-4,5),repeat=2):
 D=4*a+b*b
 for r,s in product([Fraction(i,j) for i in range(-5,6) for j in range(1,5)],repeat=2):
  T=2*r+b*s;U=D*s;N=r*r+b*r*s-a*s*s
  assert D*T*T-U*U==4*D*N
  identity+=1
residues=0
for d in [-3,5,-7]:
 m=4*abs(d)
 for T,U in product(range(m),repeat=2):
  if (d*T*T-U*U)%(4*d)==0:
   assert U%d==0 and (T-U//d)%2==0
  residues+=1
for T,U in product(range(8),repeat=2):
 if (2*T*T+U*U)%8==0:assert T%2==0 and U%4==0
grid=sorted({Fraction(i,j) for i in range(-12,13) for j in range(1,9)})
coordinates=0
for a,b,d in rows:
 assert 4*a+b*b==d
 assert 2*(2*a+b*b)-b*b==d
 for r,s in product(grid,repeat=2):
  T=2*r+b*s;N=r*r+b*r*s-a*s*s
  if T.denominator==N.denominator==1:assert r.denominator==s.denominator==1
  coordinates+=1
# Wrong half-integral basis for sqrt(-2) is not integral.
r=s=Fraction(1,2)
assert (r*r+2*s*s).denominator!=1
# Raw odd-radicand basis has discriminant4d, not the full d.
assert all(4*d!=d for d in [-3,5,-7])
out={'status':'PASS','universal_trace_norm_identity_cases':identity,'odd_modular_cases':residues,
 'even_modular_cases':64,'rational_integral_coordinate_stress_cases':coordinates,
 'actual_discriminants':[d for a,b,d in rows],'negative_controls':4,
 'scope':'Exact arithmetic regression, not Lean or full H discriminant/unramifiedness.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(out,indent=2)+'\\n');print(out)
""")
subprocess.run([sys.executable,str(p/'regress_cm_constituent_orders.py')],check=True)
q=p/'ORDER-PRIMARY'
copies_native=[
(o/'RADICAL-PRIMARY/QuadraticBasic.lean','QuadraticBasic.lean','Mathlib/Algebra/QuadraticAlgebra/Basic.lean'),
(o/'RADICAL-PRIMARY/QuadraticDefs.lean','QuadraticDefs.lean','Mathlib/Algebra/QuadraticAlgebra/Defs.lean'),
(b/'pel-original-cm-minkowski-bound-rebuild-r2/MINKOWSKI-PRIMARY/AlgDiscrRebuild.lean','AlgebraDiscriminant.lean','Mathlib/RingTheory/Discriminant.lean'),
(b/'pel-original-cm-minkowski-bound-rebuild-r2/MINKOWSKI-PRIMARY/NFDiscrRebuild.lean','NumberFieldDiscriminant.lean','Mathlib/NumberTheory/NumberField/Discriminant/Defs.lean'),
(b/'pel-original-cm-minkowski-bound-rebuild-r2/MINKOWSKI-PRIMARY/ToLinRebuild.lean','MatrixToLin.lean','Mathlib/LinearAlgebra/Matrix/ToLin.lean'),
(b/'pel-original-cm-prime-residues-rebuild-r1/RESIDUE-PRIMARY/ZModBasic.lean','ZModBasic.lean','Mathlib/Data/ZMod/Basic.lean')]
native={}
for src,n,url in copies_native:
 if not src.exists() and n=='ZModBasic.lean':src=r/'quartics/quartic-318-326/proof/recovery/cm-class-exhaustion-plan-20261112/ZModBasic.lean'
 shutil.copy2(src,q/n);native[n]=url
put('PRIMARY-PROVENANCE.json',{'mathlib_commit':'56a005855ea17e0b0958f73ec801ae140b0a1679','native_files':native})
d=json.loads((o/'intake.json').read_text());prior=d['order']
d.update(packet=p.name,revision_of=o.name,status='DRAFT_CM_CONSTITUENT_FULL_ORDERS_REVIEW_PENDING',order=prior+new,new_modules=new,modified_predecessor_modules=[],revised_modules=[],changed_modules=new,exact_predecessor_modules=prior,unchanged_producer_modules=len(prior))
d['files']={n+'.lean':{'sha256':sha(p/(n+'.lean')),'imports':sorted(ci.import_names((p/(n+'.lean')).read_text()))} for n in d['order']};put('intake.json',d)
copies=[]
for n in prior:
 assert (p/(n+'.lean')).read_bytes()==(o/(n+'.lean')).read_bytes()
 copies.append({'source':o.name+'/'+n+'.lean','consumer':n+'.lean','source_sha256':sha(o/(n+'.lean')),'consumer_sha256':sha(p/(n+'.lean')),'exact_copy':True})
put('COPY_BINDINGS.json',{'copies':copies})
obs=[
('source_hypotheses','Integral z in actual commutative quadratic field','Actual integral coordinate map and omega; trace/norm and trace of omega*z','No quaternionic integrality closure assumption'),
('constructed_objects','Full native integer ring, not a suborder','Universal denominator removal gives actual map surjectivity','All four rows supplied'),
('index_domain_coverage','Every integral element and every constituent','Generic trace identity plus3 odd and1 even exact cases','Finite residue proofs apply to arbitrary integers via casts'),
('transition_maps','R_Z to F_Q to full native O_F','Explicit coordinate ring map, ring equivalence and Z-algebra upgrade','Correct native basis transport'),
('limiting_object_identity','Native NumberField.discr of each actual field','Full integer basis via proved equivalence and native discr_eq_discr','Raw basis or table label is insufficient'),
('coefficient_conventions','omega²=a+b omega, D=4a+b²','Actual rows(-2,0),(-1,1),(1,1),(-2,1)','Trace/norm signs and half-generator convention fixed'),
('local_conditions','Divisibility of all denominators','Prime residue domains3/5/7, mod4 parity and mod8 even obstruction','No unsupplied coordinate premise in concrete consumer'),
('exceptional_cases','Even versus odd discriminant and real quadratic row','Separate -8 proof; rational nonsquare5 supplies field','No false uniform half-integral basis'),
('downstream_consumption','Maximal-order/discriminant prerequisite for H compositum','Exact native discriminants-8,-3,5,-7','Same-H embeddings/compositum/relative different remain separate')]
put('APPLICATION.json',{'packet':p.name,'producer':'advance_pel_identification','status':d['status'],'claim':'Full native integer rings and actual discriminants of all four quadratic constituents; no full H discriminant or unramifiedness.',
'intake_sha256':sha(p/'intake.json'),'copy_bindings_sha256':sha(p/'COPY_BINDINGS.json'),'local_lean_run':False,'new_source_acceptance':False,'historical_acceptance_transferred':False,'unramifiedness_proved':False,'artin_reciprocity_proved':False,
'sources':{n+'.lean':sha(p/(n+'.lean')) for n in d['order']},
'bindings':{n:sha(p/n) for n in ['README.md','DERIVATION.md','intake.json','COPY_BINDINGS.json','PRIMARY-PROVENANCE.json','regress_cm_constituent_orders.py','REGRESSION.json']},
'primary_sources':{str(f.relative_to(p)):sha(f) for f in q.iterdir()},
'obligations':[{'name':n,'required_input':a,'constructed_input':bb,'justification':c,'source_references':[x+'.lean' for x in new]+['DERIVATION.md'],'evidence':[x+'.lean' for x in new]+['DERIVATION.md']} for n,a,bb,c in obs]})
print('APP',sha(p/'APPLICATION.json'));print('INTAKE',sha(p/'intake.json'))
print('NEWLINES',sum(len((p/(n+'.lean')).read_text().splitlines()) for n in new))
import check_progress_experiment as ce
_,diag,_,_=ce.packet(p.name,ci.derive_plan(early_depth=7));print('STATIC PASS',len(diag['order']))
