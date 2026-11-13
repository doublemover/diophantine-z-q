from pathlib import Path
import json, hashlib, shutil, sys
r=Path(__file__).resolve().parents[1]
b=r/'quartics/quartic-318-326/proof/experiments'
o=b/'pel-original-cm-constituent-orders-rebuild-r1'
p=b/'pel-original-cm-constituent-compositum-rebuild-r1'
sys.path.insert(0,str(r/'scripts'))
import check_progress_lean as ci
import check_progress_experiment as ce
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
def put(n,v):(p/n).write_text(json.dumps(v,indent=2)+'\n')
new=['PELCMShiftedRadicalGenerators318','PELCMConstituentFieldEmbeddings318','PELCMConstituentNativeOrderEmbeddings318','PELCMConstituentScalarTowers318','PELCMConstituentDiscriminantInputs318']
(p/'README.md').write_text("""# The full quadratic constituents embedded into the same radical field

Five new Lean source modules extend all 1,214 frozen predecessor modules. The already constructed full quadratic orders are now connected to the SAME degree-16 radical field H, not to unspecified isomorphic fields. Their integral generators map to sqrt(-2), (1+sqrt(-3))/2, (1+sqrt(5))/2 and (1+sqrt(-7))/2. Explicit equations construct injective Q-algebra embeddings and their restrictions to full native integer rings.

Recover every raw radical from these shifted generators. The prior arbitrary-element generation theorem then proves that the supremum of the four literal embedded constituent images is all H. The actual scalar towers have relative degree 8. All pairs of native constituent discriminants are coprime by explicit integral Bezout witnesses, and their product is -840.

This supplies actual constituent/compositum inputs for a later coprime-discriminant maximal-order theorem. It does NOT prove that the product order is the full integer ring of H, compute native NumberField.discr H, prove finite unramifiedness, identify a Hilbert class field, establish reciprocity or identify an original CM residue field or a published numerical j invariant. An exact rational regression computes a candidate integral-basis discriminant only; it cannot discharge maximality.

Source review and GitHub Lean replay are pending. No Lean build has run in the assistant cloud. All previous source and review records are immutable, and predecessor acceptance is not whole-proof kernel acceptance.
""")
(p/'DERIVATION.md').write_text("""# Same-carrier constituent comparison

## Shifted generators and equations
The four constituent carriers are precisely PELCMQuadraticConstituentFields318.Field i, with equations omega^2 = a_i + b_i omega and pairs (-2,0), (-1,1), (1,1), (-2,1). Their full native integer rings and discriminants were proved by the predecessor's universal denominator-removal argument. In the existing literal radical tower H, define shifted generators using the already named raw radicals. Their square equations follow from the same raw-square certificates. The first generator is unshifted; the other three are (1+g)/2. No division occurs in the integer ring until integrality is proved by transport from the full constituent order.

## Actual field and full-order maps
QuadraticAlgebra.lift consumes each displayed square equation and gives a Q-algebra homomorphism from that exact constituent into H. Its omega image and arbitrary-element coordinate formula are explicit. Field-homomorphism injectivity proves these are embeddings. The native integer map is defined by applying the actual field map to an arbitrary native integer and transporting its IsIntegral proof. Its value square with fullIntegerEquiv is definitional. Thus the source full order, native order and H element are literally identified, not merely assigned equal discriminants.

## Full compositum rather than four selected points
Every raw radical is recovered from the shifted generator: g_0=w_0 and g_i=2*w_i-1 for i=1,2,3. Every Q-subalgebra containing all shifted generators therefore contains every raw radical. The predecessor all_mem theorem, proved from arbitrary coordinates through every quadratic stage, then puts EVERY element of H into that subalgebra. Apply this to the supremum of the actual ranges of the four embeddings. Each shifted generator belongs to its own range as the image of omega. The supremum is top; no dimension match is substituted for this elementwise argument.

## Actual towers and discriminant inputs
Each field homomorphism supplies its own Algebra and compatible Q/Field_i/H scalar tower. FiniteDimensional.right supplies the relative finite-dimensional structure. Native finrank multiplication, together with constituent degree 2 and the same H's degree 16, gives relative degree 8 for all four constituents. This is distinct from the original K/H tower, which remains unchanged.

The native constituent discriminants are -8, -3, 5 and -7. A complete 4 by 4 integral Bezout table proves pairwise coprimality for every distinct pair. The product is -840. This information concerns the exact full native constituent orders embedded above. It is sufficient input material for a coprime-discriminant compositum argument, but that maximal-order argument is NOT asserted or assumed here.

## Historical disposition and open boundary
The constituent full-order draft survived and received a new scoped internal review. The five connecting modules are new work. Their application is subject to a separate independent review. The same original m=210 CM field embeds in H as before; no CM point is added or renamed. A candidate integral product basis has arithmetic discriminant 840^8 in the regression, but the full H integer ring, native H discriminant, relative different, unramifiedness, Hilbert class-field maximality, Artin action and original CM residue-field identification remain open consumers.
""")
q=p/'COMPOSITUM-PRIMARY';q.mkdir(exist_ok=True)
rad=b/'pel-original-cm-radical-extension-rebuild-r1/RADICAL-PRIMARY'
items=[(o/'ORDER-PRIMARY/QuadraticBasic.lean','QuadraticBasic.lean','Mathlib/Algebra/QuadraticAlgebra/Basic.lean'),(o/'ORDER-PRIMARY/QuadraticDefs.lean','QuadraticDefs.lean','Mathlib/Algebra/QuadraticAlgebra/Defs.lean'),(rad/'DimensionFree.lean','DimensionFree.lean','Mathlib/LinearAlgebra/Dimension/Free.lean'),(rad/'FieldTower.lean','FieldTower.lean','Mathlib/FieldTheory/Tower.lean'),(rad/'AlgebraTower.lean','AlgebraTower.lean','Mathlib/RingTheory/AlgebraTower.lean'),(b/'height-original-normal-native-dual-restriction-rebuild-r1/REBUILD-PRIMARY/SubalgebraBasic.lean','SubalgebraBasic.lean','Mathlib/Algebra/Algebra/Subalgebra/Basic.lean'),(b/'forward-original-weighted-weyl-r2/DESCENT-ACTUAL-IMAGES-PRIMARY/Mathlib-RingTheory-Coprime-Basic.lean','CoprimeBasic.lean','Mathlib/RingTheory/Coprime/Basic.lean')]
for src,name,_ in items:shutil.copy2(src,q/name)
put('PRIMARY-PROVENANCE.json',{'mathlib_commit':'56a005855ea17e0b0958f73ec801ae140b0a1679','native_files':{name:url for _,name,url in items}})
i=json.loads((o/'intake.json').read_text());prior=i['order']
i.update(packet=p.name,revision_of=o.name,status='DRAFT_SAME_H_CONSTITUENT_COMPOSITUM_REVIEW_PENDING',order=prior+new,new_modules=new,modified_predecessor_modules=[],revised_modules=[],changed_modules=new,exact_predecessor_modules=prior,unchanged_producer_modules=len(prior))
i['files']={n+'.lean':{'sha256':sha(p/(n+'.lean')),'imports':sorted(ci.import_names((p/(n+'.lean')).read_text()))} for n in i['order']};put('intake.json',i)
copies=[]
for n in prior:
 assert (p/(n+'.lean')).read_bytes()==(o/(n+'.lean')).read_bytes()
 copies.append({'source':o.name+'/'+n+'.lean','consumer':n+'.lean','source_sha256':sha(o/(n+'.lean')),'consumer_sha256':sha(p/(n+'.lean')),'exact_copy':True})
put('COPY_BINDINGS.json',{'copies':copies})
obs=[('source_hypotheses','Quadratic lift needs exact generator equation; generation theorem needs all raw generators','Each shifted equation is proved from the literal radical-square theorem; every raw generator recovered','No abstract field equivalence or degree count replaces the equations'),('constructed_objects','The same four full native constituent orders and the same H','Literal domains Field i, fullIntegerEquiv and embedding into original radical H','Native order map defined by actual field embedding, with an exact value square'),('index_domain_coverage','All four constituent indices and every element of H','Fin 4 cases include the even unshifted row and all three odd shifted rows; all_mem covers every H element','The range supremum is not only a collection of four known elements'),('transition_maps','Q algebra embedding and full-integer-ring restriction must commute','Explicit coordinate map and definitional full_order_square','All rational and integer coefficients are mapped into the same H'),('limiting_object_identity','The full compositum in H, not a related isomorphic field','The supremum of the literal four ranges is top by arbitrary-element generation','No cardinality-only inference; full H integer order is not yet identified'),('coefficient_conventions','Omega square equals a+b omega, with the correct odd half-generators','Raw radicands -2,-3,5,-7; integral discriminants -8,-3,5,-7','Division by 2 is in H; integrality comes later from actual native integer transport'),('local_conditions','Coprime native constituent discriminants for each distinct pair','Complete integral Bezout table, applied after native_discriminant rewrite','Not a proof of relative unramifiedness or local maximality'),('exceptional_cases','Even constituent and distinct-index condition','First generator unshifted; diagonal pairs explicitly excluded','No false half-integral basis for sqrt(-2) and no false diagonal coprimality'),('downstream_consumption','Inputs for full compositum order and native discriminant argument','Same-carrier embeddings, full order restriction, top compositum, degrees and coprime discriminants','Maximal product order, H discriminant, different, reciprocity and original CM fields remain separate')]
put('APPLICATION.json',{'packet':p.name,'producer':'/root/pel_restart','status':i['status'],'claim':'Literal constituent field and native integer embeddings into the same H, full compositum identity, actual relative degrees, and pairwise native discriminant coprimality.','intake_sha256':sha(p/'intake.json'),'copy_bindings_sha256':sha(p/'COPY_BINDINGS.json'),'local_lean_run':False,'kernel_acceptance':False,'new_source_acceptance':False,'historical_acceptance_transferred':False,'full_H_integer_ring_proved':False,'unramifiedness_proved':False,'artin_reciprocity_proved':False,'sources':{n+'.lean':sha(p/(n+'.lean')) for n in i['order']},'bindings':{n:sha(p/n) for n in ['README.md','DERIVATION.md','intake.json','COPY_BINDINGS.json','PRIMARY-PROVENANCE.json','regress_cm_constituent_compositum.py','REGRESSION.json']},'primary_sources':{str(f.relative_to(p)):sha(f) for f in q.iterdir()},'obligations':[{'name':n,'required_input':a,'constructed_input':bb,'justification':c,'source_references':[x+'.lean' for x in new]+['DERIVATION.md'],'evidence':[x+'.lean' for x in new]+['DERIVATION.md']} for n,a,bb,c in obs]})
_,d,_,_=ce.packet(p.name,ci.derive_plan(early_depth=7))
print('STATIC PASS',len(d['order']),'new modules',len(new),'lines',sum(len((p/(n+'.lean')).read_text().splitlines()) for n in new))
print('APPLICATION',sha(p/'APPLICATION.json'));print('INTAKE',sha(p/'intake.json'))
