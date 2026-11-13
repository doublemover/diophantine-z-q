"""Freeze the original-kernel target-open successor; no Lean invocation."""
from pathlib import Path
import hashlib,json,re,sys,subprocess,shutil
root=Path(__file__).resolve().parents[1]
ex=root/'quartics/quartic-318-326/proof/experiments'
old=ex/'relative-original-kernel-scalar-saturation-rebuild-r1'
p=ex/'relative-original-kernel-target-open-rebuild-r1'
h=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
def put(n,v): (p/n).write_text(json.dumps(v,indent=2)+'\n')
new=json.loads((p/'REBUILD-NEW-SOURCES.json').read_text());assert len(new)==len(set(new))==16
prev=json.loads((old/'intake.json').read_text());order=prev['order']+new
assert all((p/n).read_bytes()==(old/n).read_bytes() for n in prev['files'])
files={n+'.lean':{'sha256':h(p/(n+'.lean')),'imports':re.findall(r'^(?:public )?import ([A-Za-z0-9_.]+)',(p/(n+'.lean')).read_text(),re.M)} for n in order}
put('intake.json',{'packet':p.name,'status':'FRESH_RECONSTRUCTION_PENDING_REVIEW_KERNEL_PENDING','order':order,'files':files,'new_modules':new})
put('SOURCE-COPIES.json',{'predecessor':old.name,'predecessor_intake_sha256':h(old/'intake.json'),'exact_predecessor_sources':len(prev['files']),'new_sources':{n+'.lean':h(p/(n+'.lean')) for n in new},'historical_byte_recovery':False,'changed_predecessor_sources':[]})
put('COPY_BINDINGS.json',{'predecessor':old.name,'unchanged':{n:h(p/n) for n in prev['files']},'changed':{}})
(p/'MODULE_ORDER.txt').write_text('\n'.join(order)+'\n')
(p/'SOURCE_SHA256SUMS').write_text(''.join(v['sha256']+'  '+n+'\n' for n,v in files.items()))
(p/'README.md').write_text('''# Original kernel global target open and all-scheme tests

Sixteen reconstruction sources, 1,326 exact predecessor sources, 1,342 total. Twelve recovered unfinished source drafts are repaired and joined to four new all-test/base-change/relation sources. This is not a historical-byte recovery claim. The old copied metadata described the predecessor; this packet now binds its actual current sources and consumer.

The two ORIGINAL full-kernel points on every exact normalized overlap differ by the literal inverse coordinate UNIT. All-ring unit invariance of the entire original zero scheme proves equality of the slice opens on every actual overlap. Their images glue into one genuine open of the SAME represented normalized-kernel scheme, with exact restriction on each chart. No projectivity of H0 or the kernel, H1 vanishing, reducedness or field-rational-point sufficiency is assumed.

The original whole nowhere-zero family maps smoothly and surjectively to that produced target open. Its square with the old full-kernel normalization is an actual categorical pullback. The exact source open and both original projections are preserved. Consequently the result gives a natural compatible-pair classification on ALL test schemes, including non-affine and nonreduced tests. For every map from an arbitrary scheme to the target open, its actual fiber product gives a smooth fppf cover and a lift into the original nowhere-zero parameter. Equality of normalized maps is unchanged by restriction to the target open, including the actual Cech pair.

This is NOT a cover of the coefficient base, NOT the varying Picard orbit-sheaf identification and NOT Picard/Jacobian representability. Cross-source comparison and global independent-envelope effectivity remain open joins. The raw norm factor 8 is unchanged. No Lean compiler, local/hosted Lean build, or kernel replay was run for this packet. Source/static checks and finite models are not kernel verification. Ancillary predecessor metadata not listed in this APPLICATION remains historical and is not a new acceptance claim.
''')
(p/'DERIVATION.md').write_text('''# Exact argument, original objects and boundary

1. The existing full quotient scalar action is natural in the named coefficient algebra map. The literal overlap quotient retains every defining equation, not just a radical. Compose its actual left/right quotient maps with the original coordinate-one slice maps.
2. Read ProjectiveParameterSliceLocalization.transition_point and ProjectiveKernelOverlapTransitions.transition_quotient. Together they identify the right original kernel point with the left point scaled by the inverse original transition coordinate. This is a specified genuine unit; the inverse orientation is not dropped.
3. The existing arbitrary-line whole-zero unit identity and exact affine factor criterion apply for every coefficient ring and its explicitly installed R action. Combine them with naturality to identify the two original nowhere-zero factorization predicates on the full overlap.
4. Every native residue-field test of that actual overlap is covered via Spec.preimage. The factorization comparison and literal Spec compositions give equality of the two pulled-back opens. This use of field tests detects open subschemes; it is not an identification of arbitrary reduced schemes.
5. The existing ambient intersection is categorical. Remove its common closed-immersion ambient map using the already existing MonicTargetPullback318.cancel theorem. The new cancellation wrapper explicitly credits that producer instead of duplicating its proof.
6. Form the union of the actual local open images in the existing glued normalized kernel. The exact overlap pullback lifts matching chart points; compatibility proves its restriction to each chart is exactly the old slice locus. Cover surjectivity gives uniqueness. Empty schemes, empty local opens, empty index sets and arbitrary non-finite covers are covered by the generic lemma.
7. On the actual full principal-source cover, the old normalization chart identity and the old principal-locus preimage identity identify the WHOLE preimage of the produced global target open with the original nowhere-zero source open. The old coefficient map is retained.
8. Lift the original nowhere-zero normalization through the target open. Its surjectivity follows from the old global normalization and the exact preimage equality, not from an assumed effective quotient. The source open range equals the precise target-open preimage. The open-immersion lift supplies the categorical universal property on all test schemes. Smoothness follows by base change; surjectivity and finite presentation give the fppf cover of this represented target open only.
9. Apply the actual pullback universal property to obtain a compatible-pair equivalence for every test scheme and prove naturality in both directions. Form the literal pullback of the produced cover along any target test to obtain its actual smooth surjective fppf local lift. The monomorphic target inclusion proves equality of relations on every Hom set and hence on the literal Cech pair. This does not yet identify that relation with the varying Picard orbit relation or represent its sheaf quotient.

Exact reused producers include the original quotient parameter, normalized full overlap rings and transition, finite-projective two-term presentation, original whole-zero schemes, native residue maps, glued kernel atlas, and original global normalization. The source-level boundary is extended beyond the predecessor's per-slice opens to a single global target open with its original-family fppf cover and arbitrary test pullbacks. No changed manuscript, accepted Lean manifest, kernel replay claim, or global arithmetic theorem is supplied.
''')
obs=[
('Actual quotient overlap and scalar','Both points and the scalar must be constructed on the full old quotient with correct transition orientation.','Literal left/right original kernel points and inverse coordinate unit; all-ring scalar naturality.','Quotient extensionality, original transition_point and transition_quotient identify the exact equation, including nilpotents.',new[:2]),
('All-ring original section compatibility','Use the original arbitrary line and every coefficient ring, not H1-vanishing or projective H0 substitutes.','Unit factor equivalence on the full normalized overlap with f.toAlgebra installed.','Old whole-zero unit equality preserves scheme structure and factorization in both directions.',[new[2]]),
('All-prime coverage','Every point of each actual overlap must be tested, with its induced coefficient action.','Spec.preimage constructs named R and rational actions for every field test.','Native residue fields and the actual factorization criterion detect equality of opens on the whole overlap.',[new[3]]),
('Exact atlas intersections','The local target charts must intersect inside the same glued kernel, not merely a related ambient space.','Cancel the existing common closed immersion from the actual ambient pullback.','Reuse MonicTargetPullback318.cancel, retaining the full universal property and both chart arrows.',[new[4],new[7]]),
('Global open and exceptional indices','All charts, overlaps, empty charts/schemes and arbitrary index sets must be covered.','Union of actual local open images, exact chart preimages and uniqueness.','Actual pullback point lifting plus joint cover surjectivity prove the two inclusions; no finite/nonempty index assumption is added.',[new[5],new[6],new[7]]),
('Original source and target identity','The global preimage must be the same whole original nowhere-zero source and retain its coefficient map.','Exact preimage equality on the old full principal cover; unique lift into the produced target open.','The literal original normalization chart and original projection identities identify the consumed maps.',[new[8],new[9]]),
('Genuine cover and universal property','Surjectivity and effectivity cannot be assumed as extra input; the square must be categorical on arbitrary tests.','Surjectivity from the full normalization, exact source range, open-lift pullback, smoothness by base change.','Every target point has an original source preimage in the exact open, and the open-immersion lift gives universal existence/uniqueness. This covers the target open only.',[new[9],new[10],new[11]]),
('All-scheme tests and base changes','Downstream tests include non-affine and nonreduced schemes and literal original maps.','Natural compatible-pair equivalence; arbitrary pullback smooth fppf cover and original-family lift.','Pullback Hom universal property and native smooth/surjective base-change theorems apply to the exact produced map; both projections are recorded.',[new[12],new[13],new[14]]),
('Relation identity and remaining consumer','Do not replace varying Picard effectivity by a represented normalized-kernel target.','Same-fiber equivalence for every test scheme and original Cech relation, with explicit remaining boundary.','Cancel only the actual monomorphic open inclusion. Orbit-sheaf identification, cross-source coherence, independent-envelope effectivity and Jacobian representation remain unproved here.',[new[15]])]
(p/'APPLICATION.md').write_text('# Application contract\n\n'+'\n\n'.join('## '+n+'\nRequires: '+r+'\nConstructs: '+c+'\nJustification: '+j for n,r,c,j,_ in obs)+'\n')
primary=p/'TARGET-OPEN-PRIMARY'
for name,source in {
 'OpenImmersion.lean':p/'RESIDUE-COVERAGE-PRIMARY/OpenImmersion.lean',
 'Smooth.lean':p/'RESIDUE-COVERAGE-PRIMARY/Smooth.lean',
 'HasPullback.lean':p/'RELATION-PRIMARY/HasPullback.lean.txt',
 'IsPullbackBasic.lean':ex/'pel-original-rosati-polarization-equivariance-r1/THETA-ZERO-PRIMARY/IsPullbackBasic.lean',
}.items(): shutil.copyfile(source,primary/name)
paths={
 'OpenImmersion.lean':'Mathlib/AlgebraicGeometry/OpenImmersion.lean',
 'Smooth.lean':'Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean',
 'UnderlyingMap.lean':'Mathlib/AlgebraicGeometry/Morphisms/UnderlyingMap.lean',
 'PullbackCarrier.lean':'Mathlib/AlgebraicGeometry/PullbackCarrier.lean',
 'HasPullback.lean':'Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean',
 'IsPullbackBasic.lean':'Mathlib/CategoryTheory/Limits/Shapes/Pullback/IsPullback/Basic.lean',
 'IsPullbackDefs.lean':'Mathlib/CategoryTheory/Limits/Shapes/Pullback/IsPullback/Defs.lean',
}
put('TARGET-OPEN-PRIMARY/SOURCES.json',{'mathlib_commit':'56a005855ea17e0b0958f73ec801ae140b0a1679','files':{n:{'path':path,'sha256':h(primary/n)} for n,path in paths.items()}})
rr=json.loads(subprocess.check_output([sys.executable,'-B',str(p/'regress_target_open.py')],text=True));put('TARGET-OPEN-REGRESSION.json',rr)
sys.path.insert(0,str(root/'scripts'));import audit_section_binders as ab
rows=[];unc=[]
for n in new:
 a,_,u=ab.scan((p/(n+'.lean')).read_text());rows.extend({'source':n+'.lean',**r} for r in a);unc.extend({'source':n+'.lean',**r} for r in u)
put('BINDER-ADVISORY.json',{'selftests':ab.selftest(),'candidates':rows,'unsupported':unc,'scope':'Lexical advisory only, not Lean elaboration'})
assert not rows and not unc,(rows,unc)
assert not any(l.rstrip()!=l for n in new for l in (p/(n+'.lean')).read_text().splitlines())
bind=['README.md','DERIVATION.md','APPLICATION.md','SOURCE-COPIES.json','COPY_BINDINGS.json','intake.json','MODULE_ORDER.txt','SOURCE_SHA256SUMS','REBUILD-NEW-SOURCES.json','regress_target_open.py','TARGET-OPEN-REGRESSION.json','BINDER-ADVISORY.json','TARGET-OPEN-PRIMARY/SOURCES.json']+['TARGET-OPEN-PRIMARY/'+n for n in paths]
put('APPLICATION.json',{'packet':p.name,'author':'picard_restart','status':'FRESH_RECONSTRUCTION_PENDING_REVIEW_KERNEL_PENDING','claim':'Actual global target-open descent, original-family Cartesian smooth fppf normalization and all-scheme test/base-change/relation identities; no varying Picard effectivity.','predecessor':old.name,'predecessor_application_sha256':h(old/'APPLICATION.json'),'new_sources':{n+'.lean':h(p/(n+'.lean')) for n in new},'sources':{n:v['sha256'] for n,v in files.items()},'bindings':{n:h(p/n) for n in bind},'obligations':[{'name':n,'required_input':r,'constructed_input':c,'justification':j,'source_references':[m+'.lean' for m in ms],'evidence':['README.md','DERIVATION.md','SOURCE-COPIES.json','TARGET-OPEN-PRIMARY/SOURCES.json']} for n,r,c,j,ms in obs],'local_lean_run':False,'hosted_lean_run':False,'historical_byte_recovery':False,'full_arithmetic_theorem_proved':False})
import check_progress_experiment as c
_,d,_,_=c.packet(p.name,c.ci.derive_plan(early_depth=7))
put('STRUCTURAL-CHECK.json',{'status':'PASS','modules':len(d['order']),'exact_predecessors':len(prev['files']),'new':len(new),'local_lean_run':False,'application_sha256':h(p/'APPLICATION.json'),'intake_sha256':h(p/'intake.json')})
publish=[str((p/n).relative_to(root)) for n in ['APPLICATION.json','STRUCTURAL-CHECK.json']+list(files)+bind]
(root/'recovery-tools/kernel-target-open-publication-paths.json').write_text(json.dumps(sorted(set(publish)),indent=2)+'\n')
print(json.dumps({'app':h(p/'APPLICATION.json'),'intake':h(p/'intake.json'),'modules':len(order),'new_lines':sum(len((p/(n+'.lean')).read_text().splitlines()) for n in new),'regression':rr}))
