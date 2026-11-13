from pathlib import Path
import json,hashlib,re,shutil
root=Path(__file__).resolve().parents[1];b=root/'quartics/quartic-318-326/proof/experiments';p=b/'forward-actual-two-descent-original-rational-value-rebuild-r1';old=b/'forward-actual-two-descent-original-local-fractional-sheaf-rebuild-r1';h=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
new=['ActualTwoDescentOpenRationalEvaluationRebuild318','ActualTwoDescentPushforwardRationalValueRebuild318','ActualTwoDescentOriginalGlobalRationalValueRebuild318','ActualTwoDescentOriginalOverlapRationalFrameRebuild318','ActualTwoDescentOpenAdjointSectionsRebuild318','ActualTwoDescentOriginalRationalRestrictionSquareRebuild318','ActualTwoDescentOriginalRationalAdditiveImageRebuild318','ActualTwoDescentOriginalOverlapValueImageRebuild318','ActualTwoDescentOriginalRationalImageBoundRebuild318']
d=json.loads((old/'intake.json').read_text());oldorder=d['order'][:];d.update(packet=p.name,order=oldorder+new,new_modules=new,reused_modules=[]);d['files']={n+'.lean':{'sha256':h(p/(n+'.lean')),'imports':re.findall(r'^(?:public )?import ([A-Za-z0-9_.]+)',(p/(n+'.lean')).read_text(),re.M)} for n in d['order']}
for n in oldorder:assert (old/(n+'.lean')).read_bytes()==(p/(n+'.lean')).read_bytes(),n
(p/'intake.json').write_text(json.dumps(d,indent=2)+'\n');(p/'MODULE_ORDER.txt').write_text('\n'.join(d['order'])+'\n');(p/'SOURCE_SHA256SUMS').write_text(''.join(v['sha256']+'  '+k+'\n' for k,v in d['files'].items()))
inh={'predecessor':old.name,'predecessor_intake_sha256':h(old/'intake.json'),'exact_predecessor_sources':len(oldorder),'new_sources':{n+'.lean':h(p/(n+'.lean')) for n in new},'historical_byte_recovery':False,'changed_predecessor_sources':[],'recovered_unpublished_draft_sources':4,'newly_extended_sources':5,'draft_repair':'Use Scheme.Modules.Hom.app_smul: native Hom.app takes values in Ab, so its hom is not a ModuleCat linear map.'};(p/'SOURCE-COPIES.json').write_text(json.dumps(inh,indent=2)+'\n')
pr=p/'RATIONAL-VALUE-REBUILD-PRIMARY';pr.mkdir(exist_ok=True)
for n in ['ActualTwoDescentOriginalDegreeZeroIdealSheaf318','ActualTwoDescentOriginalIdealOverlapValues318','ActualTwoDescentOriginalOverlapOldFrameComparison318','ActualTwoDescentOriginalInverseInfinityTransition318','ActualTwoDescentOriginalIntegralSchemeRebuild318']:
 shutil.copy2(p/(n+'.lean'),pr/(n+'.lean'))
for n in ['OpenFunctionField318','ClutchedModule318']:
 shutil.copy2(root/'quartics/quartic-318-326/proof/progress'/(n+'.lean'),pr/(n+'.lean'))
shutil.copy2(b/'pel-original-algebraic-hyperplane-atlas-r2/HYPERPLANE-PRIMARY/FunctionField.lean',pr/'FunctionField.lean')
shutil.copy2(p/'IDEAL-OVERLAP-PRIMARY/Presheaf.lean',pr/'Presheaf.lean');shutil.copy2(p/'IDEAL-AFFINE-SQUARE-PRIMARY/Sheaf.lean',pr/'ModulesSheaf.lean')
ob=[
('source_hypotheses','Native generic-field transport requires integral source/target and nonempty opens.','The actual original integrality producer is used. The generic point proves the whole preimage of every nonempty ambient open is nonempty. The inverse actual open-immersion generic-stalk equivalence, not an arbitrary field isomorphism, defines evaluation.'),
('constructed_objects','Values must be defined on the original global root ideal sheaf.','coefficientMap is the actual old affineProjection composed with affineIdealRestriction. The common-chart local value uses the old affineValue and actual common-chart generic field.'),
('index_domain_coverage','Comparison must cover every section over every nonempty ambient open, not only top, generators, or marked points.','OpenAdjointSections restrictSection is the actual adjunction unit at arbitrary U. Its formula is exactly M.presheaf.map(image_preimage_le). adjoint_apply evaluates the native homEquiv_unit equality at every section. value_square specializes this whole square to the original sheaf.'),
('transition_maps','Native module restriction and scalar maps must remain intact.','PushforwardRationalValue uses forward PresheafOfModules.naturality_apply and native Hom.app_smul. The pushforward scalar is j.app(U)(a), then ambient generic-field compatibility gives multiplication by the original ambient germ. The prior draft mistakenly invoked map_smul on an Ab map and has been corrected before review.'),
('limiting_object_identity','Separate global and overlap values must be identified by an actual native square.','coefficient_square uses the exact old affineValue adjunction and coefficientMap, without an added compatibility hypothesis. value_square identifies generic values after that exact native restriction; eq_iff_section uses the already-produced actual overlap frame injection.'),
('coefficient_conventions','The inverse-u factor, its restriction, and the old frame must be retained.','OriginalOverlapRationalFrame.infinity_formula preserves the literal restricted inverseUSection and actual field maps. No sign is changed and no abstract generator is substituted.'),
('local_conditions','Full overlap image must not follow merely from injection or a chosen scalar.','OverlapValueImage.full_image uses the bijectivity of the actual old affineValue component on each nonempty common-chart open. Thus every regular-function germ occurs, and only such germs occur. RationalImageBound transports each actual global value into this entire overlap regular image.'),
('exceptional_cases','Do not assert a value on an empty open or discard the n=0 case silently.','Every rational-value statement explicitly requires Nonempty U; no totalization on empty opens is claimed. The generic-field and overlap statements add no n nonzero condition. Existing root-principal or nonsingularity statements in the predecessor retain their own n nonzero hypotheses.'),
('downstream_consumption','Do not turn overlap injection into global sheaf embedding or global lattice exhaustion.','AdditiveImage records a genuine range, additive structure, ambient scalar closure and literal image inclusions under restriction. injective_iff_restriction exposes exactly the remaining global restriction injectivity obligation. Global full image, root/infinity intrinsic-stalk identity, associated-divisor/theta/Weil, empty-open packaging and kernel elaboration remain open.')]
(p/'DERIVATION.md').write_text('# Native all-open rational values and exact restriction join\n\n'+'\n\n'.join('## '+str(i+1)+'. '+t+'\n\nRequired: '+r+'\n\nConstructed: '+j for i,(t,r,j) in enumerate(ob))+'\n')
(p/'README.md').write_text('''# Original native rational-section reconstruction and restriction join

Nine fresh sources above 1,337 exact predecessor sources. Four recovered unpublished draft modules are retained with one native scalar-API correction; five further modules close the exact all-open global/local rational-value square and produce the full overlap regular image.

The existing original global root ideal sheaf has a canonical value for every section over every nonempty ambient open, using its old common-chart coefficient map and the actual generic-stalk equivalence. Restriction and ambient scalar laws are preserved. The actual old pullback square gives its infinity expression with the literal inverse-u factor.

The native adjunction unit is now evaluated on EVERY ambient open and every section, not merely top or selected generators. Consequently the global value is exactly the old overlap frame value of the native restricted section. Equality of global values is equivalent to equality of those native restricted sections. On every nonempty common-chart subopen, the entire frame-value image is exactly the regular-function image in the original field, by the old actual frame's surjectivity.

Actual global value ranges form additive subgroups, are closed under the original ambient regular scalar action, and include into one another under restriction. Every such value lies in the full regular image on the overlap preimage.

This does NOT prove global restriction injectivity, global full-image exhaustion, identification of intrinsic germs with all local fractional lattices, associated-divisor or theta/Weil comparison. The exact remaining injectivity equivalence is recorded, not assumed away. No empty-open totalization, local Lean run or recovered historical acceptance is claimed. Source review and hosted/kernel validation are separate.
''')
(p/'GLOBAL-THEOREM-AUDIT.md').write_text('''# Completed join and remaining obligations

Completed in source: the native restriction-unit section square identifies the separately constructed global and local overlap rational values, on every nonempty ambient open and every section. The full local overlap image is produced from the old frame bijection. This is a genuine join absent from the four-module draft.

Still open: prove injectivity of restriction of the entire original global ideal sheaf to the common-chart preimage, rather than assume it. Prove the full global value image from both chart conditions, not only containment in the overlap regular image. Compare intrinsic original stalk germs with the chosen local spectra and their yR / inverse-u R fractional modules. Build the associated-divisor sheaf and identify the normalized theta/Weil object. Empty opens require separate sheaf packaging.

The new injective_iff_restriction statement is an exact characterization of the remaining obligation, not a proof that it holds. The inherited global arithmetic theorem and formal Lean acceptance have not been established by this batch.
''')
# Structural evidence only; a parser/elaborator was not run.
idx={n:i for i,n in enumerate(d['order'])};checks=[]
for n in new:
 s=(p/(n+'.lean')).read_text();assert not re.search(r'\b(sorry|admit|axiom)\b',s),n
 for imp in d['files'][n+'.lean']['imports']:
  if imp in idx:assert idx[imp]<idx[n],(n,imp)
 checks.append({'module':n,'lines':len(s.splitlines()),'sha256':h(p/(n+'.lean'))})
(p/'RATIONAL-JOIN-STRUCTURAL.json').write_text(json.dumps({'status':'PASS_SOURCE_BINDINGS_AND_IMPORT_ORDER_ONLY','sources':len(d['order']),'exact_predecessor_sources':len(oldorder),'new_modules':checks,'lean_run':False,'proof_acceptance':False},indent=2)+'\n')
ev=['README.md','DERIVATION.md','GLOBAL-THEOREM-AUDIT.md','SOURCE-COPIES.json','MODULE_ORDER.txt','SOURCE_SHA256SUMS','intake.json','RATIONAL-JOIN-STRUCTURAL.json']+[str(q.relative_to(p)) for q in pr.glob('*')]
a={'author':'/root/arithmetic_restart (extension and scalar repair); /root/advance_global_arithmetic (recovered four-module draft)','status':'PENDING_DISTINCT_REVIEW_AND_HOSTED_CHECK','claim':'Native all-nonempty-open global rational values, exact original native restriction-unit value square, full common-chart regular image, genuine additive/scalar value ranges and explicit remaining global injectivity obligation.','sources':{k:v['sha256'] for k,v in d['files'].items()},'bindings':{f:h(p/f) for f in ev},'obligations':[{'name':t,'required_input':r,'constructed_input':j,'justification':j,'source_references':[n+'.lean' for n in new],'evidence':['DERIVATION.md','SOURCE-COPIES.json']} for t,r,j in ob],'local_lean_run':False,'full_arithmetic_theorem_proved':False};(p/'APPLICATION.json').write_text(json.dumps(a,indent=2)+'\n')
print('APP',h(p/'APPLICATION.json'),'INTAKE',h(p/'intake.json'),'ORDER',len(d['order']),'EXACT',len(oldorder),'NEW',len(new))
