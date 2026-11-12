from pathlib import Path
import hashlib,json,re,shutil
root=Path(__file__).resolve().parents[1]
base=root/'quartics/quartic-318-326/proof/experiments'
name='forward-actual-two-descent-original-infinity-square-rebuild-r1'
old=base/'forward-actual-two-descent-original-root-square-rebuild-r2';p=base/name
h=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
new=['ActualTwoDescentOpenChartCoefficientRebuild318','ActualTwoDescentOpenChartCoefficientCompatibilityRebuild318','ActualTwoDescentOriginalOverlapGenericCoefficientsRebuild318','ActualTwoDescentOriginalInfinityGenericIdentityRebuild318','ActualTwoDescentOriginalInfinityLocalFieldRebuild318','ActualTwoDescentOriginalInfinityNamedPoleRebuild318']
borrow=['DominantFunctionField318','AffineFunctionFieldMap318']
d=json.loads((old/'intake.json').read_text());order=d['order']+new
files={}
for n in order:
 f=p/(n+'.lean');files[f.name]={'sha256':h(f),'imports':re.findall(r'^(?:public )?import ([A-Za-z0-9_.]+)',f.read_text(),re.M)}
d.update(packet=name,order=order,files=files,new_modules=new,reused_modules=borrow)
(p/'intake.json').write_text(json.dumps(d,indent=2)+'\n')
inh={'predecessor':old.name,'predecessor_intake_sha256':h(old/'intake.json'),'exact_predecessor_sources':len(d['order'])-len(new),'new_sources':{n+'.lean':h(p/(n+'.lean')) for n in new},'borrowed_sources':{n+'.lean':{'source':'proof/progress/'+n+'.lean','sha256':h(base.parent/'progress'/(n+'.lean'))} for n in borrow},'historical_byte_recovery':False,'changed_predecessor_sources':[]}
(p/'SOURCE-COPIES.json').write_text(json.dumps(inh,indent=2)+'\n')
(p/'MODULE_ORDER.txt').write_text('\n'.join(order)+'\n')
(p/'SOURCE_SHA256SUMS').write_text(''.join(files[n+'.lean']['sha256']+'  '+n+'.lean'+'\n' for n in order))
primary=p/'INFINITY-SQUARE-REBUILD-PRIMARY';primary.mkdir(exist_ok=True)
for n in borrow:
 src=base.parent/'progress'/(n+'.lean');shutil.copy2(src,primary/src.name)
for n in ['OpenFunctionField318','ActualTwoDescentInfinityNativeFractionFunctions318','ActualTwoDescentOriginalTwoChartCubicScheme318','ActualTwoDescentOriginalOverlapQuotientMaps318']:
 src=p/(n+'.lean')
 if not src.exists():src=base.parent/'progress'/(n+'.lean')
 shutil.copy2(src,primary/(n+'.lean'))
ob=[
('Entire original generic carrier','Coefficients must live in the actual original scheme function field, not an unrelated rational model.','coefficient j is the inverse native open-immersion generic-stalk isomorphism applied to the native Spec coefficient. Its fraction_comparison and stalk_square fix all coefficients.'),
('Native transition direction','Affine refinement Spec(S) to Spec(R) is contravariant on coordinates.','Borrowed DominantFunctionField.map_comp and AffineFunctionFieldMap.on_coefficient give the whole generic square, after actual dense open immersions supply dominance.'),
('Complete overlap','The comparison must use the whole original D(y)=D(v) overlap.','commonChart is the literal intoInfinity followed by infinityChart. pushout.condition and actual_into_affine give both exact scheme-factor squares.'),
('Original constants and x','Constants and x must agree with the old named affine generic functions.','All affine and infinity coefficients pass through overlapCoefficientMap. The actual quotient map sends x to u/v and constants to the same constant; v times its inverse is the actual localization identity.'),
('Every root parameter','The root formula must hold for every a, not just test points or the three roots.','root_square proves named root(n,a)*native(v)=native(u-a*v) for all K-valued a, by the exact same generic maps.'),
('Denominator nonzero','Division by native v must be justified.','The native chart coefficient is injective by its exact affine fraction comparison. Existing original chart_v_nonzero then gives v_nonzero, without n nonzero.'),
('Actual marked infinity stalk','The local field comparison must extend the canonical original stalk equivalence.','comparison extends infinityEquiv through native fraction-ring structures, on_stalk retains its algebraMap square, and on_chart follows the newly rebuilt exact germ/coefficient square.'),
('Pole and unit normalization','The named original function must consume the old actual local unit calculation.','named_root identifies the original generic root with infinityAffineX minus the old local constant. normalization then retains the exact e,d units, u cube for v, and nonzero d/e multiplying the double pole.'),
('Historical and verification boundary','Fresh source must not inherit lost approval or imply global divisor/theta results.','All 1312 predecessor sources are unchanged, including the separately reviewed ThreePole repair. Two borrowed baseline modules are credited byte-exact. Six fresh modules require independent review and hosted kernel replay. All-point support, associated sheaf, translations and theta/Weil identification are not concluded.')
]
doc='# Fresh original infinity field compatibility\n\n'+ '\n\n'.join('## '+str(i+1)+'. '+t+'\n\nRequired: '+r+'\n\nConstructed and justification: '+j for i,(t,r,j) in enumerate(ob))+'\n'
(p/'DERIVATION.md').write_text(doc)
(p/'README.md').write_text('# Original infinity square reconstruction\n\nSix fresh modules identify the SAME original scheme-generic root with its actual infinity-local fraction expression and the earlier unit-normalized double pole. The complete overlap is the actual native scheme pushout overlap. No replacement model or pointwise test substitutes for its map square.\n\nTwo existing baseline generic-map modules are reused byte-exact and credited. This is fresh reconstruction, not recovered historical source or inherited acceptance. No local Lean run. Hosted replay and distinct review remain pending.\n')
(p/'GLOBAL-THEOREM-AUDIT.md').write_text('# Remaining scope\n\nThis packet proves an exact named-function local comparison, conditional only on the stated field and characteristic-zero structure. It does not construct a native principal-divisor homomorphism, an associated-divisor sheaf identification, global translation, theta group, Weil pairing, Cassels–Tate pairing, or rank proof. Actual all-point off-support units are the next join. Structural admission is not kernel validation.\n')
ev=['check_infinity_generic_rebuild.py','README.md','DERIVATION.md','GLOBAL-THEOREM-AUDIT.md','SOURCE-COPIES.json','MODULE_ORDER.txt','SOURCE_SHA256SUMS','intake.json']+[str(q.relative_to(p)) for q in primary.glob('*')]+[str(q.relative_to(p)) for q in (p/'ROOT-SQUARE-REBUILD-PRIMARY').glob('*')]+[str(q.relative_to(p)) for q in (p/'THREE-POLE-AUDIT-REPAIR').glob('*') if q.is_file()]
app={'author':'/root/advance_global_arithmetic','status':'PENDING_DISTINCT_REVIEW_AND_HOSTED_CHECK','claim':'Exact whole native overlap comparison, same named original root in actual infinity-local fraction field, and its old actual unit-normalized double pole.','sources':{n+'.lean':files[n+'.lean']['sha256'] for n in order},'bindings':{f:h(p/f) for f in ev},'obligations':[{'name':str(i+1),'required_input':r,'constructed_input':t,'justification':j,'source_references':[n+'.lean' for n in new+borrow],'evidence':['DERIVATION.md','SOURCE-COPIES.json']} for i,(t,r,j) in enumerate(ob)],'local_lean_run':False,'full_arithmetic_theorem_proved':False}
(p/'APPLICATION.json').write_text(json.dumps(app,indent=2)+'\n')
for f in old.glob('*.lean'):assert f.read_bytes()==(p/f.name).read_bytes()
print('APP',h(p/'APPLICATION.json'),'INTAKE',h(p/'intake.json'),'ORDER',len(order),'EXACT',len(list(old.glob('*.lean'))))
