from pathlib import Path
import json,hashlib,shutil
r=Path(__file__).resolve().parent;root=r.parent;repo=root/'pel-integration43597228569/repo';ex=repo/'quartics/quartic-318-326/proof/experiments';old='height-normalized-valuative-center-r68';new='height-normalized-valuative-center-r69';mod='IntegralOriginalBicanonicalRestrictions318';head='57227e167abe49436d651b932ff75d5bdf9b5898';c=r/'candidates';p=r/'successors'/new;H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();W=lambda p,d:p.write_text(json.dumps(d,indent=2)+'\n');tag='HOSTED-43603177874'
res=json.loads((c/'CENTER-RESULT.json').read_text());assert res['packet']==old and res['packet_sha256']==H(ex/old/'intake.json') and res['commands'][-1]['module']==mod and res['commands'][-1]['exit_code']==1
shutil.copytree(ex/old,p);hist=p/'inherited-metadata'/old;hist.mkdir(parents=True)
for q in list(p.iterdir()):
 if q.is_file() and q.suffix!='.lean':shutil.move(str(q),hist/q.name)
d=json.loads((hist/'intake.json').read_text());d.update(packet=new,status='UNACCEPTED_HOSTED_EXPERIMENT',revision_classification_schema=1,revision_of=old);shutil.copy2(c/(mod+'.lean'),p/(mod+'.lean'));d['files'][mod+'.lean']['sha256']=H(p/(mod+'.lean'))
rev=[n for n in d['order'] if (p/(n+'.lean')).read_bytes()!=(ex/old/(n+'.lean')).read_bytes()];reuse=[n for n in d['order'] if n not in rev];assert rev==[mod] and len(reuse)==95;d.update(new_modules=[],revised_modules=rev,reused_modules=reuse,unchanged_predecessor_modules=reuse);W(p/'intake.json',d)
oldh={n+'.lean':H(ex/old/(n+'.lean')) for n in d['order']};newh={n+'.lean':H(p/(n+'.lean')) for n in d['order']};W(p/'INHERITANCE.json',{'predecessor':old,'predecessor_commit':head,'unchanged_sources':95,'changed_sources':{mod+'.lean':newh[mod+'.lean']},'old_sources':oldh,'new_sources':newh});(p/'MODULE_ORDER.txt').write_text('\n'.join(d['order'])+'\n');(p/'SOURCE_SHA256SUMS').write_text(''.join(h+'  '+n+'\n' for n,h in newh.items()))
ob=[
('required_inputs','Open-immersion instances attached to exact morphisms and complete chart route equalities.','Abstract imageLE_of_route substitutes the route target before applying original imageLE; spec_algEquiv_open supplies the exact native Spec.map instance.','Handles proof dependency without replacing the morphism or adding geometry assumptions.'),
('constructed_objects','The same original tensor sheaf and J²-scaled global pair, actual integral branch and infinity formulas.','branchQ, infinityQ, originalQ, branch_route and infinity_route remain unchanged.','Two exported abstract helper theorems added; no old theorem statement modified.'),
('index_and_domain_coverage','Every c, all four branch indices, both sections and the entire infinity chart.','Original full open-image inequalities and restriction conclusions preserved.','No generic-point, smaller dense-open, selected root or reduced index family substituted.'),
('transition_maps','Exact algebra equivalences and their contravariant Spec maps; true presheaf restriction of differential tensor sections.','Each restriction installs the same map instance and calls unchanged weightedSquare_restrict_to with original route.','No alternate scalar structure, chart isomorphism or normalization map.'),
('scalars_and_signs','Original J² and exact branch/infinity coefficients and universal differentials.','All coefficient and differential rewrites and section identities remain byte-identical.','No unit assumption, factor cancellation or resource/limit change.'),
('consumer_identity','IntegralOriginalGlobalPair consumes these same weighted original restrictions.','Actual branch and infinity restriction statements unchanged, on their whole original chart domains.','A helper proof transport is not replacement with coefficient equality alone.'),
('exceptional_cases','All original unit parameters and chart hypotheses, including both n cases.','No additional excluded point, denominator or genericity condition.','No new axiom, admission, unchecked shortcut or scratch endpoint promoted.'),
('downstream_and_history','Own r68 run43603177874/head57227e and exact96-root predecessor.','FiveChartGeometry passes13.899s; BicanonicalRestrictions fails9.386s on exact dependent rewrite/instance errors.','One of96 source files changes,95 exact reused; earlier passes are corroboration, not this candidate acceptance.'),
('verification_boundary','Independent source, current contract/propagation review and hosted kernel replay.','Exact own artifact/RESULT/log/before, primaries and independent source review retained; static checks only.','No local Lean; full module, packet and arithmetic theorem unproved. Common diagnostic-only tooling stays separate.')]
obs=[{'id':i,'required_input':q,'constructed_input':s,'justification':j,'source_refs':[mod+'.lean','IntegralOriginalGlobalPair318.lean',tag+'/primary/IntrinsicTensorChartSections318.lean'],'evidence':[tag+'/center-RESULT.json',tag+'/'+mod+'.log'],'independent_review':'CURRENT_CONTRACT_REVIEW_PENDING'} for i,q,s,j in ob]
readme=f'''# Preserve complete original bicanonical chart restrictions

Successor of `{old}` at `{head}`. Own hosted run43603177874 verifies FiveChartGeometry PASS13.899s and then BicanonicalRestrictions FAIL9.386s. The new failure consists of dependent open-image rewrite motives and missing IsOpenImmersion instances for the exact algebra-equivalence spectrum maps.

Two abstract helper theorems are added: route substitution before the original imageLE, and the native open-immersion instance for Spec.map of an algebra equivalence. They are specialized only inside the existing complete branch/infinity restriction proofs. All old statements, definitions, maps, full chart domains, coefficients, differentials, J² scaling, imports and options remain unchanged.

Exactly1 of96 modules changes,95 reused. Source review is not hosted compilation or whole-packet acceptance. No local Lean. Common observer tooling is separate and makes no production-source change.

## Nine application obligations
'''
readme+='\n'.join(f'{i+1}. **{k}.** Required: {q} Constructed: {s} Justification: {j}\n' for i,(k,q,s,j) in enumerate(ob));(p/'README.md').write_text(readme)
e=p/tag;e.mkdir();shutil.copytree(c/'primary',e/'primary')
for n in [mod+'.before',mod+'.diff',mod+'-REPAIR.json',mod+'.log']:shutil.copy2(c/n,e/n)
shutil.copy2(c/'CENTER-RESULT.json',e/'center-RESULT.json')
for n in ['ARTIFACT.json','artifact.zip']:shutil.copy2(r/'evidence/center'/n,e/n)
W(p/'HOSTED_REPAIR.json',{'packet':new,'predecessor':old,'run':43603177874,'head':head,'changed_sources':[mod+'.lean'],'source_review':'PENDING','propagation_review':'PENDING','hosted_replay':'PENDING','local_lean_run':False})
W(p/'SOURCE_VALIDATION.json',{'packet':new,'predecessor':old,'base_head':head,'closure_modules':96,'changed_sources':{mod+'.lean':newh[mod+'.lean']},'public_statement_exception':None,'new_helper_declarations':['imageLE_of_route','spec_algEquiv_open'],'source_review':'PENDING','propagation_review':'PENDING','hosted_replay':'PENDING','local_lean_run':False,'full_arithmetic_theorem_proved':False})
a={'packet':new,'predecessor':old,'author':'geometry_repair_resume','producer':'geometry_repair_resume','status':'SOURCE_REVIEW_AND_CURRENT_CONTRACT_REVIEW_PENDING','intake_sha256':H(p/'intake.json'),'contract':'README.md','contract_sha256':H(p/'README.md'),'obligations':obs,'sources':newh,'mathlib_commit':'56a005855ea17e0b0958f73ec801ae140b0a1679','local_lean_run':False,'full_arithmetic_theorem_proved':False}
a['bindings']={n:H(p/n) for n in ['README.md','intake.json','INHERITANCE.json','MODULE_ORDER.txt','SOURCE_SHA256SUMS','HOSTED_REPAIR.json','SOURCE_VALIDATION.json',mod+'.lean']};a['bindings'].update({str(f.relative_to(p)):H(f) for f in e.rglob('*') if f.is_file()});W(p/'APPLICATION.json',a)
shutil.copy2(p/'APPLICATION.json',p/'SOURCE-REVIEW-INPUT-APPLICATION.json')
mp=root/'review43603177874/BICANONICAL-SOURCE-BINDINGS.json';m=json.loads(mp.read_text());assert H(mp)=='27eef8c62c42fabeefb66177691f1b617cfefd11ba1f10371edf55a90463ca18';files=dict(m['source_bindings']);files['review43603177874/BICANONICAL-SOURCE-REVIEW.md']=m['report_sha256'];files[str(mp.relative_to(root))]=H(mp)
for n,h in files.items():
 q=root/n;assert H(q)==h,n;dest=p/'SOURCE-REVIEW'/n;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(q,dest);a['bindings'][str(dest.relative_to(p))]=h
for f in ['HOSTED_REPAIR.json','SOURCE_VALIDATION.json']:
 q=json.loads((p/f).read_text());q['source_review']='PASS_SOURCE_ONLY_NOT_HOSTED';W(p/f,q);a['bindings'][f]=H(p/f)
a['status']='SOURCE_REVIEWED_CURRENT_CONTRACT_PROPAGATION_AND_HOSTED_PENDING';a['bindings']['SOURCE-REVIEW-INPUT-APPLICATION.json']=H(p/'SOURCE-REVIEW-INPUT-APPLICATION.json');a['source_review']={'reviewer':'lean_review_resume','report':'SOURCE-REVIEW/review43603177874/BICANONICAL-SOURCE-REVIEW.md','report_sha256':m['report_sha256'],'bindings':'SOURCE-REVIEW/review43603177874/BICANONICAL-SOURCE-BINDINGS.json','bindings_sha256':H(mp),'scope':'Source-only; current contract and propagation pending','kernel_acceptance':False};W(p/'APPLICATION.json',a)
for n,h in a['bindings'].items():assert H(p/n)==h,n
W(r/'PAIRS.json',[{'predecessor':old,'packet':new,'changed_modules':[mod]}]);print(json.dumps({'packet':new,'intake':H(p/'intake.json'),'README':H(p/'README.md'),'APPLICATION':H(p/'APPLICATION.json'),'source':H(p/(mod+'.lean'))},indent=2))
