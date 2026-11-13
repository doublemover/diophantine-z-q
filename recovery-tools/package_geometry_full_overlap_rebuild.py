from pathlib import Path
import json,hashlib,re,shutil,sys
r=Path(__file__).resolve().parents[1]
b=r/'quartics/quartic-318-326/proof/experiments'
q=b/'height-original-normal-overlap-model-maps-rebuild-r1';p=b/'height-original-normal-full-overlap-rebuild-r1'
h=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
def dump(f,x): f.write_text(json.dumps(x,indent=2)+'\n')
names=['NormalizationClosureChartRange318','OriginalNormalChartRanges318','OriginalNormalTwoChartCover318','IntegralJLineOverlapOpen318','OriginalNormalFullOverlap318']
d=json.loads((q/'intake.json').read_text());prior=list(d['order'])
for n in prior:
 assert (p/(n+'.lean')).read_bytes()==(q/(n+'.lean')).read_bytes()
for n in names:
 d['order'].append(n);d['files'][n+'.lean']={'sha256':h(p/(n+'.lean')),'imports':re.findall(r'^public import ([A-Za-z0-9_.]+)',(p/(n+'.lean')).read_text(),re.M)}
d.update(packet=p.name,status='PENDING_FRESH_DISTINCT_REVIEW_NOT_LEAN_VALIDATED',new_modules=names,revised_modules=[],reused_modules=prior,unchanged_predecessor_modules=prior)
dump(p/'intake.json',d)
hist=p/'INHERITED-METADATA';hist.mkdir(exist_ok=True)
for n in ['intake.json','APPLICATION.json','APPLICATION.md','README.md','INHERITANCE.json']:
 shutil.copy2(q/n,hist/n)
review=r/'quartics/quartic-318-326/proof/independent-reviews/resume-20261112/normal-overlap-model-maps-rebuild-review.json'
shutil.copy2(review,hist/review.name)
prim=p/'FULL-OVERLAP-PRIMARY';prim.mkdir(exist_ok=True)
loc={
 'OpenImmersion.lean':b/'height-original-normal-native-dual-restriction-rebuild-r1/NATIVE-RESTRICTION-PRIMARY/OpenImmersion.lean',
 'PrimeTopology.lean':q/'MODEL-MAPS-PRIMARY/PrimeTopology.lean',
 'AffineScheme.lean':b/'height-original-normal-model-identification-r1/PRIMARY/Mathlib__AlgebraicGeometry__AffineScheme.lean',
}
for n in ['JLineAtlas318','JLineOverlapOpen318','ProjectiveLineOverlap318','ContactFullOverlap318','InfinityGlobalScheme318','NormalizationBaseCompatibility318']:
 loc[n+'.lean']=r/'quartics/quartic-318-326/proof/progress'/ (n+'.lean')
for n,f in loc.items():shutil.copy2(f,prim/n)
dump(p/'PRIMARY-PROVENANCE.json',{'source':'Exact surviving primary/source bytes; no fresh native fetch or Lean run claimed. OpenImmersion and PrimeTopology inherited from pinned 56a005855ea17e0b0958f73ec801ae140b0a1679 packets. AffineScheme inherited from the named normal-model-identification packet.','files':{n:{'source':str(f.relative_to(r)),'sha256':h(f)} for n,f in loc.items()}})
dump(p/'INHERITANCE.json',{'predecessor':q.name,'predecessor_intake_sha256':h(q/'intake.json'),'predecessor_application_sha256':h(q/'APPLICATION.json'),'predecessor_source_review_sha256':h(review),'unchanged_sources':len(prior),'revised_sources':{},'new_sources':{n+'.lean':h(p/(n+'.lean')) for n in names},'old_sources':{n+'.lean':h(q/(n+'.lean')) for n in prior},'historical_status':'Fresh continuation. Prior review is scoped source review, not Lean validation; no lost acceptance reused.'})
(p/'SOURCE_SHA256SUMS').write_text(''.join(h(p/(n+'.lean'))+'  '+n+'.lean\n' for n in d['order']))
(p/'MODULE_ORDER.txt').write_text('\n'.join(d['order'])+'\n')
ob=[
('source_hypotheses','Use the actual normalization section-equivalence chart, not arbitrary open charts with merely dense agreement.','NormalizationClosureChartRange318.range unfolds the OLD data constructor: a Spec isomorphism followed by the affine preimage fromSpec. Exact opensRange_comp_of_isIso and opensRange_fromSpec give the full inverse image.','NormalizationClosureChartRange318.lean; FULL-OVERLAP-PRIMARY/AffineScheme.lean; FULL-OVERLAP-PRIMARY/OpenImmersion.lean'),
('constructed_objects','Preserve both original normal orders, charts, projection and the same proper-normal realization M.','OriginalNormalChartRanges318 consumes the OLD canonicalData for both charts and transports its exact range through OriginalNormalModelCanonicalIso318.iso, using the existing projection compatibility. The finite polynomial-action equality is transported exactly as in the old constructor.','OriginalNormalChartRanges318.lean; OriginalNormalOrderChart318.lean; OriginalNormalInfinityChart318.lean; OriginalNormalModelCanonicalIso318.lean'),
('index_domain_coverage','Cover all points of M, including vertical points and every finite place.','Each chart range is the entire inverse image of the corresponding standard projective-line chart. JLineAtlas318.standard_opens_cover proves joint surjectivity. The native OpenCover uses these same two maps, and every point of the existing center is covered. No pointwise coverage is upgraded to factorization of the whole center through one chart.','OriginalNormalTwoChartCover318.lean; OriginalNormalChartRanges318.lean; FULL-OVERLAP-PRIMARY/JLineAtlas318.lean'),
('transition_maps','Identify the FULL intersection with the actual old normal-order localizations and correct reciprocal variance.','IntegralJLineOverlapOpen318 generalizes both surviving projective-chart preimage proofs from Q to any commutative ring. OriginalNormalFullOverlap318 proves the old infinity localization image is exactly D(S), pulls back the full finite chart using the old infinity projection square, and applies native IsOpenImmersion.isPullback. The first leg is j followed by finite i, where j is Spec of the accepted overlap ring equivalence; the second is the old infinity k.','IntegralJLineOverlapOpen318.lean; OriginalNormalFullOverlap318.lean; OriginalNormalOverlapChartEquality318.lean; FULL-OVERLAP-PRIMARY/OpenImmersion.lean'),
('limiting_object_identity','Do not substitute a generic model, abstract localization, or unbranched source for the model intersection.','The pullback lands in the original M.scheme and uses precisely OriginalNormalOrderChart318.chart and OriginalNormalInfinityChart318.chart. The source is the entire InfinityOverlap integral closure, not SourceOpenRing. The actual range intersection is the old composite k followed by the old infinity chart.','OriginalNormalFullOverlap318.lean; OriginalNormalOverlapChartMaps318.lean; OriginalNormalOverlapOrderLocalization318.lean'),
('coefficient_conventions','Retain finite and reciprocal polynomial actions, original coefficients and differential convention.','The infinity basic-open element is literally OriginalNormalInfinityOrder318.polynomialScalar X, with infinityNormalAlgebra and infinity_localization installing the old reciprocal action. No dual transition is changed: the exact inherited -T^2 reciprocal correction remains in localDual. Coverage alone does not identify localDual with a global dualizing object.','OriginalNormalFullOverlap318.lean; OriginalNormalOverlapNativeComparison318.lean; OriginalNormalReciprocalDualTransition318.lean'),
('local_conditions','Use a complete principal localization, not a punctured subset inferred from density.','The proof invokes the prior integral-closure principal-localization theorem through infinity_localization and native PrimeSpectrum.localization_away_comap_range. This is equality of full open subsets, hence native categorical pullback, not only agreement on field-valued points.','OriginalNormalFullOverlap318.lean; IntegralClosurePrincipalLocalization318.lean; FULL-OVERLAP-PRIMARY/PrimeTopology.lean'),
('exceptional_cases','Do not remove bad primes or assert regularity from normality.','All c,t,w,D,M from OriginalAllPlaceNormalModel318 are retained. No additional noncontact, good-reduction, scalar-unit, freeness, regularity or branch-denominator inversion premise is added. Normalization already supplies the same entire charts at bad primes; the overlap only inverts the relevant base coordinate.','OriginalNormalChartRanges318.lean; OriginalNormalTwoChartCover318.lean; OriginalNormalFullOverlap318.lean'),
('downstream_consumption','Record exactly which global duality obligations this removes and which remain.','The prior native comparison now has the actual full categorical intersection as domain, and both full normal charts cover M. Effective descent of the local dual modules, ambient trace/differential coherence, identification with a dualizing/Hodge object, regular-model comparison and discrepancy remain unproved. This packet does not alter the canonical 2,000-module audit replay.','README.md; OriginalNormalFullOverlap318.lean; OriginalNormalOverlapNativeComparison318.lean')]
(p/'APPLICATION.md').write_text('# Full original normal-chart coverage and intersection\n\n'+'\n\n'.join(f'## {i}. {n}\n\nRequired: {req}\n\nConstructed and justified: {got}\n\nSources: {src}' for i,(n,req,got,src) in enumerate(ob,1))+'\n')
(p/'README.md').write_text('''# Whole normal-chart cover and full categorical overlap

Five fresh source modules on 1,540 byte-exact predecessors. The preceding five-source model-map packet has a distinct scoped source review; neither it nor this continuation is claimed Lean-validated.

The actual old finite and infinity normalization charts now have exact ranges: the full inverse images of the two standard projective-line charts under the SAME original M.projection. The proof reads the actual section-equivalence construction, rather than inferring surjectivity from density. Transport uses the existing canonical-model isomorphism and its base square.

These same charts give a native two-chart OpenCover of M, including every vertical/bad-prime point and every point of the already-constructed valuative center. This is pointwise center coverage, not a factorization of its entire valuation-ring morphism through one chart.

The rational standard-chart overlap proofs are generalized over an arbitrary commutative coefficient ring. The prior infinity principal-localization theorem then identifies the full chart intersection with the actual entire reciprocal normal overlap. Native IsOpenImmersion.isPullback supplies the categorical intersection with the original exact localization maps. It is not the smaller unbranched source.

This removes the chart-coverage and full-intersection boundary from the preceding local-dual comparison. It does not glue those modules, prove ambient trace/differential coherence, identify a dualizing/Hodge object, prove regularity, or calculate discrepancy. The existing reciprocal differential factor remains unchanged. The canonical audit replay is untouched.

Historical comparison: the actual surviving InfinityGlobalScheme318 range proof, both ProjectiveLineOverlap318/JLineOverlapOpen318 rational preimage proofs, and ContactFullOverlap318 native full-intersection method were read and adapted to the literal all-place normal orders. No lost historical acceptance is reused. No cloud Lean, local Lean, hosted Lean or new resource options were run/added.
''')
(p/'DRAFT-STATUS.md').write_text('Frozen five fresh sources; distinct source review pending. No Lean run or kernel acceptance.\n')
bind={str(f.relative_to(p)):h(f) for root in [prim,hist] for f in root.iterdir() if f.is_file()}
for n in ['README.md','APPLICATION.md','INHERITANCE.json','PRIMARY-PROVENANCE.json','SOURCE_SHA256SUMS','MODULE_ORDER.txt','intake.json']:
 bind[n]=h(p/n)
dump(p/'APPLICATION.json',{'packet':p.name,'author':'geometry_restart','producer':'geometry_restart','status':'PENDING_FRESH_DISTINCT_REVIEW_NOT_LEAN_VALIDATED','intake_sha256':h(p/'intake.json'),'sources':{f:h(p/f) for f in d['files']},'bindings':bind,'obligations':[{'name':n,'required_input':req,'constructed_input':got,'justification':got,'source_references':src.split('; '),'evidence':src.split('; ')} for n,req,got,src in ob],'local_lean_run':False,'cloud_lean_run':False,'hosted_lean_run':False,'kernel_acceptance':False})
sys.path.insert(0,str(r/'scripts'))
import check_progress_experiment as c
plan=c.ci.derive_plan(early_depth=7)
_,checked,_,_=c.packet(p.name,plan)
dump(p/'STRUCTURAL-CHECK.json',{'status':'PASS_STRUCTURAL_ONLY','modules':len(checked['order']),'predecessors_exact':len(prior),'new_modules':names,'lean_run':False,'kernel_acceptance':False})
print('APPLICATION',h(p/'APPLICATION.json'),'INTAKE',h(p/'intake.json'),'MODULES',len(checked['order']))
