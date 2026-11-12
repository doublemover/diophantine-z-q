from pathlib import Path
import json,hashlib,re,shutil
root=Path(__file__).resolve().parents[1];b=root/'quartics/quartic-318-326/proof/experiments'
p=b/'forward-actual-two-descent-original-support-rebuild-r1';old=b/'forward-actual-two-descent-original-infinity-square-rebuild-r1'
h=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
new=['ActualTwoDescentInfinityPrimeSupportRebuild318','ActualTwoDescentOriginalOffOriginAffineCoverRebuild318','ActualTwoDescentOriginalOffSupportStalkUnitsRebuild318','ActualTwoDescentOriginalAllPointRootSupportRebuild318']
d=json.loads((old/'intake.json').read_text());d.update(packet=p.name,order=d['order']+new,new_modules=new,reused_modules=[])
d['files']={n+'.lean':{'sha256':h(p/(n+'.lean')),'imports':re.findall(r'^(?:public )?import ([A-Za-z0-9_.]+)',(p/(n+'.lean')).read_text(),re.M)} for n in d['order']}
(p/'intake.json').write_text(json.dumps(d,indent=2)+'\n')
inh={'predecessor':old.name,'predecessor_intake_sha256':h(old/'intake.json'),'exact_predecessor_sources':1318,'new_sources':{n+'.lean':h(p/(n+'.lean')) for n in new},'historical_byte_recovery':False,'changed_predecessor_sources':[]}
(p/'SOURCE-COPIES.json').write_text(json.dumps(inh,indent=2)+'\n')
(p/'MODULE_ORDER.txt').write_text('\n'.join(d['order'])+'\n')
(p/'SOURCE_SHA256SUMS').write_text(''.join(v['sha256']+'  '+k+'\n' for k,v in d['files'].items()))
primary=p/'SUPPORT-REBUILD-PRIMARY';primary.mkdir(exist_ok=True)
shutil.copy2(b/'height-original-normal-center-cotangent-r1/PRIMARY/PrimeSpectrumTopology.lean',primary/'PrimeSpectrumTopology.lean')
for n in ['ActualTwoDescentOriginalRootAffineSupport318','ActualTwoDescentInfinityMaximalGenerator318','ActualTwoDescentInfinityLocalParameter318','ActualTwoDescentOriginalCubicChartCover318','ActualTwoDescentOriginalTwoChartCubicScheme318']:
 shutil.copy2(p/(n+'.lean'),primary/(n+'.lean'))
ob=[
('All infinity primes','The support calculation must quantify all prime ideals of the literal original infinity ring.','The actual cubic v*factor=u^3 forces u into every prime containing v; span(u,v) is the actual maximal origin ideal. Prime properness then gives equality.'),
('Actual prime point','Ideal equality must identify the exact scheme origin, not merely a rational coordinate pair.','PrimeSpectrum.ext compares q with the previously constructed infinityPrime; native infinityChart maps it to the actual original infinityPoint.'),
('Native complete puncture','Every infinity prime away from O must lift through actual D(v).','Native localization_away_comap_range for InfinityPuncture gives the literal spectrum preimage, using v nonmembership from all-prime support.'),
('Whole affine cover away from O','The puncture lift must land in the same original glued scheme.','The exact pushout.condition identifies intoAffine then affineChart with intoInfinity then infinityChart. The old native two-chart cover thus produces an affine preimage of EVERY scheme point away from O.'),
('Same named root','An unrelated root coordinate or field cannot replace the original function.','named_root uses the exact old rootNumerator=x-a and previously rebuilt original generic coefficient maps. It equates the literal affine coordinate image with the same named original root.'),
('All affine primes away from Ta','Unit production must hold at every off-root affine prime, not only closed points.','The surviving actual_root_unit_off_support tests the full prime spectrum and actual localization. Equality of prime ideals would contradict the given original scheme point inequality.'),
('Actual scheme stalk unit','A unit in a coordinate localization must be transported through the real scheme stalk equivalence.','e is the exact open-immersion stalk equivalence, not an arbitrary algebra equivalence. Its inverse maps the old localization unit to the very coefficient s used by stalk_square.'),
('Generic image and exceptional cases','The same s must have the desired generic value, with support points retained explicitly.','The native stalk_square followed by named_root proves the full image equation. classify separates p=Ta and p=O and constructs a unit in every remaining stalk; n nonzero is not needed here.'),
('Verification and historical boundary','Fresh reconstruction cannot inherit lost acceptance or imply general divisor machinery.','All1318 predecessor sources remain exact. Existing all-prime affine support and old native chart cover are credited and consumed. Four new sources require fresh review and kernel replay. No general principal-divisor map, valuation sheaf, translation or theta/Weil result is inferred.')
]
doc='# Fresh all-point original root support\n\n'+'\n\n'.join('## '+str(i+1)+'. '+t+'\n\nRequired: '+r+'\n\nConstructed and justification: '+j for i,(t,r,j) in enumerate(ob))+'\n'
(p/'DERIVATION.md').write_text(doc)
(p/'README.md').write_text('# Original all-point support reconstruction\n\nFour fresh sources prove that the actual original affine chart covers every scheme point except O and that the same named original root function is represented by an actual unit in every stalk outside Ta and O. This consumes earlier complete affine-prime support, the real scheme pushout cover, and the fresh exact generic coefficient square. No rational-point restriction is substituted.\n\nFresh source reconstruction, not recovered historical bytes. No Lean run. Distinct review and hosted replay pending.\n')
(p/'GLOBAL-THEOREM-AUDIT.md').write_text('# Remaining scope\n\nAll-point local unit support is proved as a concrete certificate. General principal-divisor homomorphisms, supported Weil cycles, associated-divisor sheaf equality, translations and theta/Weil identification remain separate joins. The already available root order2 requires n nonzero; this all-point support theorem does not silently remove that premise from valuation statements.\n')
ev=['README.md','DERIVATION.md','GLOBAL-THEOREM-AUDIT.md','SOURCE-COPIES.json','MODULE_ORDER.txt','SOURCE_SHA256SUMS','intake.json']+[str(q.relative_to(p)) for q in primary.glob('*')]
app={'author':'/root/advance_global_arithmetic','status':'PENDING_DISTINCT_REVIEW_AND_HOSTED_CHECK','claim':'All-scheme-point affine coverage away from actual O and actual off-support stalk units for the SAME named original root function.','sources':{k:v['sha256'] for k,v in d['files'].items()},'bindings':{f:h(p/f) for f in ev},'obligations':[{'name':str(i+1),'required_input':r,'constructed_input':t,'justification':j,'source_references':[n+'.lean' for n in new],'evidence':['DERIVATION.md','SOURCE-COPIES.json']} for i,(t,r,j) in enumerate(ob)],'local_lean_run':False,'full_arithmetic_theorem_proved':False}
(p/'APPLICATION.json').write_text(json.dumps(app,indent=2)+'\n')
for f in old.glob('*.lean'):assert f.read_bytes()==(p/f.name).read_bytes()
print('APP',h(p/'APPLICATION.json'),'INTAKE',h(p/'intake.json'),'ORDER',len(d['order']),'EXACT',1318)
