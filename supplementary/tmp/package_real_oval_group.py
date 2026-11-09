from pathlib import Path
import json,hashlib,datetime,re,subprocess
p=Path('quartics/quartic-318-326/proof/experiments/forward-real-oval-group-r1');base=p.parent;progress=base.parent/'progress';h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();order=['RealQuarticAssociativityPolynomial318','RealQuarticSumU318','RealQuarticSumAnalytic318','RealQuarticAssociativity318','RealQuarticGroup318','RealQuarticTopologicalGroup318'];sources={n+'.lean':h(p/(n+'.lean')) for n in order}
m=re.search(r'EXPERIMENT_AUDIT_PASS declarations=(\d+) modules=6',(p/'validation/AuditRealOvalGroup.log').read_text());assert m;count=int(m[1])
for n in order:assert (p/'validation'/(n+'.log')).read_text().count('\n')==1
pd=json.loads((base/'forward-real-oval-cover-r1/DEPENDENCY-PINS.json').read_text());known=pd['frozen_packet_sources'];known[str(base/'forward-real-oval-cover-r1/RealQuarticOvalCover318.lean')]='';own={n:p/(n+'.lean') for n in order};fm={Path(f).stem:Path(f) for f in known};bp={};fp={};seen=set()
def visit(n):
 if n in seen:return
 seen.add(n)
 if n in own:f=own[n]
 elif n in fm:f=fm[n];fp[str(f)]=h(f)
 elif (progress/(n+'.lean')).exists():f=progress/(n+'.lean');bp[n+'.lean']=h(f)
 else:
  assert n.startswith(('Mathlib.','Lean.','Std.','Init.')),n
  return
 for i in re.findall(r'^(?:public |meta )?import (?:all )?(\S+)',f.read_text(),re.M):visit(i)
for n in order:visit(n)
assert len(bp)==122 and len(fp)==6
for n,v in bp.items():assert hashlib.sha256(subprocess.check_output(['git','show','5e483a2:'+str(progress/n)])).hexdigest()==v
pp={}
for f in ['Mathlib/Analysis/Analytic/Uniqueness.lean','Mathlib/Analysis/Analytic/Composition.lean','Mathlib/Topology/Algebra/Group/Defs.lean','Mathlib/Topology/MetricSpace/ProperSpace.lean']:
 q=progress/'.lake/packages/mathlib'/f
 if q.exists():pp[f]=h(q)
pd={'baseline_source_pins':bp,'frozen_packet_sources':fp,'primary_mathlib_sources':pp,'frozen_predecessor_receipts':{str(base/n/'VALIDATION.json'):h(base/n/'VALIDATION.json') for n in ['forward-real-oval-cover-r1','forward-real-guard-ambient-r1','forward-coherent-multiple-charts-r1','forward-real-guard-witness-r1']},'original_baseline_commit':'5e483a2','mathlib_commit':'56a005855ea17e0b0958f73ec801ae140b0a1679'}
# Earlier packet receipt naming is preserved rather than invented.
(p/'DEPENDENCY-PINS.json').write_text(json.dumps(pd,indent=2)+'\n')
text=f'''# Actual compact group on the full real quartic oval

Author: /root/advance_integer_witnesses. Frozen six-module packet. Fresh strict replay and recursive private-inclusive audit of {count} declarations passed; distinct review and admission pending.

For every real D>0, the full ordinary real curve C_D={{(u,v):v²=1-Du⁴}} carries the actual commutative group law
U=(u b+a v)/(1+D u²a²),
V=(v b(1-Du²a²)-2D u a(u²+a²))/(1+D u²a²)².
The identity is(0,1) and inverse is(-u,v). No tangent, inverse, zero-coordinate or zero-ordinate points are removed. All denominators are positive on the entire real ambient domain. The curve is the actual closed subtype of R² with its existing topology; no topology or law is transported from an abstract circle.

## Associativity without a sign assumption

For U associativity, set q=1+Du²a², p=ub+av, r=vb(1-Du²a²)-2Dua(u²+a²), and t=1+Da²c², k=ae+cb, l=be(1-Da²c²)-2Dac(a²+c²). The two iterated U coordinates normalize to (pe q+cr)/(q²+Dp²c²) and (ul+kv t)/(t²+Dk²u²). A cleared polynomial identity, expressed as a linear combination of the three exact curve equations, proves equality. The included SymPy generator only generated coefficient expressions; Lean's ring and linear_combination proof is the certificate. No generated equality is taken on trust. Every normalized denominator is proved nonzero before division.

For V associativity, the exact sum_curve theorem and proved U associativity show the two V expressions have equal squares. This alone would not fix sign. Instead pull both functions back by the already proved globally analytic surjection R³ onto three full ovals. Both nested rational V expressions are globally real analytic, because their denominators never vanish. At the zero angle triple both have value1. Continuity makes their sum nonzero near that reference, so equal squares imply actual equality on a neighborhood. The analytic identity principle on connected R³ then proves equality everywhere. Surjectivity returns this identity to every triple of oval points, retaining every exceptional branch. No pointwise choice of a square root or assertion that the trigonometric cover is additive is used.

The remaining group axioms are direct rational identities, with negation closure and inverse cancellation using the exact curve equation. The bundled AddCommGroup uses these explicit operations and ordinary recursive integer/natural multiples. This is a genuine group on the full oval, not the previously available normalized-source-branch addition theorem.

## Original topology and compactness

Addition is continuous because both rational coordinate functions are analytic on all R⁴. Their composition with actual subtype projections supplies continuity of the exact bundled addition. Negation is ordinary coordinate negation. The resulting IsTopologicalAddGroup uses the original induced topology. Compactness is proved independently: the oval equation is closed; the actual analytic oval surjection bounds |u| by the positive radius D^(-1/4), and the equation gives |v|<=1. Thus the oval is a closed subset of a concrete compact closed ball in R². There is no circular compact-group assumption.

## Consumer and boundaries

This supplies the real compact-group carrier required before identifying the coherent arithmetic charts as an integer group orbit. That identification is NOT proved in this packet. In particular, no closed cyclic-subgroup component, finite component group, analytic cover of the actual component or scalar-region nonemptiness follows just from the group package. The previously proved full-oval-product guard density cannot be substituted for guard density on that smaller component. The next consumer must compare actual arithmetic u/v coordinates with these same operations and original topology.

The actual orbit-component analytic cover, scalar-region nonemptiness, allowed progression selection, local/CRT/prime preparation, remaining source-row assembly and full integer-to-source theorem remain open. The existing historical compact-Lie-group argument is prior justification; this is a concrete formal prerequisite, not evidence of historical absence. No manuscript, historical disposition or accepted manifest is changed.

## Verification

Six exact sources were freshly replayed with Lean4.35.0 -j1 -M6144 -Ddebug.skipKernelTC=false under the shared serial checker, followed by the private/generated-inclusive recursive audit. Only propext, Classical.choice and Quot.sound are allowed. The exact recursive project import closure has122 baseline sources, compared with original5e483a2, and6 frozen predecessor source modules. No upstream rebuild, independent acceptance or global arithmetic proof is claimed.
'''
(p/'DERIVATION.md').write_text(text)
obs=[
('source_requirements','Every point of the full real quartic for arbitrary positive D.','Ordinary subtype of R² satisfying v²=1-Du⁴, with explicit rational operations.','Positivity of every denominator holds on the full ambient domain, not merely a generic or normalized branch.',['RealQuarticSumU318.lean','RealQuarticGroup318.lean']),
('first_coordinate_associativity','Global U associativity on all three input ovals.','Exact polynomial certificate and normalized rational identities.','The three curve relations produce the cleared numerator identity; all clearing factors are separately proved nonzero. The generator is not an oracle.',['RealQuarticAssociativityPolynomial318.lean','RealQuarticSumU318.lean']),
('analytic_sign_comparison','Equality of V, not only equality of its square.','Two entire real analytic expressions on the actual three-angle surjection, both1 at the origin.','Equal squares and nonzero sum near the common reference give local equality; analytic uniqueness on connected R³ extends it globally.',['RealQuarticSumAnalytic318.lean','RealQuarticAssociativity318.lean']),
('index_coverage','Every real oval triple, including tangent/inverse/turning points.','The exact full-oval surjection supplies each of the three angles independently.','Surjectivity proved for both ordinate signs transfers the global analytic identity to arbitrary triples. No exception is discarded.',['RealQuarticAssociativity318.lean','RealQuarticOvalCover318.lean']),
('group_identity','The group operations must be those whose rational formulas are consumed later.','AddCommGroup uses add,zero,neg defined by sumU,sumV,(0,1),(-u,v).','Closure, commutativity, both identities, inverse and associativity are explicit; recursive multiples use these operations.',['RealQuarticGroup318.lean']),
('topology_maps','Continuity in the independently existing real subspace topology.','Analytic R⁴ coordinate expressions composed with actual subtype projections; coordinate negation.','The IsTopologicalAddGroup is built from continuity of the exact law, without a transported topology.',['RealQuarticTopologicalGroup318.lean','RealQuarticSumAnalytic318.lean']),
('compactness','Actual compact carrier, not assumed compact-source data.','Closed polynomial locus inside a concrete finite-radius compact ball.','The positive actual radius bounds u via full surjectivity; the equation bounds v. Properness of R² yields compactness.',['RealQuarticTopologicalGroup318.lean']),
('actual_consumer_boundary','Do not identify arbitrary full-oval density with the actual arithmetic orbit component.','This packet ends at the compact group; integer-chart homomorphism and component cover are explicit future comparisons.','Historical justification is preserved, and no actual orbit/scalar/progression or final arithmetic conclusion is inferred.',['DERIVATION.md']),
('verification_acceptance','Fresh exact strict replay, private-inclusive axiom audit and distinct review.','Six sources, bound logs/artifacts,122 original baseline and6 predecessor pins.','Only three standard logical axioms permitted. Distinct review and accepted-manifest admission remain pending.',['VALIDATION.json','AuditRealOvalGroup.lean'])]
app={'author':'/root/advance_integer_witnesses','claim':'The explicit rational law defines a compact topological commutative group on the whole ordinary real quartic oval for every D>0.','sources':sources,'derivation_sha256':h(p/'DERIVATION.md'),'obligations':[{'id':a,'required_input':b,'constructed_input':c,'justification':d,'source_refs':e,'evidence':e[0]} for a,b,c,d,e in obs],'full_arithmetic_theorem_proved':False};(p/'APPLICATION.json').write_text(json.dumps(app,indent=2)+'\n')
intake={'packet':p.name,'status':'ISOLATED_STRICT_PASS_PENDING_DISTINCT_REVIEW','order':order,'files':{n+'.lean':{'sha256':sources[n+'.lean'],'imports':re.findall(r'^public import (\S+)',(p/(n+'.lean')).read_text(),re.M)} for n in order},'accepted_snapshot_promoted':False,'full_arithmetic_theorem_proved':False};(p/'intake.json').write_text(json.dumps(intake,indent=2)+'\n')
val={'status':'PASS','date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':app['claim'],'compiler':'Lean4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc','mathlib_commit':'56a005855ea17e0b0958f73ec801ae140b0a1679','flags':['-j1','-M','6144','-Ddebug.skipKernelTC=false'],'module_order':order,'sources':sources,'commands':[{'command':'lean-checked -R PACKET -o OUTPUT/'+n+'.olean PACKET/'+n+'.lean','exit_code':0} for n in order]+[{'command':'lean-checked -R PACKET PACKET/AuditRealOvalGroup.lean','exit_code':0}],'audit':{'modules':6,'declarations':count,'includes_private_and_generated':True,'recursively_checks_dependencies':True,'allowed_axioms':['propext','Classical.choice','Quot.sound']},'logs':{f.name:h(f) for f in (p/'validation').glob('*.log')},'audit_source_sha256':h(p/'AuditRealOvalGroup.lean'),'application_sha256':h(p/'APPLICATION.json'),'intake_sha256':h(p/'intake.json'),'derivation_sha256':h(p/'DERIVATION.md'),'dependency_pins_sha256':h(p/'DEPENDENCY-PINS.json'),'baseline_pins_count':122,'frozen_predecessor_sources':6,'artifacts':{f.name:h(f) for f in Path('build/forward-real-oval-group-r1').glob('*') if f.is_file()},'independent_review_status':'PENDING_DISTINCT_REVIEW','accepted_snapshot_promoted':False,'full_arithmetic_theorem_proved':False};(p/'VALIDATION.json').write_text(json.dumps(val,indent=2)+'\n');(p/'SHA256SUMS').write_text(''.join(h(f)+'  '+str(f.relative_to(p))+'\n' for f in sorted(p.rglob('*')) if f.is_file() and f.name!='SHA256SUMS'));print('sources',sources);print('APPLICATION',h(p/'APPLICATION.json'));print('VALIDATION',h(p/'VALIDATION.json'));print('audit',count)
