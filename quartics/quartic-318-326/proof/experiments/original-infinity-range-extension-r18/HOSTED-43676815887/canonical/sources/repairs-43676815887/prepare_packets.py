from pathlib import Path
import json,hashlib,shutil
r=Path(__file__).resolve().parent;ws=r.parents[1];repo=ws/'integration-20261114/repo';host=ws/'integration-next-43673862672/hosted-43676815887';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
observed='IntegralValuativeChartPoints318'; cr=ws/'geometry-20261115/finite-dual-repairs-43676815887'; pr=ws/'geometry-20261115/preventive-evaluation-43676815887'
sa=json.loads((r/'SOURCE-APPLICATION.json').read_text()); fa=json.loads((cr/'SOURCE-APPLICATION.json').read_text()); pa=json.loads((pr/'SOURCE-APPLICATION.json').read_text())
sources={observed:(r,sa['before_sha256'],sa['after_sha256']),'DVRNormalizedFiniteOrder318':(cr,fa['before_sha256'],fa['after_sha256'])}
for f,v in pa['sources'].items():sources[Path(f).stem]=(pr,v['before_sha256'],v['after_sha256'])
reports=['CHART-POINTS-43676815887-SOURCE-REVIEW.md','FINITE-ORDER-43676815887-SOURCE-REVIEW.md','PREVENTIVE-EVALUATION-43676815887-SOURCE-REVIEW.md']
for f in reports:assert (ws/'review-20261114'/f).is_file(),f
meta=json.loads((host/'artifacts.json').read_text());manifest=[]
for old,new in [('height-normalized-valuative-center-r78','height-normalized-valuative-center-r79'),('height-original-parameter-evaluation-r9','height-original-parameter-evaluation-r10')]:
 actual=host/('experiment-'+old)/'progress-experiments'/old;result=json.loads((actual/'RESULT.json').read_text());cs=result['commands'];assert cs[-1]['module']==observed and cs[-1]['exit_code']==1;assert sum(c['exit_code']==0 for c in cs)==59
 src=repo/'quartics/quartic-318-326/proof/experiments'/old;p=r/'successors'/new;assert not p.exists();shutil.copytree(src,p);assert result['packet_sha256']==sha(src/'intake.json')
 for f in ['APPLICATION.json','README.md','intake.json','INHERITANCE.json']:
  if (src/f).exists():shutil.copy2(src/f,p/('IMMEDIATE-PREDECESSOR-'+f))
 for mod,(origin,before,after) in sources.items():
  assert sha(src/(mod+'.lean'))==before,(old,mod,'before');assert sha(origin/'sources'/(mod+'.lean'))==after;shutil.copy2(origin/'sources'/(mod+'.lean'),p/(mod+'.lean'))
 for f in reports:assert not(p/f).exists();shutil.copy2(ws/'review-20261114'/f,p/f)
 for origin,label in [(r,'CHART-POINTS'),(cr,'FINITE-ORDER'),(pr,'PREVENTIVE-EVALUATION')]:
  dest=p/('CANONICAL-43676815887-'+label);dest.mkdir();shutil.copy2(origin/'SOURCE-APPLICATION.json',dest/'SOURCE-APPLICATION.json')
  # Preserve each self-contained source contract with exact before, source and motivating evidence.
  contract=json.loads((origin/'SOURCE-APPLICATION.json').read_text())
  for rel,h in contract['bindings'].items():
   assert sha(origin/rel)==h; target=dest/rel;target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(origin/rel,target)
 ev=p/'HOSTED-43676815887';ev.mkdir()
 for f in ['RESULT.json','logs/'+observed+'.log','logs/IntegralRootPointMaps318.log']:shutil.copy2(actual/f,ev/Path(f).name)
 a=next(a for a in meta['artifacts']if a['name']=='experiment-'+old);(ev/'ARTIFACT-METADATA.json').write_text(json.dumps(a,indent=2)+'\n')
 d=json.loads((src/'intake.json').read_text());changed=[n for n in d['order']if n in sources];preventive=[n for n in changed if n!=observed];assert len(changed)==5
 d.update(packet=new,revision_of=old,new_modules=[],reused_modules=[n for n in d['order']if n not in sources],revised_modules=changed,unchanged_predecessor_modules=[n for n in d['order']if n not in sources])
 for n in changed:d['files'][n+'.lean']['sha256']=sha(p/(n+'.lean'))
 (p/'intake.json').write_text(json.dumps(d,indent=2)+'\n');unreached=len(d['order'])-60
 inheritance={'predecessor':old,'predecessor_commit':'9582519df0fe15c6e01c86d935a85a9a5257eb8d','predecessor_intake_sha256':sha(src/'intake.json'),'predecessor_application_sha256':sha(src/'APPLICATION.json'),'unchanged_sources':len(d['order'])-5,'changed_sources':{n+'.lean':sha(p/(n+'.lean'))for n in changed},'old_sources':{n+'.lean':sha(src/(n+'.lean'))for n in d['order']},'observed_failed_module':observed,'preventive_unreached_modules':preventive};(p/'INHERITANCE.json').write_text(json.dumps(inheritance,indent=2)+'\n')
 research='parameter' in new
 (p/'README.md').write_text(f'''# {new}

Unaccepted successor to its OWN {old}. Exact own run43676815887 at9582519df0fe15c6e01c86d935a85a9a5257eb8d has59 strict full-module passes, including IntegralRootPointMaps. IntegralValuativeChartPoints then fails on noninferable parameter-specific local Algebra instances. Own RESULT/intake and exact module logs are bound, not borrowed. This prefix leaves {unreached} roots unreached. No successor kernel acceptance or local Lean.

Five exact same-before source repairs; order stays {len(d['order'])} roots, {len(d['order'])-5} unchanged. ChartPoints is the ONLY observed failed module here. The other four are PREVENTIVE and UNREACHED: DVRNormalizedFiniteOrder (separate compact own9/1/7 evidence), IntegralValuativeGenericPoint, DVRNormalizedInfinityOrder, NormalizedGenericChartMaps (static identical-pattern review, no own module receipts). Each canonical self-contained source contract and independent review is bound.

Public type/name changes are explicit, not a blanket body-only/unchanged-signature claim:
- ChartPoints: actual finite eval and localized infinity evaluation algebras become named exposed defs; finite/infinity root-relation types carry explicit letI. Original hu unit-denominator and hz signed relation remain; whole finite/infinity scheme maps and structure identities unchanged.
- FiniteOrder: eval t algebra becomes named; root_relation letI and pointMap/native consumers scoped. Original exists_integral_model theorem unchanged.
- GenericPoint: actual aeval t algebra named; root_relation letI and whole sourceMap consumers scoped. Whole finite_generic_equality and point extension unchanged.
- InfinityOrder: eval w algebra named; root_relation letI and pointMap consumers scoped. Reciprocal-root/original-root/integral-root recovery unchanged with all nonzero inputs.
- GenericChartMaps: two actual aeval algebras receive distinct finiteEvaluationAlgebra/infinityEvaluationAlgebra names; public finite/infinity relation types letI, native map consumers scoped. reciprocal_roots and ht unchanged.

No external Algebra premise, new unit/domain hypothesis, narrowed signed/branch/infinity locus, module/import expansion or resource/trust changes. {'All ten appended parameter research roots remain unreached and unaccepted.' if research else 'Later center consumers remain unverified.'} Later inactive normalization/conductor, duality, original-pair research is NOT appended. Actual source/radicand definitions and coefficients remain unchanged; nonunit factors are not canceled integrally.

Historical inherited nested reports/closures remain historical; no historical APP rewrite. Trace may carry same-before repairs only as separately reviewed preventive propagation. Lattice earlier arithmetic/height/PrimeFrame/Completion/point-map deferrals and distinct trace/lattice older Restrictions remain explicit; no all-copy claim. Site85 remains displaced/inactive/unfixed, no source lineage borrowed.

No intrinsic dualizing, regular/maximal model, proper-model integral section, all-place KS210, metric or completed GeometricRealization claim. Final independent current report remains external to frozen packet inventory; inherited bound report filenames are never overwritten.
''')
 req=[dict(o)for o in sa['obligations']]
 req[0].update(constructed_input='Actual eval/aeval/localized-evaluation algebras named and explicitly installed in five existing sources; no new external algebra premise.')
 req[5].update(constructed_input='Five modules expose named evaluation definitions and public letI root-relation types as detailed in README and per-source canonical contracts.',justification='All original signed relations, infinity hu, reciprocal nonzero inputs retained. Not an unchanged-signature claim.')
 next(o for o in req if o['id']=='consumer')['justification']=f'Own geometry prefix leaves {unreached} roots unreached. Four changed siblings are preventive/unreached, not observed failures here.'
 req[-1].update(required_input='Own '+old+' run43676815887 RESULT/intake and ChartPoints log.',constructed_input=f'59 strict full-module passes, then ChartPoints failure; {unreached} later roots unreached. Compact FiniteOrder receipt is distinct motivating evidence only.',justification='Current successor untested. Three additional static same-pattern repairs have no own failure/pass receipt. No borrowed acceptance.')
 for o in req:o.update(source_refs=[n+'.lean'for n in changed]+['NormalizedOriginalValuativeCenter318.lean']+(['OriginalParameterAllPlaceEvaluations318.lean']if research else[]),evidence=['HOSTED-43676815887/RESULT.json','HOSTED-43676815887/'+observed+'.log']+reports)
 bindings={str(f.relative_to(p)):sha(f)for f in p.rglob('*')if f.is_file()and f!=p/'APPLICATION.json'}
 app={'packet':new,'predecessor':old,'author':'geometry_lean','producer':'geometry_lean','status':'SOURCE_REVIEWED_CURRENT_PROPAGATION_PENDING_HOSTED_UNVERIFIED','intake_sha256':sha(p/'intake.json'),'contract':'README.md','contract_sha256':sha(p/'README.md'),'local_lean_run':False,'kernel_verified':False,'full_arithmetic_theorem_proved':False,'new_source_acceptance':False,'obligations':req,'observed_failed_module':observed,'preventive_unreached_modules':preventive,'bindings':bindings};(p/'APPLICATION.json').write_text(json.dumps(app,indent=2)+'\n');assert all(sha(p/f)==h for f,h in bindings.items());assert sum((p/(n+'.lean')).read_bytes()!=(src/(n+'.lean')).read_bytes()for n in d['order'])==5
 manifest.append({'old':old,'new':new,'packet_dir':str(p),'roots':len(d['order']),'intake_sha256':sha(p/'intake.json'),'application_sha256':sha(p/'APPLICATION.json'),'changed_source_sha256':{n+'.lean':sha(p/(n+'.lean'))for n in changed},'preventive_unreached_modules':preventive,'binding_count':len(bindings)})
(r/'HANDOFF.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps(manifest,indent=2))
