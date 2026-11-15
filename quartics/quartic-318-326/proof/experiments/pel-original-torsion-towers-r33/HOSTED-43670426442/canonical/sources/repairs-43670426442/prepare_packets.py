from pathlib import Path
import json,hashlib,shutil
r=Path(__file__).resolve().parent;ws=r.parents[1];repo=ws/'integration-20261114/repo';host=ws/'integration-next-43667489535/hosted-43670426442';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
mod='IntegralGlobalLocalCompletion318';newsrc=r/'sources'/(mod+'.lean');report=ws/'review-20261114/GLOBAL-LOCAL-COMPLETION-43670426442-SOURCE-REVIEW.md';sa=json.loads((r/'SOURCE-APPLICATION.json').read_text());meta=json.loads((host/'artifacts.json').read_text());manifest=[]
dr=ws/'geometry-20261115/finite-dual-repairs-43670426442';dm='DVRTwistSquareNormalization318';dsa=json.loads((dr/'SOURCE-APPLICATION.json').read_text());dsource=dr/'sources'/(dm+'.lean')
for old,new in [('height-normalized-valuative-center-r76','height-normalized-valuative-center-r77'),('height-original-parameter-evaluation-r7','height-original-parameter-evaluation-r8')]:
 actual=host/('experiment-'+old)/'progress-experiments'/old
 result=json.loads((actual/'RESULT.json').read_text());cs=result['commands'];assert cs[-1]['module']==mod and cs[-1]['exit_code']==1;assert sum(c['exit_code']==0 for c in cs)==56
 src=repo/'quartics/quartic-318-326/proof/experiments'/old;p=r/'successors'/new;shutil.copytree(src,p,dirs_exist_ok=True)
 assert result['packet_sha256']==sha(src/'intake.json')
 for f in ['APPLICATION.json','README.md','intake.json','INHERITANCE.json']:
  if (src/f).exists():shutil.copy2(src/f,p/('IMMEDIATE-PREDECESSOR-'+f))
 assert sha(src/(mod+'.lean'))==sa['before_sha256'];assert sha(src/(dm+'.lean'))==dsa['before_sha256']
 shutil.copy2(newsrc,p/newsrc.name);shutil.copy2(dsource,p/dsource.name);shutil.copy2(report,p/'INDEPENDENT-COMPLETION-SOURCE-REVIEW.md');shutil.copy2(r/'SOURCE-APPLICATION.json',p/'SOURCE-APPLICATION.json')
 pre=p/'PREVENTIVE-DVR';pre.mkdir(exist_ok=True)
 for f in ['SOURCE-APPLICATION.json','INDEPENDENT-SOURCE-REVIEW.md']:shutil.copy2(dr/f,pre/f)
 shutil.copytree(dr/'evidence',pre/'OWN-RESEARCH-EVIDENCE',dirs_exist_ok=True)
 (pre/'SCOPE.json').write_text(json.dumps({'source':dm,'same_before_sha256':dsa['before_sha256'],'after_sha256':sha(dsource),'scope':'Preventive identical-before source propagation. This geometry predecessor stopped before this module; own failed research receipt is not a geometry failure or acceptance.','research_source_predecessor':'height-original-finite-dual-cofactor-r2','geometry_predecessor':old,'geometry_module_reached':False},indent=2)+'\n')
 ev=p/'HOSTED-43670426442';ev.mkdir(exist_ok=True)
 for f in ['RESULT.json','logs/'+mod+'.log','logs/IntegralInfinityArithmeticDomain318.log','logs/IntegralGlobalHeightOne318.log']:shutil.copy2(actual/f,ev/Path(f).name)
 a=next(a for a in meta['artifacts'] if a['name']=='experiment-'+old);(ev/'ARTIFACT-METADATA.json').write_text(json.dumps(a,indent=2)+'\n')
 d=json.loads((src/'intake.json').read_text());changed=[mod,dm];d.update(packet=new,revision_of=old,new_modules=[],reused_modules=[n for n in d['order'] if n not in changed],revised_modules=changed,unchanged_predecessor_modules=[n for n in d['order'] if n not in changed])
 for n in changed:d['files'][n+'.lean']['sha256']=sha(p/(n+'.lean'))
 (p/'intake.json').write_text(json.dumps(d,indent=2)+'\n')
 inheritance={'predecessor':old,'predecessor_commit':'7cbf02dd9bed3447c5d46502ebeb4f4c7aa7221b','predecessor_intake_sha256':sha(src/'intake.json'),'predecessor_application_sha256':sha(src/'APPLICATION.json'),'unchanged_sources':len(d['order'])-2,'changed_sources':{n+'.lean':sha(p/(n+'.lean')) for n in changed},'old_sources':{n+'.lean':sha(src/(n+'.lean')) for n in d['order']},'preventive_unreached_modules':[dm]};(p/'INHERITANCE.json').write_text(json.dumps(inheritance,indent=2)+'\n')
 research='parameter' in new
 (p/'README.md').write_text(f'''# {new}

Unaccepted successor to its OWN {old}. Own run43670426442 at exact7cbf02dd9bed3447c5d46502ebeb4f4c7aa7221b has56 strict full-module passes. IntegralInfinityArithmeticDomain, InfinityHeightOne, InfinityPrimeFrame and GlobalHeightOne now pass. IntegralGlobalLocalCompletion then fails because its hR-dependent local domain instance cannot be inferred, followed by dependent completion elaboration cascades. Own current RESULT/intake and logs are bound. No successor kernel acceptance or local Lean.

Two source changes only. IntegralGlobalLocalCompletion replaces two hidden-hR local instances with named exposed actualStalkDomain/actualStalkDVR constructions and explicitly installs those in Completion and all theorem types/bodies. These public let-bound instance types are intentionally disclosed; this is NOT a blanket unchanged-signature claim. The existing hR coefficient injection, h2, separation hN and actual intrinsic height-one hx construct the same actual stalk/domain/DVR and actual maximal-ideal completion. No external domain/DVR or model premise is added. The exact canonical map, injectivity, faithful flatness and additive valuation preservation remain.

DVRTwistSquareNormalization318 is an explicitly PREVENTIVE identical-before propagation from the distinct research lane's own current failure. This geometry predecessor stopped before that module. Its old d565adbe source is identical to the failed research source; the independently reviewed8a73 repair isolates the integer power identity before rewriting the full product. Negative valuations, parity e in Fin2, all original twist factors and public types/options remain unchanged. No research receipt is borrowed as a geometry failure or acceptance. PREVENTIVE-DVR contains exact source review, own research evidence and scope.

Order remains {len(d['order'])} roots, with {len(d['order'])-2} exact unchanged source copies. {'All ten appended parameter research roots remain unreached/unaccepted.' if research else 'Later center consumers remain unverified.'} Historical nested source reports/closures remain historical evidence, not silently rewritten current claims. Later inactive original-pair/native-dual research is NOT appended. All resource/trust options unchanged.

Trace may propagate matching-before source repairs under its own reviewed preventive contract, not as an observed trace geometry outcome. Lattice16 remains explicitly deferred for earlier arithmetic/height/PrimeFrame changes and distinct older Restrictions; trace older Restrictions also remain deferred. No blanket all-copy repair claim.

Actual good-base stalk completion is not an intrinsic dualizing or maximal regular-model comparison. Bad-base geometry, global proper-model integral sections, all-place KS210 and metrics remain separate. No GeometricRealization claim. Final independent current propagation review is appended externally after APPLICATION freeze.
''')
 req=[dict(o) for o in sa['obligations']]
 req[-1].update(required_input='Own '+old+' run43670426442 RESULT/intake and full module log.',constructed_input='56 strict successes, then exact GlobalLocalCompletion failure. Separate same-before DVR normalization preventive repair, with its own research provenance.',justification='Successor untested; no borrowed research failure/acceptance. '+('Ten appended roots unreached.' if research else 'Later center consumers unverified.'))
 for o in req:o.update(source_refs=[mod+'.lean',dm+'.lean','NormalizedOriginalValuativeCenter318.lean']+(['OriginalParameterAllPlaceEvaluations318.lean'] if research else []),evidence=['HOSTED-43670426442/RESULT.json','HOSTED-43670426442/'+mod+'.log','INDEPENDENT-COMPLETION-SOURCE-REVIEW.md','PREVENTIVE-DVR/SOURCE-APPLICATION.json','PREVENTIVE-DVR/INDEPENDENT-SOURCE-REVIEW.md','PREVENTIVE-DVR/SCOPE.json'])
 bindings={str(f.relative_to(p)):sha(f) for f in p.rglob('*') if f.is_file() and f!=p/'APPLICATION.json'}
 app={'packet':new,'predecessor':old,'author':'geometry_lean','producer':'geometry_lean','status':'SOURCE_REVIEWED_CURRENT_PROPAGATION_PENDING_HOSTED_UNVERIFIED','intake_sha256':sha(p/'intake.json'),'contract':'README.md','contract_sha256':sha(p/'README.md'),'local_lean_run':False,'kernel_verified':False,'full_arithmetic_theorem_proved':False,'new_source_acceptance':False,'obligations':req,'preventive_unreached_modules':[dm],'bindings':bindings};(p/'APPLICATION.json').write_text(json.dumps(app,indent=2)+'\n')
 assert all(sha(p/f)==h for f,h in bindings.items());assert sum((p/(n+'.lean')).read_bytes()!=(src/(n+'.lean')).read_bytes() for n in d['order'])==2
 manifest.append({'old':old,'new':new,'packet_dir':str(p),'roots':len(d['order']),'intake_sha256':sha(p/'intake.json'),'application_sha256':sha(p/'APPLICATION.json'),'changed_source_sha256':{n+'.lean':sha(p/(n+'.lean')) for n in changed},'binding_count':len(bindings)})
(r/'HANDOFF.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps(manifest,indent=2))
