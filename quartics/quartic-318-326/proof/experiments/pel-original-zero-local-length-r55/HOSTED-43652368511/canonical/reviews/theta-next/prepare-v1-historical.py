from pathlib import Path
import re,json,hashlib
out=Path(__file__).resolve().parent
base=out.parents[1]/'integration-20261114/repo/quartics/quartic-318-326/proof/experiments/pel-original-torsion-towers-r26'
mods={
'AlgebraicThetaSection':([],[]),
'LevelTheta':(['summable','holomorphic'],['hτ']),
'LevelThetaFourier':(['torusTerm_summable','real_evaluation','fourier_exact'],['hτ']),
'LevelThetaIndependence':(['torus_independent','entire_independent'],['hτ']),
'LevelThetaStrictDerivative':(['theta_contDiff_one','normalized_contDiff_one'],['hτ']),
'ScaledThetaConvergence':(['oneBound_summable','bound_summable','norm_bound','summable','hasSum'],['hτ','ha']),
'ScaledThetaHolomorphy':(['weightedOne_summable','derivativeBound_summable','derivative_norm_bound','selected_summable','selected_hasFDerivAt','selected_holomorphic'],['hτ','ha']),
'ThetaContinuousDerivative':(['derivative_sum_continuousAt','continuous_fderiv','selected_contDiff_one'],['hτ','ha']),
'ThetaInfinitesimalPeriod':([],[]),'ThetaTranslationPeriod':([],[])}
records=[]
for name,(decls,binders) in mods.items():
 f='PELOriginal'+name+'318.lean';s=(base/f).read_text();(out/'before'/f).write_text(s);t=s
 for d in decls:
  match=re.search(r'^(?:lemma|theorem) '+re.escape(d)+r'\b',t,re.M);assert match,d;pos=match.start()
  # Put include before the immediately preceding documentation comment.
  prefix=t[:pos];trim=prefix.rstrip()
  if trim.endswith('-/'):
   doc=trim.rfind('/--');assert doc>=0;pos=doc
  t=t[:pos]+'include '+' '.join(binders)+' in\n'+t[pos:]
 if name=='ScaledThetaConvergence':
  old='  simpa only [oneBound,pow_zero,one_mul,Int.cast_abs] using';new='  change Summable (fun n : ℤ =>\n    Real.exp (-Real.pi*((a*coercive τ)*(n:ℝ)^2-2*S*|(n:ℝ)|)))\n  simpa only [pow_zero,one_mul,Int.cast_abs] using';assert old in t;t=t.replace(old,new,1)
 if name=='ScaledThetaHolomorphy':
  old='  simpa only [weightedOne,oneBound,pow_one,Int.cast_abs] using';new='  change Summable (fun n : ℤ =>\n    |(n:ℝ)|*Real.exp (-Real.pi*((a*coercive τ)*(n:ℝ)^2-2*S*|(n:ℝ)|)))\n  simpa only [pow_one,Int.cast_abs] using';assert old in t;t=t.replace(old,new,1)
 if decls:(out/'after'/f).write_text(t)
 records.append({'module':f,'declarations':decls,'explicit_binders':binders,'before_sha256':hashlib.sha256(s.encode()).hexdigest(),'after_sha256':hashlib.sha256(t.encode()).hexdigest(),'changed':bool(decls),'options_unchanged':re.findall(r'^set_option.*',s,re.M)==re.findall(r'^set_option.*',t,re.M)})
(out/'SOURCE-HASHES.json').write_text(json.dumps({'source_commit':'2e4471d08710d58a1fdc2353b62a30023d88e94e','source_packet':base.name,'module_count_reviewed':10,'module_count_changed':7,'declaration_count':23,'binder_count':37,'sources':records},indent=2)+'\n')
print('prepared7source candidates,23 declarations,37 binders')
