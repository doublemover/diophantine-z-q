from pathlib import Path
import json,hashlib,shutil
BASE=Path(__file__).resolve().parent
CAND=BASE/'recovered/candidates'
ROOT=BASE/'successors'
REPO=Path('/workspace/scratch/41c6d5925c0e/pel-integration43539970197/repo')
EX=REPO/'quartics/quartic-318-326/proof/experiments'
HEAD='7a5f079f2a82fa6f21db0e060d9bca1af9956a0b'
ROWS=json.loads((BASE/'recovered/geometry-PROPAGATION-BINDINGS.json').read_text())['packets']
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
W=lambda p,d:p.write_text(json.dumps(d,indent=2)+'\n')
ROOT.mkdir()
for row in ROWS:
 old,new=row['predecessor'],row['packet'];changed=['IntegralRationalInfinityMap318']+(['LocalizedTensorRestriction318'] if row['modules']==173 else [])
 p=ROOT/new;shutil.copytree(EX/old,p);hist=p/'inherited-metadata'/old;hist.mkdir(parents=True)
 for f in list(p.iterdir()):
  if f.is_file() and f.suffix!='.lean':shutil.move(str(f),hist/f.name)
 d=json.loads((hist/'intake.json').read_text());d['packet']=new;d['status']='UNACCEPTED_HOSTED_EXPERIMENT';d['revision_classification_schema']=1;d['revision_of']=old
 for m in changed:
  assert H(CAND/(m+'.lean'))==row['changed'][m]
  shutil.copyfile(CAND/(m+'.lean'),p/(m+'.lean'));d['files'][m+'.lean']['sha256']=H(p/(m+'.lean'))
 revised=[m for m in d['order'] if (p/(m+'.lean')).read_bytes()!=(EX/old/(m+'.lean')).read_bytes()];reused=[m for m in d['order'] if m not in revised]
 d.update(new_modules=[],revised_modules=revised,reused_modules=reused,unchanged_predecessor_modules=reused);W(p/'intake.json',d)
 assert H(p/'intake.json')==row['intake_sha256']
 oldhash={n+'.lean':H(EX/old/(n+'.lean')) for n in d['order']};sourcehash={n+'.lean':H(p/(n+'.lean')) for n in d['order']};assert sourcehash==row['sources']
 W(p/'INHERITANCE.json',{'predecessor':old,'predecessor_commit':HEAD,'unchanged_sources':len(reused),'changed_sources':{m+'.lean':sourcehash[m+'.lean'] for m in changed},'old_sources':oldhash,'new_sources':sourcehash})
 (p/'SOURCE_SHA256SUMS').write_text(''.join(h+'  '+n+'\n' for n,h in sourcehash.items()));(p/'MODULE_ORDER.txt').write_text('\n'.join(d['order'])+'\n')
 changedtext=', '.join('`'+m+'.lean`' for m in changed)
 readme=f'''# Exact hosted ring-map and localization-carrier repair

Successor of `{old}` at `{HEAD}`. The predecessor is frozen. Hosted run [43539970197](https://github.com/doublemover/diophantine-z-q/actions/runs/43539970197) supplies observed diagnostics, not acceptance of these candidates.

## Observed frontier and bounded change

Center r59 records 41 successful module commands, then IntegralRationalInfinityMap318 fails at line 127 applying its abstract-intermediate-algebra helper to the concrete composite. The log names an unification failure and opaque OreLocalization.instAdd; it does not establish a different mathematical map. Lattice r10 records 60 successful module commands, then LocalizedTensorRestriction318 fails at line 31 because the untyped tensor numeral leaves its localization carrier inferred as ℕ, with additional hidden-coercion evaluation failures. Neither packet completed its recursive audit.

This successor changes exactly {changedtext}. The rational repair normalizes the original coordinate and generators for two already-constructed ring homomorphisms. It no longer requests a freshly synthesized intermediate algebra structure. It is applied to the SAME composite (originalFieldEmbedding c).comp (infinityMap ℚ c).toRingHom and originalEmbedding c, using the SAME hX/hroot witnesses. When present, the localized tensor repair explicitly pins the original carrier L in the evaluation statements and exposes the SAME TensorProduct.lift as an algebra-hom application before its native elementary-tensor formula. The rational change in lattice is propagated from the center diagnostic, not a claimed observed lattice failure.

## Application contract

1. **Required inputs:** The rational wrapper takes two ring maps from the same infinity order to the same target commutative ring and agreement on its coordinate and every j : Fin 3 root. The former intermediate A/algebra parameters are unnecessary because the actual composite is already constructed. Tensor localization still requires the same arbitrary commutative rings, original A-actions, element x, localization L, map f and exact IsUnit image hypothesis; no new scalar action, field or invertibility premise is assumed.
2. **Constructed objects:** Same full infinity order over the localization of ℚ[X] at the product of all three coefficient polynomials; same original overlap and Kummer field. Tensor targetAlgebra remains exactly (f.comp (algebraMap A B)).toAlgebra. The explicit L annotations identify that original localization, not ℕ or a different localization.
3. **Coverage:** rational_order_ext is unchanged. It proves agreement on all rational constants, polynomial X, the entire localized coefficient base and every ordered Fin 3 root. The new private wrapper proves those very premises. Both elementary tensor evaluations quantify all b : B or a : A over the same L; no branch, point, index or tensor factor is omitted.
4. **Transitions:** originalFieldEmbedding, infinityMap, rationalOrderEquiv and originalEmbedding remain unchanged. RingHom.comp_apply only exposes their evaluation. Tensor baseMap is the same Away.lift; rightMap is the same f; lift is the same TensorProduct.lift and ring-hom projection. The native lift_tmul theorem yields the product of these exact maps, not an alternative extension.
5. **Scalars and signs:** Same signed pivot root, reciprocal unit and ordered root ratios. All seven explicit targetAlgebra installations remain unchanged. The left tensor proof uses the already-constructed baseMap.commutes a, whose target algebra map is definitionally the exact f.comp(algebraMap A B); no scalar factor is discarded.
6. **Consumer identity:** field_restriction still identifies the exact full embeddings; infinity_restriction still consumes that equality with the original field injection. IntegralOriginalCommonRestriction318 still applies the same lift and lift_right through the same finiteBaseChange inverse, with its original X and finiteRestriction_unit.
7. **Exceptional cases:** No additional domain, field, nonzero or root-selection assumption, no excluded point or smaller open. The arbitrary-L evaluation statement is made explicit so it cannot silently default to the unrelated natural-number carrier. No changed statement is treated as already kernel checked.
8. **Downstream preservation:** Full predecessor source set and order retained; all ancillary lists are recomputed from the exact byte delta and versioned by revision_classification_schema 1. Rational public theorem statements are unchanged. Tensor lift_right/lift_left statement text gains explicit L annotations and the right numeral's L type; this repairs inference while preserving the intended general localization statement. All definition bodies, imports and resource options are unchanged in the tensor file. Historical evidence remains historical.
9. **Verification boundary:** Internal independent source/provenance review is distinct from hosted elaboration and recursive axiom audit. The new helper's concrete unification and the tensor evaluation elaboration remain unverified until hosted. No local Lean/Lake, arithmetic-theorem proof, manuscript incorporation or whole-packet acceptance is claimed.
'''
 (p/'README.md').write_text(readme);assert H(p/'README.md')==row['readme_sha256']
 ed=p/'HOSTED-43539970197';ed.mkdir();shutil.copytree(CAND/'primary',ed/'primary')
 for m in changed:
  for suffix in ['.lean.before','.lean.diff','.log','-REPAIR.json']:shutil.copyfile(CAND/(m+suffix),ed/(m+suffix))
 for name in ['center-RESULT.json','lattice-RESULT.json','INDEPENDENT-GEOMETRY-SOURCE-REVIEW.md']:shutil.copyfile(CAND/name,ed/name)
 rec=p/'RECOVERY';rec.mkdir()
 for name in ['geometry-PROPAGATION-REVIEW.md','geometry-PROPAGATION-BINDINGS.json']:shutil.copyfile(BASE/'recovered'/name,rec/name)
 W(rec/'RECONSTRUCTION.json',{'reason':'Original out-of-scope geometry workspace disappeared before final report binding.','source_recovery':'Exact reviewed candidate bytes and hosted/primary evidence recovered from retained trace-r8 copy; unchanged sources from exact published predecessor.','source_intake_readme_match_original_review':True,'original_reviewed_application_sha256':row['application_sha256'],'original_reviewed_application_bytes_available':False,'application_metadata_regenerated':True,'new_metadata_review':'PENDING','local_lean_run':False})
 W(p/'HOSTED_REPAIR.json',{'packet':new,'predecessor':old,'run':43539970197,'head':HEAD,'changed_sources':[m+'.lean' for m in changed],'source_review':'NO_SOURCE_LEVEL_BLOCKER','propagation_review':'ORIGINAL_SOURCE_REVIEW_PASSED_RECOVERY_METADATA_RECHECK_PENDING','hosted_replay':'PENDING','local_lean_run':False})
 W(p/'SOURCE_VALIDATION.json',{'packet':new,'predecessor':old,'base_head':HEAD,'source_hash_import_binding_checks':'PENDING_RECOVERY_RECHECK','predecessor_closure_comparison':'PENDING_RECOVERY_RECHECK','closure_modules':len(d['order']),'changed_sources':{m+'.lean':H(p/(m+'.lean')) for m in changed},'public_statement_exception':'LocalizedTensorRestriction carrier annotations only, as specified in README' if len(changed)>1 else None,'resource_options':'UNCHANGED','source_review':'NO_SOURCE_LEVEL_BLOCKER','propagation_review':'RECOVERY_METADATA_RECHECK_PENDING','hosted_replay':'PENDING','local_lean_run':False,'full_arithmetic_theorem_proved':False})
 bindings={n:H(p/n) for n in ['README.md','intake.json','INHERITANCE.json','SOURCE_SHA256SUMS','MODULE_ORDER.txt','HOSTED_REPAIR.json','SOURCE_VALIDATION.json']+[m+'.lean' for m in changed]}
 for directory in [ed,rec]:bindings.update({f.relative_to(p).as_posix():H(f) for f in sorted(directory.rglob('*')) if f.is_file()})
 W(p/'APPLICATION.json',{'packet':new,'predecessor':old,'producer':'geometry_repair_resume','author':'geometry_repair_resume','status':'RECOVERED_SOURCE_REVIEWED_PROPAGATION_AND_HOSTED_REPLAY_PENDING','intake_sha256':H(p/'intake.json'),'contract':'README.md','contract_sha256':H(p/'README.md'),'sources':sourcehash,'bindings':bindings,'mathlib_commit':'56a005855ea17e0b0958f73ec801ae140b0a1679','local_lean_run':False,'full_arithmetic_theorem_proved':False})
 print(new,'SOURCE/INTAKE/README EXACTLY RECOVERED','APP regenerated',H(p/'APPLICATION.json'))
