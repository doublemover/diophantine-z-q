from pathlib import Path
import hashlib,json,shutil
B=Path(__file__).resolve().parent;C=B/'candidates';ROOT=B/'successors';REPO=Path('/workspace/scratch/41c6d5925c0e/pel-integration43539970197/repo');EX=REPO/'quartics/quartic-318-326/proof/experiments';HEAD='b3d76fb41c03f9194b0613eac0a9b4cb04b2576c'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
W=lambda p,d:p.write_text(json.dumps(d,indent=2)+'\n')
PAIRS=[('height-normalized-valuative-center-r60','height-normalized-valuative-center-r61',['IntegralRationalInfinityMap318']),('height-original-ks-lattice-assembly-r11','height-original-ks-lattice-assembly-r12',['IntegralRationalInfinityMap318','IntegralOriginalCommonRestriction318'])]
ROOT.mkdir()
for old,new,changed in PAIRS:
 p=ROOT/new;shutil.copytree(EX/old,p);hist=p/'inherited-metadata'/old;hist.mkdir(parents=True)
 for f in list(p.iterdir()):
  if f.is_file() and f.suffix!='.lean':shutil.move(str(f),hist/f.name)
 d=json.loads((hist/'intake.json').read_text());d.update(packet=new,status='UNACCEPTED_HOSTED_EXPERIMENT',revision_classification_schema=1,revision_of=old)
 for m in changed:shutil.copyfile(C/(m+'.lean'),p/(m+'.lean'));d['files'][m+'.lean']['sha256']=H(p/(m+'.lean'))
 revised=[n for n in d['order'] if (p/(n+'.lean')).read_bytes()!=(EX/old/(n+'.lean')).read_bytes()];reused=[n for n in d['order'] if n not in revised];assert set(revised)==set(changed)
 d.update(new_modules=[],revised_modules=revised,reused_modules=reused,unchanged_predecessor_modules=reused);W(p/'intake.json',d)
 sourcehash={n+'.lean':H(p/(n+'.lean')) for n in d['order']};oldhash={n+'.lean':H(EX/old/(n+'.lean')) for n in d['order']}
 W(p/'INHERITANCE.json',{'predecessor':old,'predecessor_commit':HEAD,'unchanged_sources':len(reused),'changed_sources':{n+'.lean':sourcehash[n+'.lean'] for n in revised},'old_sources':oldhash,'new_sources':sourcehash})
 (p/'MODULE_ORDER.txt').write_text('\n'.join(d['order'])+'\n');(p/'SOURCE_SHA256SUMS').write_text(''.join(h+'  '+n+'\n' for n,h in sourcehash.items()))
 change_text=', '.join('`'+n+'.lean`' for n in changed)
 (p/'README.md').write_text(f'''# Exact hosted projection and concrete localization-argument repair

Successor of `{old}` at `{HEAD}`. Published predecessors are frozen. [Hosted run 43564923898](https://github.com/doublemover/diophantine-z-q/actions/runs/43564923898) supplies the observed failure evidence; the successor remains an unaccepted hosted experiment.

## Observed frontier

Center r60 has 41 successful module commands, then IntegralRationalInfinityMap318 fails in 10.081s at two witness conversions. Its expected expressions still contain the explicit infinityMap.toRingHom projection, while the witnesses use the same AlgHom directly. Lattice r11 has 61 successful module commands, including the repaired LocalizedTensorRestriction318 in 1.970s, then IntegralOriginalCommonRestriction318 fails in 22.829s with unresolved concrete lift arguments and target-semiring inference. Neither packet completed its recursive axiom audit. No separate prefix diagnostic file is claimed: only the actual retained RESULT and module logs are evidence.

This successor changes exactly {change_text}. Rational changes add only AlgHom.toRingHom_eq_coe before the already-present AlgHom.coe_toRingHom in two simpa-only lists. When present, common-restriction changes explicitly name the same original lift carriers/element/map/unit witness and type the same target algebraMap as a ring homomorphism. The rational change in lattice is cross-packet propagation from center, not an observed lattice error. The newly passing generic tensor source is unchanged.

## Application contract

1. **Required inputs:** Rational comparison still quantifies every c : Fin 4 → ℚˣ, the same full infinity order and same exact original embeddings. Native projection/coercion lemmas apply to any already-constructed algebra homomorphism and are rfl identities, adding no hypothesis. Common restriction still uses arbitrary R with CommRing R and c : Fin 4 → Rˣ; its lift requires A=R[X], L=Localization.Away X, B=FiniteOrder R c, T=OldOverlap R c, the same X, finiteRestriction and finiteRestriction_unit.
2. **Constructed objects:** The original infinity order, original Kummer field, finite full order, canonical Laurent localization and old overlap are unchanged. Explicit A/L/B/T arguments select those existing objects rather than leaving metavariables to inference. No new Algebra or CommRing instance, localization or target action is installed.
3. **Coverage:** Rational extensionality still checks all rational constants, polynomial X, the whole localized polynomial base and every j : Fin 3 ordered root. Its concluding restriction is for arbitrary a in the entire order. Common restriction retains the entire CommonOrder and every finite-order a; the finite comparison and all signed roots are unchanged. No point, branch, coefficient factor or tensor component is removed.
4. **Transition maps:** Rational projection→ring-hom coercion→function coercion only normalizes the same infinityMap inside the same originalFieldEmbedding composite. The common-order ring map remains precisely LocalizedTensorRestriction.lift composed with finiteBaseChange.symm.toRingHom, from CommonOrder to OldOverlap. No reversal or replacement of this map is made.
5. **Scalars and signs:** Original signed pivot/root ratios and all coefficients are unchanged. The concrete lift uses the already-passing generic targetAlgebra induced by finiteRestriction, with exactly its original X-image-unit witness. In common_constant the ascription names the same algebraMap R (OldOverlap R c) as R →+* OldOverlap R c; it does not choose a different scalar action or add compatibility as a premise.
6. **Consumer identity:** infinity_restriction still consumes the exact equality by original open-embedding injectivity. common_finite cancels the same finiteBaseChange equivalence and applies the same hosted-passing lift_right. common_y and common_constant retain their original finite_polynomial transitions; commonAlgRestriction packages that exact ring map and scalar equation. IntegralWholeOverlapGenerators318 consumes the same common restriction and original root values.
7. **Exceptional cases:** Arbitrary commutative R and the same twist units are retained, including the full potentially ramified orders. No field/domain/nonzero assumption, excluded locus, alternative field component, or reduced generator family is added. All maps and invertibility premises are those previously constructed.
8. **Downstream preservation:** Complete predecessor source sets/order are retained. Every ancillary new/revised/reused/unchanged list is recomputed from immediate predecessor bytes under schema 1. Rational theorem/helper declarations are unchanged; common-restriction public statements are unchanged except the explicit type ascription around the original algebraMap in common_constant. Constructor/proof annotations and the Laurent numeral identify existing types only. Imports/resource options/trust settings are unchanged. Inherited reports and recovery records remain evidence for their own frozen older revisions, not this successor's approval.
9. **Verification boundary:** Internal independent source/provenance review and Python structural checks are not hosted elaboration, recursive axiom-audit success, arithmetic-theorem proof or manuscript acceptance. The 1.970s generic tensor pass is one observed module command, not whole-packet acceptance. New concrete normalization and inference behavior remain pending hosted verification. No local Lean/Lake is run.
''')
 ed=p/'HOSTED-43564923898';ed.mkdir();shutil.copytree(C/'primary',ed/'primary')
 for m in changed:
  for suffix in ['.lean.before','.lean.diff','.log','-REPAIR.json']:shutil.copyfile(C/(m+suffix),ed/(m+suffix))
 for n in ['center-RESULT.json','lattice-RESULT.json','LocalizedTensorRestriction318-PASS.log']:shutil.copyfile(C/n,ed/n)
 W(p/'HOSTED_REPAIR.json',{'packet':new,'predecessor':old,'run':43564923898,'head':HEAD,'changed_sources':[n+'.lean' for n in revised],'source_review':'PENDING','propagation_review':'PENDING','hosted_replay':'PENDING','local_lean_run':False})
 W(p/'SOURCE_VALIDATION.json',{'packet':new,'predecessor':old,'base_head':HEAD,'source_hash_import_binding_checks':'PENDING','predecessor_closure_comparison':'PENDING','closure_modules':len(d['order']),'changed_sources':{n+'.lean':sourcehash[n+'.lean'] for n in revised},'public_statement_exception':'common_constant exact original algebraMap gains a RingHom type ascription' if len(changed)>1 else None,'source_review':'PENDING','propagation_review':'PENDING','hosted_replay':'PENDING','local_lean_run':False,'full_arithmetic_theorem_proved':False})
 bindings={n:H(p/n) for n in ['README.md','intake.json','INHERITANCE.json','SOURCE_SHA256SUMS','MODULE_ORDER.txt','HOSTED_REPAIR.json','SOURCE_VALIDATION.json']+[m+'.lean' for m in changed]};bindings.update({f.relative_to(p).as_posix():H(f) for f in sorted(ed.rglob('*')) if f.is_file()})
 W(p/'APPLICATION.json',{'packet':new,'predecessor':old,'producer':'geometry_repair_resume','author':'geometry_repair_resume','status':'SOURCE_REVIEW_AND_HOSTED_REPLAY_PENDING','intake_sha256':H(p/'intake.json'),'contract':'README.md','contract_sha256':H(p/'README.md'),'sources':sourcehash,'bindings':bindings,'mathlib_commit':'56a005855ea17e0b0958f73ec801ae140b0a1679','local_lean_run':False,'full_arithmetic_theorem_proved':False})
 print(new,'intake',H(p/'intake.json'),'README',H(p/'README.md'))
W(B/'PAIRS.json',[{'predecessor':o,'packet':n,'changed_modules':cs} for o,n,cs in PAIRS])
