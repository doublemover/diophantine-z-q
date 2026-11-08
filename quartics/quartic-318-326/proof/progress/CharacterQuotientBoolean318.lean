module
public import CharacterBooleanKernel318
public import CharacterQuotientPointGroup318
public section
noncomputable section
namespace CharacterQuotientBoolean318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CharacterBooleanAffine318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- The actual old quotient has the identity or its already specified
whole-Scheme negation, according to the exact character. -/
@[expose] def targetMap (i:Fin 4) (s:Fin 4→Bool):
    SourceCharacterGlobal318.Model i⟶SourceCharacterGlobal318.Model i:=
  if epsilon i s=1 then 𝟙 _ else CharacterQuotientOperations318.negation i
@[reassoc] theorem target_comparison (i:Fin 4) (s:Fin 4→Bool):
    targetMap i s≫(CompletedNormalizationIso318.iso i).hom=
      (CompletedNormalizationIso318.iso i).hom≫CharacterBooleanGlobal318.targetMap i s:=by
  unfold targetMap CharacterBooleanGlobal318.targetMap
  by_cases h:epsilon i s=1
  · simp only [if_pos h,Category.id_comp,Category.comp_id]
  · simp only [if_neg h]
    exact CompletedIsoOperations318.negation_comparison _ _ _
/-- The original canonical source-to-cubic-normalization map, not a newly
chosen same-field quotient, intertwines every whole-source sign. -/
theorem equivariant (i:Fin 4) (s:Fin 4→Bool):
    ContactGlobalSigns318.map units s≫SourceCharacterGlobal318.globalMap i=
      SourceCharacterGlobal318.globalMap i≫targetMap i s:=by
  apply (cancel_mono (CompletedNormalizationIso318.iso i).hom).mp
  rw [Category.assoc,CompletedNormalizationIso318.actual_source_join,
    CharacterBooleanGlobal318.equivariant,Category.assoc,target_comparison,
    ←Category.assoc,CompletedNormalizationIso318.actual_source_join]
theorem fixes_iff (i:Fin 4) (s:Fin 4→Bool):
    ContactGlobalSigns318.map units s≫SourceCharacterGlobal318.globalMap i=
      SourceCharacterGlobal318.globalMap i↔epsilon i s=1:=by
  rw [←CharacterBooleanGlobal318.fixes_iff]
  constructor
  · intro h
    have hh:=congrArg (fun f=>f≫(CompletedNormalizationIso318.iso i).hom) h
    simpa only [Category.assoc,CompletedNormalizationIso318.actual_source_join] using hh
  · intro h
    apply (cancel_mono (CompletedNormalizationIso318.iso i).hom).mp
    simpa only [Category.assoc,CompletedNormalizationIso318.actual_source_join] using h

/-- The induced action is a genuine additive equivalence on every Scheme
test, with no field-point or reducedness restriction. -/
@[expose] def targetAddEquiv (i:Fin 4) (s:Fin 4→Bool) {T:Scheme}
    (b:T⟶Spec (CommRingCat.of ℚ)):
    CharacterQuotientPointGroup318.Points i b≃+CharacterQuotientPointGroup318.Points i b where
  toFun p:=if epsilon i s=1 then p else -p
  invFun p:=if epsilon i s=1 then p else -p
  left_inv p:=by by_cases h:epsilon i s=1 <;> simp [h]
  right_inv p:=by by_cases h:epsilon i s=1 <;> simp [h]
  map_add' p q:=by by_cases h:epsilon i s=1 <;> simp [h,add_comm]
@[simp] theorem targetAddEquiv_val (i:Fin 4) (s:Fin 4→Bool) {T:Scheme}
    (b:T⟶Spec (CommRingCat.of ℚ)) (p:CharacterQuotientPointGroup318.Points i b):
    (targetAddEquiv i s b p).val=p.val≫targetMap i s:=by
  change (if epsilon i s=1 then p else -p).val=_
  by_cases h:epsilon i s=1
  · simp only [if_pos h,targetMap,h,ite_true,Category.comp_id]
  · simp only [if_neg h,targetMap,h,ite_false,CharacterQuotientPointGroup318.neg_val]
end CharacterQuotientBoolean318
