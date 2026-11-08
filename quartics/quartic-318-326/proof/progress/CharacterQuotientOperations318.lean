module
public import CompletedNormalizationIso318
public import CompletedIsoOperations318
public section
noncomputable section
namespace CharacterQuotientOperations318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[expose] def structureMap (i:Fin 4):SourceCharacterGlobal318.Model i⟶Spec (CommRingCat.of ℚ):=
  SourceCharacterGlobal318.modelMap i≫ProjectiveJLine318.structureMap ℚ
@[reassoc] theorem iso_over_Q (i:Fin 4):
    (CompletedNormalizationIso318.iso i).hom≫WeierstrassGluing318.structureMap (publishedA i) (publishedB i)=structureMap i:=by
  rw [←CompletedCharacterFinite318.targetTMap_over_Q,←Category.assoc,CompletedNormalizationIso318.iso_over_t]
  rfl
@[expose] def zero (i:Fin 4):Spec (CommRingCat.of ℚ)⟶SourceCharacterGlobal318.Model i:=
  CompletedIsoOperations318.zero (publishedA i) (publishedB i) (CompletedNormalizationIso318.iso i)
theorem zero_section (i:Fin 4):zero i≫structureMap i=𝟙 _:=
  CompletedIsoOperations318.zero_over_base _ _ _ _ (iso_over_Q i)
@[reassoc] theorem zero_comparison (i:Fin 4):zero i≫(CompletedNormalizationIso318.iso i).hom=
    WeierstrassGluing318.infinity (publishedA i) (publishedB i):=
  CompletedIsoOperations318.zero_comparison _ _ _
@[expose] def negation (i:Fin 4):SourceCharacterGlobal318.Model i⟶SourceCharacterGlobal318.Model i:=
  CompletedIsoOperations318.negation (publishedA i) (publishedB i) (CompletedNormalizationIso318.iso i)
theorem negation_twice (i:Fin 4):negation i≫negation i=𝟙 _:=CompletedIsoOperations318.negation_twice _ _ _
theorem zero_negation (i:Fin 4):zero i≫negation i=zero i:=CompletedIsoOperations318.zero_negation _ _ _
theorem negation_over_Q (i:Fin 4):negation i≫structureMap i=structureMap i:=
  CompletedIsoOperations318.negation_over_base _ _ _ _ (iso_over_Q i)
@[expose] def discriminant_unit (i:Fin 4):IsUnit (-16*(4*(publishedA i)^3+27*(publishedB i)^2)):=
  isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) (published_nonsingular i))
@[expose] def addition (i:Fin 4):CategoryTheory.Limits.pullback (structureMap i) (structureMap i)⟶SourceCharacterGlobal318.Model i:=
  CompletedIsoOperations318.addition _ _ (CompletedNormalizationIso318.iso i) (structureMap i) (iso_over_Q i) (discriminant_unit i)
theorem addition_over_Q (i:Fin 4):addition i≫structureMap i=
    CategoryTheory.Limits.pullback.fst (structureMap i) (structureMap i)≫structureMap i:=
  CompletedIsoOperations318.addition_over_base _ _ _ _ _ _
/-- Actual base-preserving maps on every Scheme test, not merely Q-points. -/
@[expose] def pointEquiv (i:Fin 4) {T:Scheme} (b:T⟶Spec (CommRingCat.of ℚ)):
    CompletedIsoOperations318.Points (structureMap i) b≃
      CompletedIsoOperations318.TargetPoints (publishedA i) (publishedB i) b:=
  CompletedIsoOperations318.pointEquiv _ _ (CompletedNormalizationIso318.iso i) _ (iso_over_Q i) b
end CharacterQuotientOperations318
