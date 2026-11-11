module
public import PullbackIntermediateFactor318
public section
noncomputable section
namespace OriginalAffineCoefficientIdentity318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (S T : CommRingCat.{0}) [Algebra ℚ S] [Algebra ℚ T] (φ : S →ₐ[ℚ] T)
  (c : Fin 4 → ℚˣ)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
lemma map_eq : RelativeSchemeCoefficient318.map p (VaryingSourceCoefficientPullback318.base ℚ S)
    (VaryingSourceCoefficientPullback318.base ℚ T) (Spec.map (CommRingCat.ofHom φ.toRingHom))
    (VaryingSourceCoefficientPullback318.coefficient_base ℚ S T φ)=
      RelativeCoefficientChange318.familyMap (CommRingCat.of ℚ) S T φ p := by
  apply pullback.hom_ext
  · rw [RelativeSchemeCoefficient318.map_fst,RelativeCoefficientChange318.familyMap_original]
  · rw [RelativeSchemeCoefficient318.map_snd,RelativeCoefficientChange318.familyMap_test]
end OriginalAffineCoefficientIdentity318
