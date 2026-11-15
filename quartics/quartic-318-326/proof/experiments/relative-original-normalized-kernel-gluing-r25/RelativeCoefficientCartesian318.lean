module
public import RelativeCoefficientChange318
public section
noncomputable section
namespace RelativeCoefficientCartesian318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (k R S : CommRingCat.{u}) [Algebra k R] [Algebra k S]
  (f : R →ₐ[k] S) {X : Scheme.{u}} (p : X ⟶ Spec k)
/-- The actual p-first original source family is Cartesian under EVERY
coefficient map, not merely its selected affine chart. -/
lemma cartesian : IsPullback (RelativeCoefficientChange318.familyMap k R S f p)
    (pullback.snd p (RelativeOriginalAffineChart318.baseMap k S))
    (pullback.snd p (RelativeOriginalAffineChart318.baseMap k R))
    (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
  apply IsPullback.of_right
    (h₁₂ := pullback.fst p (RelativeOriginalAffineChart318.baseMap k R))
    (h₂₂ := RelativeOriginalAffineChart318.baseMap k R)
  · simpa only [RelativeCoefficientChange318.familyMap_original,
      RelativeCoefficientChange318.spec_base] using
        (IsPullback.of_hasPullback p (RelativeOriginalAffineChart318.baseMap k S))
  · exact RelativeCoefficientChange318.familyMap_test k R S f p
  · exact IsPullback.of_hasPullback p (RelativeOriginalAffineChart318.baseMap k R)
end RelativeCoefficientCartesian318
