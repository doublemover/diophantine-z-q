module
public import PELOriginalLevelTwoChartMorphism318
public section
noncomputable section
namespace PELOriginalLevelTwoNormalizedColumns318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalLevelTwoCubicProducts318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3) (s : Label 2)

abbrev Chart := Localization.Away (denominator τ hτ j s)

/-- Literal regular theta2 coordinate ratios on the principal open
where theta2_s cubed/cubic_j squared is invertible. -/
@[expose] def normalized (r : Label 2) : Chart τ hτ j s :=
  algebraMap (CoordinateChart τ hτ j) (Chart τ hτ j s) (coordinate τ hτ j r s) *
    IsLocalization.Away.invSelf (denominator τ hτ j s)

lemma normalized_self : normalized τ hτ j s s = 1 :=
  IsLocalization.Away.mul_invSelf (denominator τ hτ j s)

lemma original_denominator_nonzero (z : ComplexVectors)
    (hz : value τ hτ 3 j z ≠ 0) (hs : value τ hτ 2 s z ≠ 0) :
    algebraEvaluation τ hτ z j hz (denominator τ hτ j s) ≠ 0 := by
  rw [denominator_evaluation]
  exact div_ne_zero (pow_ne_zero 3 hs) (pow_ne_zero 2 hz)

@[expose] def originalPoint (z : ComplexVectors)
    (hz : value τ hτ 3 j z ≠ 0) (hs : value τ hτ 2 s z ≠ 0) :
    Chart τ hτ j s →ₐ[ℂ] ℂ :=
  RankOneAffinePointAction318.liftedPoint (coordinate τ hτ j) (s,s)
    (algebraEvaluation τ hτ z j hz) (original_denominator_nonzero τ hτ j s z hz hs)

/-- The actual regular normalized coordinates recover the literal
level-two ratios, with complete cancellation of the original cubic
trivialization and the two extra theta2_s factors. -/
theorem normalized_evaluation (r : Label 2) (z : ComplexVectors)
    (hz : value τ hτ 3 j z ≠ 0) (hs : value τ hτ 2 s z ≠ 0) :
    originalPoint τ hτ j s z hz hs (normalized τ hτ j s r) =
      value τ hτ 2 r z / value τ hτ 2 s z := by
  let f := originalPoint τ hτ j s z hz hs
  have hb (a : CoordinateChart τ hτ j) :
      f (algebraMap _ (Chart τ hτ j s) a) = algebraEvaluation τ hτ z j hz a :=
    IsLocalization.Away.lift_eq
      (isUnit_iff_ne_zero.mpr (original_denominator_nonzero τ hτ j s z hz hs)) a
  have hi : f (IsLocalization.Away.invSelf (denominator τ hτ j s)) =
      (algebraEvaluation τ hτ z j hz (denominator τ hτ j s))⁻¹ := by
    have he := congrArg f (IsLocalization.Away.mul_invSelf (denominator τ hτ j s))
    rw [map_mul,map_one,hb] at he
    apply mul_left_cancel₀ (original_denominator_nonzero τ hτ j s z hz hs)
    rw [he,mul_inv_cancel₀ (original_denominator_nonzero τ hτ j s z hz hs)]
  change f (normalized τ hτ j s r) = _
  rw [normalized,map_mul,hb,hi,evaluation,denominator_evaluation]
  field_simp [hz,hs] <;> ring

/-- This principal chart is an actual member of the entry cover used
by the genuine regular scheme map, with its full structural map. -/
@[reassoc] theorem local_scheme_map :
    RankOneAffineColumnCover318.entryMap (coordinate τ hτ j) (s,s) ≫
      PELOriginalLevelTwoChartMorphism318.morphism τ hτ j =
    RankOneAffineColumnCover318.localMap (coordinate τ hτ j) (s,s) :=
  RankOneAffineProjectiveMorphism318.entry_morphism _ _ _ _
end PELOriginalLevelTwoNormalizedColumns318
