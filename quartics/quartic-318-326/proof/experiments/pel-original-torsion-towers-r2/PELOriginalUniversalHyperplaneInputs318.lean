module
public import PELOriginalUniversalBalancedCoefficients318
public section
noncomputable section
namespace PELOriginalUniversalHyperplaneInputs318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318 PELOriginalMixedPointEvaluation318
open PELOriginalOpenRegularFunction318 PELOriginalOpenRegularNaturality318
open PELOriginalWholeHZeroDimension318 PELOriginalLevelTheta318
open PELOriginalBalancedHyperplaneSquares318 PELOriginalUniversalBalancedCoefficients318
variable (τ : ℂ) (hτ : 0 < τ.im)

lemma cubic_basis_value (k : NonemptyIndex τ hτ) (r : Label 6) (z : ComplexVectors)
    (hz : z∈domain τ hτ (opens τ hτ k)) :
    value τ hτ (opens τ hτ k)
      (PELOriginalWholePowerMixedTransition318.originalCoefficient τ hτ 2 k (thetaVector τ hτ 6 r)) z=
      PELOriginalLevelPowerSections318.value τ hτ 6 r z/
        (PELOriginalLevelPowerSections318.value τ hτ 3 k.val.1 z)^2 := by
  let p := point τ hτ (opens τ hτ k) z hz
  have he := point_ι τ hτ _ z hz
  have hn := coordinates_nonzero τ hτ k.val p z he
  rw [value_at_point τ hτ _ _ z p he]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop
    ((LineFrameTopScalar318.ringTop (opens τ hτ k)).inv
      (PELOriginalWholePowerMixedTransition318.originalCoefficient τ hτ 2 k (thetaVector τ hτ 6 r))))=_
  rw [PELOriginalWholePowerMixedTransition318.originalCoefficient,Iso.hom_inv_id_apply,
    PELOriginalWholePowerMixedCoefficient318.evaluation τ hτ 2 k.val _ p z hn.1 he]
  simp only [PELOriginalWholePowerRatioCover318.coverRatio,PELOriginalSexticRatioCover318.theta_lift]

/-- Actual cubic universal inputs retain all36 doubled-degree functions,
not a selected basis of only the balanced image. -/
@[expose] def cubic : Data τ hτ 3 where
  lineData := cubicData τ hτ
  label i := i.val.1
  gauge _ _ := rfl
  basis k r := PELOriginalWholePowerMixedTransition318.originalCoefficient τ hτ 2 k (thetaVector τ hτ 6 r)
  basis_value := cubic_basis_value τ hτ

/-- Actual quadratic universal inputs retain all16 original H0(4)
functions, algebraized by genuine degree6 padding and whole regular units. -/
@[expose] def quadratic : Data τ hτ 2 where
  lineData := quadraticData τ hτ
  label i := i.val.2
  gauge _ _ := rfl
  basis k r := PELOriginalQuarticMixedCoefficients318.coefficient τ hτ k (thetaVector τ hτ 4 r)
  basis_value k r z hz := by
    rw [PELOriginalQuarticMixedCoefficients318.coefficient_value τ hτ k _ z hz]
    simpa only [PELOriginalSexticRatioCover318.theta_lift]
end PELOriginalUniversalHyperplaneInputs318
