module
public import PELOriginalOrderPowerCoefficients318
public section
noncomputable section
namespace PELOriginalHyperplaneAllPowerBasis318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalOpenRegularFunction318 PELOriginalOpenRegularNaturality318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318 PELOriginalWholeHZeroDimension318
variable (τ : ℂ) (hτ : 0 < τ.im) (N : ℕ) [NeZero N]
structure Data where
  lineData : PELOriginalBalancedLineData318.Data τ hτ
  label : NonemptyIndex τ hτ → Label N
  gauge : ∀ i z,lineData.g i z=PELOriginalLevelPowerSections318.value τ hτ N (label i) z
  basis : ∀ (m : ℕ) [NeZero (N*m)] (i : NonemptyIndex τ hτ),
    Label (N*m) → Γ(candidate τ hτ,opens τ hτ i)
  basis_value : ∀ (m : ℕ) [NeZero (N*m)] i r z,z∈domain τ hτ (opens τ hτ i) →
    value τ hτ (opens τ hτ i) (basis m i r) z=
      PELOriginalLevelPowerSections318.value τ hτ (N*m) r z/(lineData.g i z)^m
@[expose] def coefficient (m : ℕ) [NeZero (N*m)] (i : NonemptyIndex τ hτ) (r : Label (N*m)) :
    Γ(candidate τ hτ,opens τ hτ i) :=
  PELOriginalAllPowerMixedCoefficients318.coefficient τ hτ (N*m) i (thetaVector τ hτ (N*m) r)*
    ((PELOriginalCubeBasisCoefficients318.mixedUnit τ hτ i)⁻¹).val^m
lemma coefficient_value (m : ℕ) [NeZero (N*m)] (i : NonemptyIndex τ hτ) (r : Label (N*m))
    (z : ComplexVectors) (hz : z∈domain τ hτ (opens τ hτ i)) :
    value τ hτ (opens τ hτ i) (coefficient τ hτ N m i r) z=
      PELOriginalLevelPowerSections318.value τ hτ (N*m) r z/
        (PELOriginalTranslationFrameValues318.chartGauge τ hτ i z^N*
          value τ hτ (opens τ hτ i) (PELOriginalCubeBasisCoefficients318.mixedUnit τ hτ i).val z)^m := by
  let ev := evaluation τ hτ (opens τ hτ i) z hz
  have hu : ev ((PELOriginalCubeBasisCoefficients318.mixedUnit τ hτ i)⁻¹).val=
      (ev (PELOriginalCubeBasisCoefficients318.mixedUnit τ hτ i).val)⁻¹ := by
    simpa only [Units.coe_map,Units.val_inv_eq_inv_val] using congrArg Units.val
      (map_inv (Units.map ev.toMonoidHom) (PELOriginalCubeBasisCoefficients318.mixedUnit τ hτ i))
  rw [coefficient,value_eq_evaluation τ hτ _ _ z hz,map_mul,map_pow,hu]
  rw [←value_eq_evaluation τ hτ _ _ z hz,←value_eq_evaluation τ hτ _ _ z hz,
    PELOriginalAllPowerMixedCoefficients318.coefficient_value τ hτ _ i _ z hz,
    PELOriginalSexticRatioCover318.theta_lift]
  simp only [mul_pow,pow_mul,div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring
@[expose] def cubic : Data τ hτ 3 where
  lineData := PELOriginalBalancedHyperplaneSquares318.cubicData τ hτ
  label i := i.val.1
  gauge _ _ := rfl
  basis m := coefficient τ hτ 3 m
  basis_value m i r z hz := by
    rw [coefficient_value,PELOriginalOrderPowerCoefficients318.cubic_gauge τ hτ i z hz]
@[expose] def quadratic : Data τ hτ 2 where
  lineData := PELOriginalBalancedHyperplaneSquares318.quadraticData τ hτ
  label i := i.val.2
  gauge _ _ := rfl
  basis m := coefficient τ hτ 2 m
  basis_value m i r z hz := by
    rw [coefficient_value,PELOriginalOrderPowerCoefficients318.quadratic_gauge τ hτ i z hz]
end PELOriginalHyperplaneAllPowerBasis318
