module
public import PELOriginalOrderEvenThetaSections318
public section
noncomputable section
namespace PELOriginalOrderPowerCoefficients318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 PELPrincipalOrderCoordinates318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalOpenRegularFunction318 PELOriginalOpenRegularNaturality318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318 PELOriginalComplementaryOrder318
open PELOriginalComplementaryHermitian318 PELOriginalTranslationFrameValues318
variable (τ : ℂ) (hτ : 0 < τ.im) (N : ℕ) [NeZero N]

/-- Full original H0 coefficient divided only by an independently
proved regular UNIT. No field-only or meromorphic coefficient is used. -/
@[expose] def coefficient (a : order) (i j : Label N) (k : NonemptyIndex τ hτ) :
    Γ(candidate τ hτ,opens τ hτ k) :=
  PELOriginalAllPowerMixedCoefficients318.coefficient τ hτ (N*(2*degree a)) k
    (PELOriginalOrderEvenThetaSections318.section τ hτ N a i j)*
      ((PELOriginalCubeBasisCoefficients318.mixedUnit τ hτ k)⁻¹).val^(2*degree a)

lemma value_formula (a : order) (i j : Label N) (k : NonemptyIndex τ hτ)
    (z : ComplexVectors) (hz : z∈domain τ hτ (opens τ hτ k)) :
    PELOriginalOpenRegularFunction318.value τ hτ (opens τ hτ k) (coefficient τ hτ N a i j k) z=
      (PELOriginalLevelPowerSections318.value τ hτ N i (linear a z)^2*
        PELOriginalLevelPowerSections318.value τ hτ N j (linear (complement a) z)^2)/
      (chartGauge τ hτ k z^N*
        PELOriginalOpenRegularFunction318.value τ hτ (opens τ hτ k)
          (PELOriginalCubeBasisCoefficients318.mixedUnit τ hτ k).val z)^(2*degree a) := by
  let ev := evaluation τ hτ (opens τ hτ k) z hz
  have hu : ev ((PELOriginalCubeBasisCoefficients318.mixedUnit τ hτ k)⁻¹).val=
      (ev (PELOriginalCubeBasisCoefficients318.mixedUnit τ hτ k).val)⁻¹ := by
    simpa only [Units.coe_map,Units.val_inv_eq_inv_val] using congrArg Units.val
      (map_inv (Units.map ev.toMonoidHom) (PELOriginalCubeBasisCoefficients318.mixedUnit τ hτ k))
  rw [coefficient,value_eq_evaluation τ hτ _ _ z hz,map_mul,map_pow,hu]
  rw [←value_eq_evaluation τ hτ _ _ z hz,←value_eq_evaluation τ hτ _ _ z hz,
    PELOriginalAllPowerMixedCoefficients318.coefficient_value τ hτ _ k _ z hz,
    PELOriginalOrderEvenThetaSections318.lift_section]
  simp only [PELOriginalOrderEvenThetaSections318.entireValue,mul_pow,pow_mul,div_eq_mul_inv,
    mul_inv_rev,inv_pow]
  ring
lemma cubic_gauge (k : NonemptyIndex τ hτ) (z : ComplexVectors)
    (hz : z∈domain τ hτ (opens τ hτ k)) :
    chartGauge τ hτ k z^3*PELOriginalOpenRegularFunction318.value τ hτ (opens τ hτ k)
      (PELOriginalCubeBasisCoefficients318.mixedUnit τ hτ k).val z=
        PELOriginalLevelPowerSections318.value τ hτ 3 k.val.1 z := by
  rw [PELOriginalCubeBasisCoefficients318.mixedUnit_value]
  have hn := theta_nonzero τ hτ k z hz
  simp only [chartGauge,PELOriginalMixedTranslationGauge318.gauge]
  field_simp [hn.1,hn.2]
lemma quadratic_gauge (k : NonemptyIndex τ hτ) (z : ComplexVectors)
    (hz : z∈domain τ hτ (opens τ hτ k)) :
    chartGauge τ hτ k z^2*PELOriginalOpenRegularFunction318.value τ hτ (opens τ hτ k)
      (PELOriginalCubeBasisCoefficients318.mixedUnit τ hτ k).val z=
        PELOriginalLevelPowerSections318.value τ hτ 2 k.val.2 z := by
  rw [PELOriginalCubeBasisCoefficients318.mixedUnit_value]
  have hn := theta_nonzero τ hτ k z hz
  simp only [chartGauge,PELOriginalMixedTranslationGauge318.gauge]
  field_simp [hn.1,hn.2]
lemma cubic_value (a : order) (i j k : NonemptyIndex τ hτ) (z : ComplexVectors)
    (hz : z∈domain τ hτ (opens τ hτ k)) :
    PELOriginalOpenRegularFunction318.value τ hτ (opens τ hτ k)
      (coefficient τ hτ 3 a i.val.1 j.val.1 k) z=
      (PELOriginalLevelPowerSections318.value τ hτ 3 i.val.1 (linear a z)^2*
        PELOriginalLevelPowerSections318.value τ hτ 3 j.val.1 (linear (complement a) z)^2)/
        (PELOriginalLevelPowerSections318.value τ hτ 3 k.val.1 z)^(2*degree a) := by
  rw [value_formula,cubic_gauge τ hτ k z hz]
lemma quadratic_value (a : order) (i j k : NonemptyIndex τ hτ) (z : ComplexVectors)
    (hz : z∈domain τ hτ (opens τ hτ k)) :
    PELOriginalOpenRegularFunction318.value τ hτ (opens τ hτ k)
      (coefficient τ hτ 2 a i.val.2 j.val.2 k) z=
      (PELOriginalLevelPowerSections318.value τ hτ 2 i.val.2 (linear a z)^2*
        PELOriginalLevelPowerSections318.value τ hτ 2 j.val.2 (linear (complement a) z)^2)/
        (PELOriginalLevelPowerSections318.value τ hτ 2 k.val.2 z)^(2*degree a) := by
  rw [value_formula,quadratic_gauge τ hτ k z hz]
end PELOriginalOrderPowerCoefficients318
