module
public import PELOriginalThetaConstantCoefficient318
public import PELOriginalThetaLineSection318
public section
noncomputable section
namespace PELOriginalNonzeroThetaSection318
open QuaternionicRealPeriod318 PELOriginalThetaConvergence318
open PELOriginalSiegelNormalization318 PELOriginalThetaHermitianGauge318
open PELOriginalThetaGaugeMatrix318 PELOriginalPolarizationTransitions318
open PELOriginalPolarizationLineBundle318 PELOriginalThetaLineSection318
open PELOriginalDescendedMetric318 DiscreteComplexPeriodAtlas318
variable (τ:ℂ) (hτ:0<τ.im)

/-- Nontriviality transfers through the explicit nowhere-zero gauge and
actual original period normalization, without asserting theta(0)≠0. -/
theorem exists_original_value_nonzero:
    ∃z:ComplexVectors,PELOriginalGaugedTheta318.value τ hτ z≠0:=by
  obtain ⟨w,hw⟩:=PELOriginalThetaConstantCoefficient318.exists_nonzero τ hτ
  refine ⟨(normalization τ hτ).symm w,?_⟩
  simpa only [PELOriginalGaugedTheta318.value,LinearEquiv.apply_symm_apply,gaugedTheta] using
    mul_ne_zero (gauge_nonzero (bilinearMap τ) w) hw

/-- A genuinely nonzero global holomorphic section of the SAME original
rank-one bundle, certified by its positive descended metric at an actual
original quotient point. This is not yet algebraization or ampleness. -/
theorem exists_positive_section_metric:
    ∃q:Base τ,0<metric τ hτ (thetaSection τ hτ q):=by
  obtain ⟨z,hz⟩:=exists_original_value_nonzero τ hτ
  refine ⟨projection (P τ) z,?_⟩
  rw [original_metric]
  have hn:PELOriginalPolarizationMetric318.squaredNorm τ hτ
      (z,PELOriginalGaugedTheta318.value τ hτ z)≠0:=
    (PELOriginalPolarizationMetric318.squaredNorm_zero_iff τ hτ _).not.mpr hz
  have hp:0≤PELOriginalPolarizationMetric318.squaredNorm τ hτ
      (z,PELOriginalGaugedTheta318.value τ hτ z):=by
    exact mul_nonneg (sq_nonneg _) (PELOriginalPolarizationMetric318.weight_positive τ hτ z).le
  exact lt_of_le_of_ne hp (Ne.symm hn)
theorem exists_nonzero_section:
    ∃q:Base τ,(thetaSection τ hτ q).2≠0:=by
  obtain ⟨q,hq⟩:=exists_positive_section_metric τ hτ
  exact ⟨q,(zero_iff τ hτ _).not.mp (ne_of_gt hq)⟩
end PELOriginalNonzeroThetaSection318
