module
public import PELOriginalWholePowerRegularization318
public import PELOriginalHomogeneousRelationVanishing318
public import PELOriginalSexticSectionField318
public section
noncomputable section
namespace PELOriginalWholePowerSectionField318
open QuaternionicRealPeriod318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalChartSectionField318 PELOriginalChartEvaluationRegularity318
open PELOriginalSectionMultiplication318 PELOriginalGradedSectionRing318
open PELOriginalCubicRelationIdeal318 PELOriginalSexticRatioCover318
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationLineBundle318
open PELOriginalPowerSectionLift318 PELOriginalWholeHZeroDimension318
open PELOriginalSexticSectionField318 (lift_at_selected_chart)
open HomogeneousQuotientChart318
variable (τ : ℂ) (hτ : 0 < τ.im) (m : ℕ)

/-- The regular element has its LITERAL original graded-section fraction
in the SAME full section field. This identifies polarization degrees and
not merely scalar functions on a selected dense open. -/
theorem embedding_linear (j : Label 3) (s : homogeneous τ hτ (3*m)) :
    embedding τ hτ j (PELOriginalWholePowerRegularization318.linear τ hτ m j s)=
      algebraMap (Ring τ hτ) (SectionField τ hτ) (includeDegree τ hτ (3*m) s) /
        algebraMap (Ring τ hτ) (SectionField τ hτ) (generators τ hτ j)^m := by
  obtain ⟨n,p,hp,he⟩ := exists_fraction τ hτ j
    (PELOriginalWholePowerRegularization318.linear τ hτ m j s)
  have hcoeff :
      (MvPolynomial.eval₂Hom (algebraMap ℂ (Values τ)) (vector τ hτ) p *
        (vector τ hτ j)^m) * vector τ hτ j =
      (s.val * (vector τ hτ j)^n) * vector τ hτ j := by
    funext q
    change (MvPolynomial.eval₂Hom (algebraMap ℂ (Values τ)) (vector τ hτ) p q *
      (vector τ hτ j q)^m) * vector τ hτ j q =
      (s.val q * (vector τ hτ j q)^n) * vector τ hτ j q
    by_cases hj : vector τ hτ j q=0
    · simp only [hj,mul_zero]
    · let z := chart τ hτ ((core τ hτ).indexAt q) q
      have hv (i : Label 3) : value τ hτ 3 i z=vector τ hτ i q := by
        rw [←theta_lift τ hτ 3 i z]
        exact lift_at_selected_chart τ hτ 3 (thetaVector τ hτ 3 i) q
      have hz : value τ hτ 3 j z ≠ 0 := by rwa [hv]
      have hf := PELOriginalWholePowerRegularization318.cover_evaluation τ hτ m j s z hz
      rw [he,fraction_formula] at hf
      change MvPolynomial.eval (fun i => value τ hτ 3 i z) p /
        (value τ hτ 3 j z)^n =
        lift τ hτ (3*m) (asSection τ hτ (3*m) s) z/(value τ hτ 3 j z)^m at hf
      rw [lift_at_selected_chart τ hτ (3*m) s q] at hf
      simp only [hv] at hf
      rw [←PELOriginalHomogeneousRelationVanishing318.evaluate_at_point] at hf
      have hc := (div_eq_div_iff (pow_ne_zero n hj) (pow_ne_zero m hj)).mp hf
      exact congrArg (fun x : ℂ => x*vector τ hτ j q) hc
  have hring : (presentation τ hτ p * (generators τ hτ j)^m) * generators τ hτ j =
      (includeDegree τ hτ (3*m) s * (generators τ hτ j)^n) * generators τ hτ j := by
    apply Subtype.ext
    change ((presentation τ hτ p).val * (generators τ hτ j).val^m) *
      (generators τ hτ j).val =
      ((includeDegree τ hτ (3*m) s).val * (generators τ hτ j).val^n) * (generators τ hτ j).val
    rw [underlying_presentation,CubicHomogeneousMarker318.homogeneous_marker _ _ p n hp]
    change (Polynomial.monomial (3*n) _ * (Polynomial.monomial 3 (vector τ hτ j))^m) *
      Polynomial.monomial 3 (vector τ hτ j) =
      (Polynomial.monomial (3*m) s.val * (Polynomial.monomial 3 (vector τ hτ j))^n) *
        Polynomial.monomial 3 (vector τ hτ j)
    simp only [Polynomial.monomial_pow,Polynomial.monomial_mul_monomial]
    rw [show 3*n+3*m+3=3*m+3*n+3 by omega,hcoeff]
  let F := algebraMap (Ring τ hτ) (SectionField τ hτ)
  have hj : F (generators τ hτ j) ≠ 0 := by
    simpa only [F,quotientIntoField_mk,variable_image] using denominator_nonzero τ hτ j
  have hfield := congrArg F hring
  simp only [map_mul,map_pow] at hfield
  have hc := mul_right_cancel₀ hj hfield
  rw [he,fraction_image]
  exact (div_eq_div_iff (pow_ne_zero n hj) (pow_ne_zero m hj)).mpr hc

/-- Exact degree-m transition law in the common original field.
No chart-dependent meromorphic extension or normal-generation premise. -/
theorem transition (j k : Label 3) (s : homogeneous τ hτ (3*m)) :
    embedding τ hτ j (PELOriginalWholePowerRegularization318.linear τ hτ m j s)=
      embedding τ hτ k (PELOriginalWholePowerRegularization318.linear τ hτ m k s) *
        embedding τ hτ j (ratioElement τ hτ j k)^m := by
  rw [embedding_linear,embedding_linear,ratioElement,fraction_image]
  simp only [pow_one,variable_image]
  have hj : algebraMap (Ring τ hτ) (SectionField τ hτ) (generators τ hτ j) ≠ 0 := by
    simpa only [quotientIntoField_mk,variable_image] using denominator_nonzero τ hτ j
  have hk : algebraMap (Ring τ hτ) (SectionField τ hτ) (generators τ hτ k) ≠ 0 := by
    simpa only [quotientIntoField_mk,variable_image] using denominator_nonzero τ hτ k
  field_simp [hj,hk]
end PELOriginalWholePowerSectionField318
