module
public import PELOriginalChartAnalyticEvaluation318
public import PELOriginalLevelThetaStrictDerivative318
public import HomogeneousEvaluationScaling318
public section
noncomputable section
namespace PELOriginalChartEvaluationRegularity318
open Set Filter
open scoped Topology
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCubicRelationIdeal318 PELOriginalCandidateAffineCharts318
open PELOriginalChartAnalyticEvaluation318 HomogeneousQuotientChart318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)

/-- A total extension of the actual original chart evaluation. Statements
about regularity below are only on the original nonzero theta chart. -/
@[expose] def evaluate (a : CoordinateChart τ hτ j) (z : ComplexVectors) : ℂ :=
  if hz : value τ hτ 3 j z ≠ 0 then algebraEvaluation τ hτ z j hz a else 0

lemma evaluate_on_chart (a : CoordinateChart τ hτ j) (z : ComplexVectors)
    (hz : value τ hτ 3 j z ≠ 0) :
    evaluate τ hτ j a z = algebraEvaluation τ hτ z j hz a := by
  simp only [evaluate,dif_pos hz]

/-- Every element of the SAME full coordinate ring has a genuine
homogeneous-fraction representative; no chosen generating subset. -/
theorem exists_fraction (a : CoordinateChart τ hτ j) :
    ∃ n : ℕ, ∃ p : Equations, ∃ hp : p.IsHomogeneous n,
      a = (quotientMap (relations τ hτ) j).rangeRestrict (fraction j n p hp) := by
  obtain ⟨n,p,hp,ha⟩ := degreeZero_normal_form (relations τ hτ) j a
  refine ⟨n,p,hp,Subtype.ext ?_⟩
  exact ha.trans (fraction_value (relations τ hτ) j n p hp).symm

/-- Evaluate the actual quotient-chart fraction on the ORIGINAL theta
vector. The common nonzero gauge scalar cancels with its exact degree. -/
theorem fraction_formula (n : ℕ) (p : Equations) (hp : p.IsHomogeneous n)
    (z : ComplexVectors) (hz : value τ hτ 3 j z ≠ 0) :
    algebraEvaluation τ hτ z j hz
      ((quotientMap (relations τ hτ) j).rangeRestrict (fraction j n p hp)) =
        MvPolynomial.eval (fun i => value τ hτ 3 i z) p / value τ hτ 3 j z ^ n := by
  change pointEvaluation τ hτ z j hz _ = _
  rw [pointEvaluation,HomogeneousQuotientPointEvaluation318.fraction_evaluation]
  obtain ⟨c,hc,he⟩ := actual_cover_scalar τ hτ z
  rw [←he]
  change MvPolynomial.eval (fun i => c * value τ hτ 3 i z) p /
      (c * value τ hτ 3 j z) ^ n = _
  rw [HomogeneousEvaluationScaling318.evaluate_scale p n hp,mul_pow]
  field_simp [hc,hz]

/-- One fixed homogeneous polynomial expression evaluates each entire
coordinate-ring element throughout the original nonzero theta chart. -/
theorem exists_formula (a : CoordinateChart τ hτ j) :
    ∃ n : ℕ, ∃ p : Equations, ∃ hp : p.IsHomogeneous n,
      ∀ z : ComplexVectors, value τ hτ 3 j z ≠ 0 →
        evaluate τ hτ j a z =
          MvPolynomial.eval (fun i => value τ hτ 3 i z) p / value τ hτ 3 j z ^ n := by
  obtain ⟨n,p,hp,rfl⟩ := exists_fraction τ hτ j a
  exact ⟨n,p,hp,fun z hz =>
    (evaluate_on_chart τ hτ j _ z hz).trans (fraction_formula τ hτ j n p hp z hz)⟩

lemma polynomial_contDiff (p : Equations) :
    ContDiff ℂ 1 (fun z : ComplexVectors => MvPolynomial.eval
      (fun i => value τ hτ 3 i z) p) := by
  refine p.induction_on (fun c => ?_) (fun p q hp hq => ?_) (fun p i hp => ?_)
  · simpa only [MvPolynomial.eval_C] using (contDiff_const :
      ContDiff ℂ 1 (fun _ : ComplexVectors => c))
  · simpa only [map_add] using hp.add hq
  · simpa only [map_mul,MvPolynomial.eval_X] using
      hp.mul (PELOriginalLevelThetaStrictDerivative318.value_contDiff_one τ hτ 3 i)

/-- Actual C1 regularity of EVERY original affine chart function on
its true theta domain, derived from its exact homogeneous expression. -/
theorem contDiffAt_evaluate (a : CoordinateChart τ hτ j) (z : ComplexVectors)
    (hz : value τ hτ 3 j z ≠ 0) : ContDiffAt ℂ 1 (evaluate τ hτ j a) z := by
  obtain ⟨n,p,hp,he⟩ := exists_formula τ hτ j a
  have hv := PELOriginalLevelThetaStrictDerivative318.value_contDiff_one τ hτ 3 j
  apply ((polynomial_contDiff τ hτ p).contDiffAt.div
    (hv.contDiffAt.pow n) (pow_ne_zero n hz)).congr_of_eventuallyEq
  filter_upwards [hv.continuous.continuousAt.eventually_ne hz] with w hw
  exact he w hw
end PELOriginalChartEvaluationRegularity318
