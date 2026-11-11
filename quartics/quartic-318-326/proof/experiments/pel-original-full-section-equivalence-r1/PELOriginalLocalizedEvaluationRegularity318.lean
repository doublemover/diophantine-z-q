module
public import PELOriginalChartEvaluationRegularity318
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace PELOriginalLocalizedEvaluationRegularity318
open Set Filter
open scoped Topology
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
variable (d : CoordinateChart τ hτ j)

/-- Evaluation of the WHOLE original localized chart through its actual
universal property, not merely its coefficient or primitive subring. -/
@[expose] def evaluation (z : ComplexVectors) (hz : value τ hτ 3 j z ≠ 0)
    (hd : algebraEvaluation τ hτ z j hz d ≠ 0) : Localization.Away d →+* ℂ :=
  IsLocalization.Away.lift d (g := (algebraEvaluation τ hτ z j hz).toRingHom)
    (isUnit_iff_ne_zero.mpr hd)

lemma evaluation_source (z : ComplexVectors) (hz : value τ hτ 3 j z ≠ 0)
    (hd : algebraEvaluation τ hτ z j hz d ≠ 0) (a : CoordinateChart τ hτ j) :
    evaluation τ hτ j d z hz hd (algebraMap (CoordinateChart τ hτ j) (Localization.Away d) a) =
      algebraEvaluation τ hτ z j hz a :=
  IsLocalization.Away.lift_eq d (isUnit_iff_ne_zero.mpr hd) a

@[expose] def evaluate (a : Localization.Away d) (z : ComplexVectors) : ℂ :=
  if hz : value τ hτ 3 j z ≠ 0 then
    if hd : algebraEvaluation τ hτ z j hz d ≠ 0 then evaluation τ hτ j d z hz hd a else 0
  else 0

lemma evaluate_on_open (a : Localization.Away d) (z : ComplexVectors)
    (hz : value τ hτ 3 j z ≠ 0) (hd : algebraEvaluation τ hτ z j hz d ≠ 0) :
    evaluate τ hτ j d a z = evaluation τ hτ j d z hz hd a := by
  simp only [evaluate,dif_pos hz,dif_pos hd]

/-- One original coordinate numerator and one power of the SAME original
denominator suffice on its full analytic open. -/
theorem exists_ratio (a : Localization.Away d) :
    ∃ b : CoordinateChart τ hτ j, ∃ n : ℕ,
      ∀ (z : ComplexVectors) (hz : value τ hτ 3 j z ≠ 0)
        (hd : algebraEvaluation τ hτ z j hz d ≠ 0),
        evaluate τ hτ j d a z =
          PELOriginalChartEvaluationRegularity318.evaluate τ hτ j b z /
            PELOriginalChartEvaluationRegularity318.evaluate τ hτ j d z ^ n := by
  obtain ⟨⟨b,s⟩,he⟩ := IsLocalization.surj (Submonoid.powers d) a
  obtain ⟨n,hn⟩ := s.property
  refine ⟨b,n,?_⟩
  intro z hz hd
  have h := congrArg (evaluation τ hτ j d z hz hd) he
  rw [map_mul,evaluation_source,evaluation_source,←hn,map_pow] at h
  rw [evaluate_on_open τ hτ j d a z hz hd,
    PELOriginalChartEvaluationRegularity318.evaluate_on_chart τ hτ j b z hz,
    PELOriginalChartEvaluationRegularity318.evaluate_on_chart τ hτ j d z hz]
  exact (eq_div_iff (pow_ne_zero n hd)).mpr h

/-- In particular the produced regular primitive element has genuine C1
complex dependence at every original point where its denominator is a
unit. This theorem applies to every localized function, not just that one. -/
theorem contDiffAt_evaluate (a : Localization.Away d) (z : ComplexVectors)
    (hz : value τ hτ 3 j z ≠ 0) (hd : algebraEvaluation τ hτ z j hz d ≠ 0) :
    ContDiffAt ℂ 1 (evaluate τ hτ j d a) z := by
  obtain ⟨b,n,he⟩ := exists_ratio τ hτ j d a
  have hb := PELOriginalChartEvaluationRegularity318.contDiffAt_evaluate τ hτ j b z hz
  have hdc := PELOriginalChartEvaluationRegularity318.contDiffAt_evaluate τ hτ j d z hz
  have hd0 : PELOriginalChartEvaluationRegularity318.evaluate τ hτ j d z ≠ 0 := by
    rwa [PELOriginalChartEvaluationRegularity318.evaluate_on_chart τ hτ j d z hz]
  apply (hb.div (hdc.pow n) (pow_ne_zero n hd0)).congr_of_eventuallyEq
  filter_upwards [(PELOriginalLevelPowerSections318.holomorphic τ hτ 3 j).continuous.continuousAt.eventually_ne hz,
    hdc.continuousAt.eventually_ne hd0] with w hw hdw
  have hde : algebraEvaluation τ hτ w j hw d ≠ 0 := by
    rwa [PELOriginalChartEvaluationRegularity318.evaluate_on_chart τ hτ j d w hw] at hdw
  exact he w hw hde
end PELOriginalLocalizedEvaluationRegularity318
