module
public import AnalyticEvaluationDerivation318
public import PELOriginalChartEvaluationRegularity318
public import PELOriginalLevelThreeTangentSeparation318
public section
noncomputable section
namespace PELOriginalChartTangentDerivation318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalChartEvaluationRegularity318 PELOriginalAllLevelHolomorphicMap318
open Filter Topology
variable (τ : ℂ) (hτ : 0 < τ.im) (x : ComplexVectors) (j : Label 3)
  (hj : value τ hτ 3 j x ≠ 0)
/-- A total family of genuine whole-chart algebra evaluations. Off the
chosen theta chart, its harmless fallback is the SAME fixed center
point; near the center only the genuine varying evaluations occur. -/
@[expose] def nearbyEvaluation (y : ComplexVectors) : CoordinateChart τ hτ j →ₐ[ℂ] ℂ :=
  if hy : value τ hτ 3 j y ≠ 0 then algebraEvaluation τ hτ y j hy
  else algebraEvaluation τ hτ x j hj
lemma nearbyEvaluation_center : nearbyEvaluation τ hτ x j hj x = algebraEvaluation τ hτ x j hj := by
  simp only [nearbyEvaluation,dif_pos hj]
lemma nearbyEvaluation_eventually (a : CoordinateChart τ hτ j) :
    (fun y => nearbyEvaluation τ hτ x j hj y a) =ᶠ[𝓝 x] evaluate τ hτ j a := by
  filter_upwards [(PELOriginalLevelPowerSections318.holomorphic τ hτ 3 j).continuous.continuousAt.eventually_ne hj] with y hy
  simp only [nearbyEvaluation,dif_pos hy,evaluate_on_chart τ hτ j a y hy]
lemma nearbyEvaluation_differentiable (a : CoordinateChart τ hτ j) :
    DifferentiableAt ℂ (fun y => nearbyEvaluation τ hτ x j hj y a) x :=
  ((contDiffAt_evaluate τ hτ j a x hj).differentiableAt (by simp)).congr_of_eventuallyEq
    (nearbyEvaluation_eventually τ hτ x j hj a)
/-- Actual tangent direction to derivation on the WHOLE original chart
algebra; its center is exactly the previously constructed complex point. -/
@[expose] def tangentDerivation (v : ComplexVectors) :
    AnalyticEvaluationDerivation318.PointDerivations (algebraEvaluation τ hτ x j hj) :=
  AnalyticEvaluationDerivation318.direction (nearbyEvaluation τ hτ x j hj) x
    (nearbyEvaluation_differentiable τ hτ x j hj) (algebraEvaluation τ hτ x j hj)
    (nearbyEvaluation_center τ hτ x j hj) v
lemma tangentDerivation_apply (v : ComplexVectors) (a : CoordinateChart τ hτ j) :
    tangentDerivation τ hτ x j hj v a = fderiv ℂ (evaluate τ hτ j a) x v := by
  change fderiv ℂ (fun y => nearbyEvaluation τ hτ x j hj y a) x v = _
  rw [(nearbyEvaluation_eventually τ hτ x j hj a).fderiv_eq]
/-- Each original ratio has its literal analytic directional derivative,
including the distinguished ratio1. -/
lemma tangentDerivation_ratio (v : ComplexVectors) (i : Label 3) :
    tangentDerivation τ hτ x j hj v (ratioElement τ hτ j i) =
      fderiv ℂ (fun y => value τ hτ 3 i y/value τ hτ 3 j y) x v := by
  rw [tangentDerivation_apply]
  have he : evaluate τ hτ j (ratioElement τ hτ j i) =ᶠ[𝓝 x]
      (fun y => value τ hτ 3 i y/value τ hτ 3 j y) := by
    filter_upwards [(PELOriginalLevelPowerSections318.holomorphic τ hτ 3 j).continuous.continuousAt.eventually_ne hj] with y hy
    rw [evaluate_on_chart τ hτ j _ y hy,actual_ratio_evaluation]
  rw [he.fderiv_eq]
end PELOriginalChartTangentDerivation318
