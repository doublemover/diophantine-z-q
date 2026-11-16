module
public import PELOriginalProductChartPoints318
public import PELOriginalSexticBasepointFree318
public import PELOriginalAdditionTensorMap318
public section
noncomputable section
namespace PELOriginalRegularAdditionTensor318
open scoped TensorProduct
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalProductChartPoints318 PELOriginalSexticRegularization318
open PELOriginalCubicAdditionConstants318
variable (τ : ℂ) (hτ : 0 < τ.im) (j k : Label 3)

/-- All81 literal addition coordinates are regular elements of the
ACTUAL product chart, using the fixed addition constants and all36
whole sextic ratios on each factor. -/
@[expose] def coordinate (rs : Label 3 × Label 3) : ProductRing τ hτ j k :=
  ∑ u : Label 6, ∑ v : Label 6,
    additionConstant τ hτ rs.1 rs.2 u v •
      (theta τ hτ j u ⊗ₜ[ℂ] theta τ hτ k v)

lemma evaluation (z a : ComplexVectors) (hz : value τ hτ 3 j z ≠ 0)
    (ha : value τ hτ 3 k a ≠ 0) (rs : Label 3 × Label 3) :
    TensorComplexPointSeparation318.evaluation (algebraEvaluation τ hτ z j hz)
      (algebraEvaluation τ hτ a k ha) (coordinate τ hτ j k rs)=
    (value τ hτ 3 rs.1 (z+a)*value τ hτ 3 rs.2 (z-a)) /
      ((value τ hτ 3 j z)^2*(value τ hτ 3 k a)^2) := by
  rw [actual_addition_formula]
  simp only [coordinate,map_sum,TensorComplexPointSeparation318.evaluation_smul,
    TensorComplexPointSeparation318.evaluation,Algebra.TensorProduct.lift_tmul,
    theta_evaluation,smul_eq_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v hv
  field_simp [hz,ha]
  <;> ring

/-- Rank-one equations hold IN the entire product ring, not merely
pointwise or modulo nilpotents. Genuine pair evaluations separate every
tensor element by the independently proved basis-contraction theorem. -/
theorem rank_one (r r' s s' : Label 3) :
    coordinate τ hτ j k (r,s)*coordinate τ hτ j k (r',s')=
      coordinate τ hτ j k (r,s')*coordinate τ hτ j k (r',s) := by
  apply PELOriginalProductChartPoints318.ext τ hτ j k
  intro f g
  obtain ⟨z,hz,rfl⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ j f
  obtain ⟨a,ha,rfl⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ k g
  simp only [map_mul,evaluation]
  ring

lemma value_vector_nonzero (f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ)
    (g : CoordinateChart τ hτ k →ₐ[ℂ] ℂ) :
    (fun rs => TensorComplexPointSeparation318.evaluation f g (coordinate τ hτ j k rs)) ≠ 0 := by
  obtain ⟨z,hz,rfl⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ j f
  obtain ⟨a,ha,rfl⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ k g
  intro h
  apply PELOriginalAdditionTensorMap318.segre_ne_zero
    (fun r => value τ hτ 3 r (z+a)) (fun s => value τ hτ 3 s (z-a))
    (PELOriginalAllLevelProjectiveMap318.coverVector_nonzero τ hτ 1 (z+a))
    (PELOriginalAllLevelProjectiveMap318.coverVector_nonzero τ hτ 1 (z-a))
  funext rs
  have hr := congrFun h rs
  rw [evaluation] at hr
  change value τ hτ 3 rs.1 (z+a)*value τ hτ 3 rs.2 (z-a)=0
  exact (div_eq_zero_iff.mp hr).resolve_right
    (mul_ne_zero (pow_ne_zero 2 hz) (pow_ne_zero 2 ha))
end PELOriginalRegularAdditionTensor318
