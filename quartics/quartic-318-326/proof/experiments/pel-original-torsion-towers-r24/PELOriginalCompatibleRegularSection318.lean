module
public import PELOriginalWholePowerRegularization318
public import PELOriginalChartSchemePointIdentity318
public section
noncomputable section
namespace PELOriginalCompatibleRegularSection318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalChartEvaluationRegularity318 PELOriginalPolarizationAutomorphy318
open PELOriginalPowerSectionDescent318 PELOriginalSectionMultiplication318
open PELOriginalWholeHZeroDimension318 PELOriginalAutomorphyRepresentatives318
open Filter Topology
variable (τ : ℂ) (hτ : 0 < τ.im) (m : ℕ)

/-- Compatible actual WHOLE affine ring elements. The compatibility is
an evaluation consequence of the whole algebraic cocycle in the final
consumer; holomorphy is not an additional premise. -/
structure Data where
  element : ∀ j : Label 3, CoordinateChart τ hτ j
  compatible : ∀ (j k : Label 3) (z : ComplexVectors)
    (hj : value τ hτ 3 j z≠0) (hk : value τ hτ 3 k z≠0),
    algebraEvaluation τ hτ z j hj (element j)*(value τ hτ 3 j z)^m=
      algebraEvaluation τ hτ z k hk (element k)*(value τ hτ 3 k z)^m

@[expose] def index (z : ComplexVectors) : Label 3 :=
  Classical.choose (PELOriginalChartSchemePointIdentity318.cover_nonzero τ hτ z)
lemma index_nonzero (z : ComplexVectors) : value τ hτ 3 (index τ hτ z) z≠0 :=
  Classical.choose_spec (PELOriginalChartSchemePointIdentity318.cover_nonzero τ hτ z)

@[expose] def entireValue (D : Data τ hτ m) (z : ComplexVectors) : ℂ :=
  algebraEvaluation τ hτ z (index τ hτ z) (index_nonzero τ hτ z)
    (D.element (index τ hτ z)) * (value τ hτ 3 (index τ hτ z) z)^m

theorem chart_formula (D : Data τ hτ m) (j : Label 3) (z : ComplexVectors)
    (hz : value τ hτ 3 j z≠0) :
    entireValue τ hτ m D z=algebraEvaluation τ hτ z j hz (D.element j)*(value τ hτ 3 j z)^m :=
  D.compatible _ j z _ hz

/-- Local regular functions on the actual original theta charts are
entire after their EXACT cubic power is restored. No GAGA is invoked. -/
theorem entire (D : Data τ hτ m) : Differentiable ℂ (entireValue τ hτ m D) := by
  intro z
  let j := index τ hτ z
  have hj : value τ hτ 3 j z≠0 := index_nonzero τ hτ z
  have he : entireValue τ hτ m D =ᶠ[𝓝 z]
      (fun w => evaluate τ hτ j (D.element j) w*(value τ hτ 3 j w)^m) := by
    filter_upwards [(holomorphic τ hτ 3 j).continuous.continuousAt.eventually_ne hj] with w hw
    rw [chart_formula τ hτ m D j w hw,evaluate_on_chart τ hτ j _ w hw]
  exact (((contDiffAt_evaluate τ hτ j (D.element j) z hj).differentiableAt (by simp)).mul
    ((holomorphic τ hτ 3 j z).pow m)).congr_of_eventuallyEq he

lemma evaluation_period (j : Label 3) (c : CoordinateChart τ hτ j)
    (l : L τ hτ) (z : ComplexVectors) (hz : value τ hτ 3 j z≠0)
    (hzl : value τ hτ 3 j (z+l.val)≠0) :
    algebraEvaluation τ hτ (z+l.val) j hzl c=algebraEvaluation τ hτ z j hz c := by
  change pointEvaluation τ hτ (z+l.val) j hzl c=pointEvaluation τ hτ z j hz c
  simp only [pointEvaluation,projection_add_period]

/-- The full ORIGINAL automorphy law, not merely periodicity or an
unidentified flat twist, follows from the genuine chart ring points. -/
theorem automorphy (D : Data τ hτ m) (l : L τ hτ) (z : ComplexVectors) :
    entireValue τ hτ m D (z+l.val)=factor τ hτ l z^(3*m)*entireValue τ hτ m D z := by
  let j := index τ hτ z
  have hj : value τ hτ 3 j z≠0 := index_nonzero τ hτ z
  have hjl : value τ hτ 3 j (z+l.val)≠0 := by
    rw [PELOriginalLevelPowerSections318.original_automorphy]
    exact mul_ne_zero (pow_ne_zero _ (nonzero τ hτ l z)) hj
  rw [chart_formula τ hτ m D j _ hjl,chart_formula τ hτ m D j _ hj,
    evaluation_period,PELOriginalLevelPowerSections318.original_automorphy,mul_pow,←pow_mul]
  ring

@[expose] def automorphic (D : Data τ hτ m) : OriginalAutomorphic τ hτ (3*m) where
  value := entireValue τ hτ m D
  entire := entire τ hτ m D
  lattice_rule := automorphy τ hτ m D

/-- Recovered section of the independently defined original full
holomorphic bundle section space, including degree zero. -/
@[expose] def recovered (D : Data τ hτ m) : homogeneous τ hτ (3*m) :=
  ⟨(descend τ hτ (3*m) (automorphic τ hτ m D)).value,
    (descend τ hτ (3*m) (automorphic τ hτ m D)).holomorphic⟩

/-- Full chart regularization is the exact original supplied element,
not merely an element agreeing on a smaller localization. -/
theorem regularization_recovered (D : Data τ hτ m) (j : Label 3) :
    PELOriginalWholePowerRegularization318.linear τ hτ m j (recovered τ hτ m D)=D.element j := by
  apply PELOriginalChartPointSeparation318.ext τ hτ j
  intro f
  obtain ⟨z,hz,rfl⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ j f
  rw [PELOriginalWholePowerRegularization318.cover_evaluation]
  change PELOriginalPowerSectionLift318.lift τ hτ (3*m)
    (asSection τ hτ (3*m) (recovered τ hτ m D)) z/(value τ hτ 3 j z)^m=_
  rw [recovered,lift_descend]
  change entireValue τ hτ m D z/(value τ hτ 3 j z)^m=_
  rw [chart_formula τ hτ m D j z hz,mul_div_cancel_right₀ _ (pow_ne_zero _ hz)]
end PELOriginalCompatibleRegularSection318
