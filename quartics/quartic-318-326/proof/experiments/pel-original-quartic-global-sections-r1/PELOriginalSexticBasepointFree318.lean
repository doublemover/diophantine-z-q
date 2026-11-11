module
public import PELOriginalSexticRegularization318
public import ProperIdealComplexPoint318
public section
noncomputable section
namespace PELOriginalSexticBasepointFree318
open QuaternionicRealPeriod318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalRatioEvaluationExt318 PELOriginalSexticRegularization318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)

/-- The actual 36 whole sextic ratios generate the UNIT ideal in the
entire original chart. This is a scheme-theoretic basepoint-free statement,
not only nonvanishing on selected points or on a primitive open. -/
theorem span_eq_top : Ideal.span (Set.range (theta τ hτ j)) = ⊤ := by
  by_contra h
  obtain ⟨f,hf⟩ := ProperIdealComplexPoint318.exists_point
    (MvPolynomial.aeval (ratioElement τ hτ j)) (polynomial_surjective τ hτ j)
    (Ideal.span (Set.range (theta τ hτ j))) h
  obtain ⟨z,hz,rfl⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ j f
  apply PELOriginalAllLevelProjectiveMap318.coverVector_nonzero τ hτ 4 z
  funext r
  have hr := hf (theta τ hτ j r) (Ideal.subset_span (Set.mem_range_self r))
  rw [theta_evaluation] at hr
  have hn := (div_eq_zero_iff).mp hr
  exact hn.resolve_right (pow_ne_zero 2 hz)

/-- Every prime misses at least one of the actual regular sextic
coordinates. The open cover is therefore a cover of ALL scheme points. -/
theorem exists_not_mem (p : Ideal (CoordinateChart τ hτ j)) [p.IsPrime] :
    ∃ r : Label 6, theta τ hτ j r ∉ p := by
  by_contra h
  push_neg at h
  have hs : Ideal.span (Set.range (theta τ hτ j)) ≤ p := by
    apply Ideal.span_le.mpr
    rintro _ ⟨r,rfl⟩
    exact h r
  rw [span_eq_top] at hs
  exact p.ne_top (top_le_iff.mp hs)
end PELOriginalSexticBasepointFree318
