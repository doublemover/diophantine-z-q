module
public import PELOriginalOrderPullbackSections318
public import ProperIdealComplexPoint318
public import PELOriginalChartSchemePointIdentity318
public section
noncomputable section
namespace PELOriginalOrderRegularMatrix318
open QuaternionicRealPeriod318 PELPrincipalOrderCoordinates318
open PELOriginalComplementaryOrder318 PELOriginalComplementaryHermitian318
open PELOriginalOrderPullbackSections318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalRatioEvaluationExt318
variable (τ : ℂ) (hτ : 0 < τ.im) (a : order) (j : Label 3)

theorem minors (r s : Label 3) (c d : Columns) :
    regular τ hτ a j r c*regular τ hτ a j s d=
      regular τ hτ a j r d*regular τ hτ a j s c := by
  apply PELOriginalChartPointSeparation318.ext τ hτ j
  intro f
  obtain ⟨z,hz,rfl⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ j f
  simp only [map_mul,regular_cover,entireValue]
  ring

/-- All actual entries generate the unit ideal in the ENTIRE original
chart ring. Both original cubic basepoint-free families are used; no
nonvanishing of one fixed auxiliary theta function is presumed. -/
theorem entry_span : Ideal.span (Set.range (fun rc : Label 3 × Columns =>
    regular τ hτ a j rc.1 rc.2))=⊤ := by
  by_contra h
  obtain ⟨f,hf⟩ := ProperIdealComplexPoint318.exists_point
    (MvPolynomial.aeval (ratioElement τ hτ j)) (polynomial_surjective τ hτ j)
    (Ideal.span (Set.range (fun rc : Label 3 × Columns => regular τ hτ a j rc.1 rc.2))) h
  obtain ⟨z,hz,rfl⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ j f
  obtain ⟨i,hi⟩ := PELOriginalChartSchemePointIdentity318.cover_nonzero τ hτ (linear a z)
  obtain ⟨k,hk⟩ := PELOriginalChartSchemePointIdentity318.cover_nonzero τ hτ (linear (complement a) z)
  have he := hf (regular τ hτ a j i (i,k,k))
    (Ideal.subset_span (Set.mem_range_self (i,(i,k,k))))
  rw [regular_cover] at he
  exact (div_ne_zero (by simpa only [entireValue] using
    mul_ne_zero (mul_ne_zero (mul_ne_zero hi hi) hk) hk)
    (pow_ne_zero _ hz)) he
end PELOriginalOrderRegularMatrix318
