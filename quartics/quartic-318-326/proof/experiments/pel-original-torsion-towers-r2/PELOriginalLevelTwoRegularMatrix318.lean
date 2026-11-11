module
public import PELOriginalLevelTwoCubicProducts318
public import ProperIdealComplexPoint318
public section
noncomputable section
namespace PELOriginalLevelTwoRegularMatrix318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalRatioEvaluationExt318 PELOriginalLevelTwoCubicProducts318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)

/-- Literal rank-one equations hold in the ENTIRE original chart ring,
proved by its faithful full complex point presentation. -/
theorem minors (r u s t : Label 2) :
    coordinate τ hτ j r s * coordinate τ hτ j u t =
      coordinate τ hτ j r t * coordinate τ hτ j u s := by
  apply PELOriginalChartPointSeparation318.ext τ hτ j
  intro f
  obtain ⟨z,hz,rfl⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ j f
  simp only [map_mul,evaluation]
  ring

/-- The four actual theta2 cubes have no scheme-theoretic base locus.
This uses the original level-two basepoint-free family, not level-three
injectivity and not normal generation of its section ring. -/
theorem denominator_span : Ideal.span (Set.range (denominator τ hτ j)) = ⊤ := by
  by_contra h
  obtain ⟨f,hf⟩ := ProperIdealComplexPoint318.exists_point
    (MvPolynomial.aeval (ratioElement τ hτ j)) (polynomial_surjective τ hτ j)
    (Ideal.span (Set.range (denominator τ hτ j))) h
  obtain ⟨z,hz,rfl⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ j f
  apply PELOriginalAllLevelProjectiveMap318.coverVector_nonzero τ hτ 0 z
  funext s
  have he := hf (denominator τ hτ j s) (Ideal.subset_span (Set.mem_range_self s))
  rw [denominator_evaluation] at he
  have hp := (div_eq_zero_iff.mp he).resolve_right (pow_ne_zero 2 hz)
  by_contra hs
  exact (pow_ne_zero 3 hs) hp

/-- Consequently all sixteen entries generate the unit ideal too,
allowing the existing genuine rank-one column scheme gluing. -/
theorem entry_span : Ideal.span (Set.range (fun rs : Label 2 × Label 2 =>
    coordinate τ hτ j rs.1 rs.2)) = ⊤ := by
  apply top_le_iff.mp
  rw [←denominator_span τ hτ j]
  apply Ideal.span_mono
  rintro _ ⟨s,rfl⟩
  exact ⟨(s,s),rfl⟩

/-- The four diagonal principal opens cover ALL prime points. -/
theorem denominator_not_mem (p : Ideal (CoordinateChart τ hτ j)) [p.IsPrime] :
    ∃ s : Label 2, denominator τ hτ j s ∉ p := by
  by_contra h
  push_neg at h
  have he : Ideal.span (Set.range (denominator τ hτ j)) ≤ p := by
    apply Ideal.span_le.mpr
    rintro _ ⟨s,rfl⟩
    exact h s
  rw [denominator_span] at he
  exact p.ne_top (top_le_iff.mp he)
end PELOriginalLevelTwoRegularMatrix318
