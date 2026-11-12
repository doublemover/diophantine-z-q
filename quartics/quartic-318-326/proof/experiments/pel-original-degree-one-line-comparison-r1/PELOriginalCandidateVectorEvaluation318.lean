module
public import PELOriginalFullLocalizedPoints318
public section
noncomputable section
namespace PELOriginalCandidateVectorEvaluation318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalCubicRelationIdeal318
open PELOriginalChartSectionField318 PELOriginalChartAnalyticEvaluation318
open HomogeneousQuotientChart318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
variable (v : Label 3 → ℂ)
variable (hv : ∀ p ∈ relations τ hτ, MvPolynomial.eval v p = 0) (hj : v j ≠ 0)

/-- Evaluation at an independent vector satisfying every literal
original homogeneous relation. No original-image witness is assumed. -/
@[expose] def evaluation : CoordinateChart τ hτ j →ₐ[ℂ] ℂ :=
  { HomogeneousQuotientPointEvaluation318.evaluation (relations τ hτ) v hv j hj with
    commutes' := by
      intro c
      change HomogeneousQuotientPointEvaluation318.evaluation (relations τ hτ) v hv j hj
        (scalarMap τ hτ j c) = c
      rw [scalar_fraction,HomogeneousQuotientPointEvaluation318.fraction_evaluation]
      simp only [MvPolynomial.eval_C,pow_zero,div_one] }

lemma evaluation_ratio (i : Label 3) :
    evaluation τ hτ j v hv hj (ratioElement τ hτ j i) = v i / v j := by
  change HomogeneousQuotientPointEvaluation318.evaluation (relations τ hτ) v hv j hj
    ((quotientMap (relations τ hτ) j).rangeRestrict
      (fraction j 1 (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X ℂ i))) = _
  rw [HomogeneousQuotientPointEvaluation318.fraction_evaluation]
  simp only [MvPolynomial.eval_X,pow_one]
end PELOriginalCandidateVectorEvaluation318
