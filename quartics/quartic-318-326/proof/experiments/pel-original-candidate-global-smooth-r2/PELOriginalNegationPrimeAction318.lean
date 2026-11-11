module
public import PELOriginalNegationComplexBase318
public section
noncomputable section
namespace PELOriginalNegationPrimeAction318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open DiscreteComplexPeriodAtlas318 PELOriginalPolarizationTransitions318
open PELOriginalCubicRelationIdeal318 PELOriginalNegationRelations318
open PELOriginalProjectiveNegation318 PELOriginalReducedProjectiveCandidate318
open PELOriginalProjectiveCandidatePoints318 PELOriginalCandidateComplexPoints318
open PELOriginalAllLevelProjectiveMap318 PELOriginalChartAnalyticEvaluation318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Actual marked homogeneous-prime membership is computed in the
original covering gauge, with its nonzero scalar explicitly canceled. -/
lemma originalPoint_cover_mem (z : ComplexVectors) (p : Equations) (n : ℕ)
    (hp : p.IsHomogeneous n) :
    p ∈ (originalPoint τ hτ (projection (P τ) z)).asHomogeneousIdeal ↔
      MvPolynomial.eval (coverVector τ hτ 1 z) p = 0 := by
  rw [originalPoint_homogeneous τ hτ _ p n hp]
  obtain ⟨c,hc,he⟩ := actual_cover_scalar τ hτ z
  rw [←he]
  change MvPolynomial.eval (fun i => c * coverVector τ hτ 1 z i) p = 0 ↔ _
  rw [HomogeneousEvaluationScaling318.evaluate_scale p n hp]
  simp only [mul_eq_zero,pow_ne_zero n hc,false_or]

/-- Exact action on the actual ORIGINAL homogeneous-prime points;
all homogeneous degrees, including degree zero, are tested. -/
theorem original_prime_action (z : ComplexVectors) :
    ambientNegation (originalPoint τ hτ (projection (P τ) z)) =
      originalPoint τ hτ (projection (P τ) (-z)) := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n p hp
  change polynomialNegation p ∈
      (originalPoint τ hτ (projection (P τ) z)).asHomogeneousIdeal ↔
    p ∈ (originalPoint τ hτ (projection (P τ) (-z))).asHomogeneousIdeal
  rw [originalPoint_cover_mem τ hτ z _ n (polynomialNegation_homogeneous p n hp),
    polynomialNegation_value,originalPoint_cover_mem τ hτ (-z) p n hp]

/-- The actual transformed candidate complex-valued morphism and the
actual negative original point have identical ambient underlying points.
This is deliberately a point assertion until the over-C uniqueness
comparison upgrades it to equality of scheme morphisms. -/
lemma candidate_point_action_underlying (z : ComplexVectors)
    (x : ComplexProjectiveSchemePoint318.ComplexPoint) :
    inclusion τ hτ
      ((candidateComplexPoint τ hτ (projection (P τ) z) ≫ candidateNegation τ hτ) x) =
      inclusion τ hτ (candidateComplexPoint τ hτ (projection (P τ) (-z)) x) := by
  calc
    _ = ambientNegation (inclusion τ hτ
        (candidateComplexPoint τ hτ (projection (P τ) z) x)) :=
      congrArg (fun f : candidate τ hτ ⟶ ambient =>
        f (candidateComplexPoint τ hτ (projection (P τ) z) x))
        (candidateNegation_inclusion τ hτ)
    _ = _ := by
      rw [candidateComplexPoint_underlying,original_prime_action,candidateComplexPoint_underlying]
end PELOriginalNegationPrimeAction318
