module
public import PELOriginalNegationPrimeAction318
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public section
noncomputable section
namespace PELOriginalNegationSchemePointAction318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open DiscreteComplexPeriodAtlas318 PELOriginalPolarizationTransitions318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalProjectiveNegation318 PELOriginalNegationComplexBase318
open PELOriginalProperComplexCandidate318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Exact morphism-level original inversion square over C. The candidate
map is the independently constructed genuine global scheme automorphism;
the points are the original theta scheme points, with the original source
vector z sent literally to -z, including every chart boundary. -/
theorem original_scheme_point_action (z : ComplexVectors) :
    candidateComplexPoint τ hτ (projection (P τ) z) ≫ candidateNegation τ hτ =
      candidateComplexPoint τ hτ (projection (P τ) (-z)) := by
  apply (cancel_mono (inclusion τ hτ)).mp
  apply ext_of_apply_closedPoint_eq (ComplexProjectiveBase318.structureMap)
  · change ((candidateComplexPoint τ hτ (projection (P τ) z) ≫
      candidateNegation τ hτ) ≫ inclusion τ hτ) ≫
        ComplexProjectiveBase318.structureMap = _
    rw [Category.assoc]
    change (candidateComplexPoint τ hτ (projection (P τ) z) ≫
      candidateNegation τ hτ) ≫ structureMap τ hτ = _
    rw [Category.assoc,candidate_over_complex,candidate_point_over]
  · change (candidateComplexPoint τ hτ (projection (P τ) (-z)) ≫ inclusion τ hτ) ≫
      ComplexProjectiveBase318.structureMap = _
    rw [Category.assoc]
    exact candidate_point_over τ hτ _
  · exact PELOriginalNegationPrimeAction318.candidate_point_action_underlying τ hτ z _
end PELOriginalNegationSchemePointAction318
