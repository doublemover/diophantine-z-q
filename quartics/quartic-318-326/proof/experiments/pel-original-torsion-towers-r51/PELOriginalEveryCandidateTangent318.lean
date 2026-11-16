module
public import PELOriginalCandidateSchemeTangent318
public import PELOriginalFullCandidateSchemePoints318
public section
noncomputable section
namespace PELOriginalEveryCandidateTangent318
open AlgebraicGeometry CategoryTheory
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateSchemeTangent318
open EvaluationDualNumberLift318
variable (τ : ℂ) (hτ : 0 < τ.im)
/-- EVERY actual candidate complex point carries the injective original
analytic family of genuine dual-number tangents over the original base.
The full point theorem supplies the source chart, including boundaries;
no algebraic tangent surjectivity or smoothness is smuggled in. -/
theorem every_point (p : Spec (CommRingCat.of ℂ) ⟶ candidate τ hτ)
    (hp : p ≫ PELOriginalProperComplexCandidate318.structureMap τ hτ = 𝟙 _) :
    ∃ x : ComplexVectors, ∃ j : Label 3, ∃ hj : value τ hτ 3 j x ≠ 0,
      center τ hτ x j hj = p ∧
      Function.Injective (tangent τ hτ x j hj) ∧
      (∀ v, origin ≫ tangent τ hτ x j hj v = p) ∧
      (∀ v, tangent τ hτ x j hj v ≫ PELOriginalProperComplexCandidate318.structureMap τ hτ =
        Spec.map (CommRingCat.ofHom (algebraMap ℂ Dual))) := by
  obtain ⟨j,x,hj,hp'⟩ := PELOriginalFullCandidateSchemePoints318.every_candidate_point τ hτ p hp
  have hc : center τ hτ x j hj = p := hp'.symm
  exact ⟨x,j,hj,hc,tangent_injective τ hτ x j hj,
    fun v => (origin_tangent τ hτ x j hj v).trans hc,
    tangent_over_complex τ hτ x j hj⟩
end PELOriginalEveryCandidateTangent318
