module
public import PELOriginalOrderNormComposites318
public import ProperFiniteFiberDescent318
public section
noncomputable section
namespace PELOriginalFiniteOrderIsogeny318
open AlgebraicGeometry CategoryTheory PELPrincipalOrderCoordinates318
open PELOriginalProductChartCover318 PELOriginalOrderSchemeMorphism318
open PELOriginalOrderIntegralNorm318
variable (τ : ℂ) (hτ : 0 < τ.im) (a : order)
lemma proper : IsProper (morphism τ hτ a) := by
  letI : IsProper (morphism τ hτ a≫π τ hτ) := by
    rw [over_complex]
    infer_instance
  exact IsProper.of_comp (morphism τ hτ a) (π τ hτ)
/-- Every original order element with nonzero ACTUAL reduced norm is a
finite scheme morphism on the SAME candidate. The proof descends finite
full fibers of the literal norm composite through its surjective
conjugate map; no finite-closed-point surrogate is used. -/
lemma finite (ha : norm a≠0) : IsFinite (morphism τ hτ a) := by
  letI := proper τ hτ a
  letI : IsFinite (morphism τ hτ (conjugate a)≫morphism τ hτ a) := by
    rw [PELOriginalOrderNormComposites318.right]
    exact PELOriginalFiniteSurjectiveMultiplication318.finite τ hτ (norm a) ha
  exact ProperFiniteFiberDescent318.finite (morphism τ hτ (conjugate a)) (morphism τ hτ a)
    (PELOriginalOrderNormComposites318.conjugate_surjective τ hτ a ha)
lemma finite_surjective (ha : norm a≠0) :
    IsFinite (morphism τ hτ a) ∧ Function.Surjective (morphism τ hτ a) :=
  ⟨finite τ hτ a ha,PELOriginalOrderNormComposites318.surjective τ hτ a ha⟩
end PELOriginalFiniteOrderIsogeny318
