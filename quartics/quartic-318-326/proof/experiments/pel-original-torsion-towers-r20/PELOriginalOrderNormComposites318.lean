module
public import PELOriginalOrderIntegralNorm318
public import PELOriginalFiniteSurjectiveMultiplication318
public section
noncomputable section
namespace PELOriginalOrderNormComposites318
open AlgebraicGeometry CategoryTheory PELPrincipalOrderCoordinates318
open PELOriginalOrderSchemeMorphism318 PELOriginalOrderIntegralNorm318
variable (τ : ℂ) (hτ : 0 < τ.im) (a : order)
lemma left : morphism τ hτ a≫morphism τ hτ (conjugate a)=
    PELOriginalIntegerMultiplication318.multiplication τ hτ (norm a) := by
  rw [PELOriginalOrderSchemeLaws318.morphism_comp,conjugate_mul,
    PELOriginalOrderIntegerCompatibility318.integer_morphism]
lemma right : morphism τ hτ (conjugate a)≫morphism τ hτ a=
    PELOriginalIntegerMultiplication318.multiplication τ hτ (norm a) := by
  rw [PELOriginalOrderSchemeLaws318.morphism_comp,mul_conjugate,
    PELOriginalOrderIntegerCompatibility318.integer_morphism]
/-- Surjectivity on ALL scheme primes follows from the actual integer
norm composite, not only invertibility on the analytic covering vector. -/
lemma surjective (ha : norm a≠0) : Function.Surjective (morphism τ hτ a) := by
  intro y
  obtain ⟨x,hx⟩ := PELOriginalFiniteSurjectiveMultiplication318.surjective τ hτ (norm a) ha y
  refine ⟨morphism τ hτ (conjugate a) x,?_⟩
  change (morphism τ hτ (conjugate a)≫morphism τ hτ a) x=y
  rw [right]
  exact hx
lemma conjugate_surjective (ha : norm a≠0) : Function.Surjective (morphism τ hτ (conjugate a)) := by
  intro y
  obtain ⟨x,hx⟩ := PELOriginalFiniteSurjectiveMultiplication318.surjective τ hτ (norm a) ha y
  refine ⟨morphism τ hτ a x,?_⟩
  change (morphism τ hτ a≫morphism τ hτ (conjugate a)) x=y
  rw [left]
  exact hx
end PELOriginalOrderNormComposites318
