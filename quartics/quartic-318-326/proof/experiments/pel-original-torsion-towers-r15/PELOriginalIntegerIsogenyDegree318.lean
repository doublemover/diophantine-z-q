module
public import PELOriginalOrderIsogenyDegree318
public section
noncomputable section
namespace PELOriginalIntegerIsogenyDegree318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELPrincipalOrderCoordinates318 PELOriginalOrderIntegralNorm318
open PELOriginalReducedProjectiveCandidate318 PELOriginalIntegerMultiplication318
/-- The actual central integer has quaternion reduced norm n squared. -/
lemma integer_norm (n : ℤ) : norm (n:order)=n^2 := by
  apply Int.cast_injective (R := ℚ)
  rw [norm_value]
  simp [PELQuaternionAlgebra318.reducedNorm]

variable (τ : ℂ) (hτ : 0<τ.im)
/-- Exact native scheme degree n^4 of every nonzero original integer
multiplication, including negative integers, at ALL candidate primes. -/
lemma degree (n : ℤ) (hn : n≠0) (y : candidate τ hτ) :
    (multiplication τ hτ n).finrank y=n.natAbs^4 := by
  rw [←PELOriginalOrderIntegerCompatibility318.integer_morphism]
  rw [PELOriginalOrderIsogenyDegree318.degree τ hτ (n:order)
    (by rw [integer_norm]; exact pow_ne_zero _ hn),integer_norm,Int.natAbs_pow]
  ring
/-- Full arbitrary-test base change preserves the native integer degree. -/
lemma baseChange_degree (n : ℤ) (hn : n≠0) {T : Scheme}
    (p : T⟶candidate τ hτ) (t : T) :
    (pullback.snd (multiplication τ hτ n) p).finrank t=n.natAbs^4 := by
  letI := PELOriginalFiniteSurjectiveMultiplication318.finite τ hτ n hn
  letI := PELOriginalMultiplicationEtale318.etale τ hτ n hn
  rw [Scheme.Hom.finrank_pullback_snd]
  exact degree τ hτ n hn _
end PELOriginalIntegerIsogenyDegree318
