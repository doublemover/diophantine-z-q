module
public import PELOriginalIntegerIsogenyDegree318
public section
noncomputable section
namespace PELOriginalOrderDegreeLaws318
open AlgebraicGeometry CategoryTheory PELPrincipalOrderCoordinates318
open PELQuaternionAlgebra318 PELOriginalOrderIntegralNorm318
open PELOriginalReducedProjectiveCandidate318 PELOriginalOrderSchemeMorphism318
/-- Multiplicativity of the literal original integral reduced norm. -/
lemma norm_mul (a b : order) : norm (a*b)=norm a*norm b := by
  apply Int.cast_injective (R := ℚ)
  push_cast
  rw [norm_value,norm_value,norm_value]
  change reducedNorm ((a:B)*(b:B))=reducedNorm (a:B)*reducedNorm (b:B)
  simp [reducedNorm]
  ring
/-- The actual positive involution preserves the original reduced norm;
this does not identify it with standard quaternion conjugation. -/
lemma norm_adjoint (a : order) :
    norm (PELOriginalOrderHermitianAdjoint318.adjoint a)=norm a := by
  apply Int.cast_injective (R := ℚ)
  rw [norm_value,norm_value]
  change reducedNorm (rosati (a:B))=reducedNorm (a:B)
  rw [rosati_coordinates]
  simp [reducedNorm]

variable (τ : ℂ) (hτ : 0<τ.im)
/-- The genuine native degree is multiplicative for actual order maps,
retaining categorical composition a then b = the order product b*a. -/
lemma composition_degree (a b : order) (ha : norm a≠0) (hb : norm b≠0)
    (y : candidate τ hτ) :
    (morphism τ hτ a≫morphism τ hτ b).finrank y=
      (norm a).natAbs^2*(norm b).natAbs^2 := by
  rw [PELOriginalOrderSchemeLaws318.morphism_comp,
    PELOriginalOrderIsogenyDegree318.degree τ hτ (b*a)
      (by rw [norm_mul]; exact mul_ne_zero hb ha),norm_mul,Int.natAbs_mul]
  ring
/-- SAME normalized-family Rosati adjoint, now with equal native degree. -/
lemma adjoint_degree (a : order) (ha : norm a≠0) (y : candidate τ hτ) :
    (morphism τ hτ (PELOriginalOrderHermitianAdjoint318.adjoint a)).finrank y=
      (morphism τ hτ a).finrank y := by
  rw [PELOriginalOrderIsogenyDegree318.degree τ hτ _
      (by rw [norm_adjoint]; exact ha),
    PELOriginalOrderIsogenyDegree318.degree τ hτ a ha,norm_adjoint]
end PELOriginalOrderDegreeLaws318
