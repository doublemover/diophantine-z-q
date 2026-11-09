module
public import ReducedVerticalUniformizer318
public import VerticalCotangentSections318
public section
noncomputable section
namespace ReducedVerticalTensorSections318
open scoped TensorProduct
set_option maxHeartbeats 400000
variable {R B K : Type*} [CommRing R] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Field K]
  [Algebra R B] [Algebra B K] [Algebra R K] [IsScalarTower R B K] [IsFractionRing B K]

/-- The literal quadratic differentials have actual integral tensor
preimages at a reduced vertical DVR, including contact-collision primes.
The special-fiber reducedness produces the prime-uniformizer fact; no
irreducibility, derivative estimate or section-integrality premise is supplied. -/
theorem integral_sections (e : KaehlerDifferential R B ≃ₗ[B] B)
    (p : ℕ) (hp0 : (p : B) ≠ 0) (hpu : ¬IsUnit (p : B))
    [IsReduced (B ⧸ Ideal.span ({(p : B)} : Set B))] (t : K) :
    (∃ x0, IntegralCotangentTensor318.map e x0 = VerticalCotangentSections318.q0 (R := R) t) ∧
    (∃ x1, IntegralCotangentTensor318.map e x1 = VerticalCotangentSections318.q1 (R := R) t) :=
  VerticalCotangentSections318.integral_sections e p
    (ReducedVerticalUniformizer318.prime_uniformizer p hp0 hpu) t

end ReducedVerticalTensorSections318
