module
public import KilledUniformizerSections318
public import ReducedVerticalTensorSections318
public section
noncomputable section
namespace ReducedBaseTensorSections318
open scoped TensorProduct
set_option maxHeartbeats 400000
variable {R B K : Type*} [CommRing R] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Field K]
  [Algebra R B] [Algebra B K] [Algebra R K] [IsScalarTower R B K] [IsFractionRing B K]

/-- Relative differentiation kills the actual base parameter, including
ramified base uniformizers; no replacement by a rational prime occurs. -/
theorem derived_kills_base (e : KaehlerDifferential R B ≃ₗ[B] B) (r : R) :
    FractionSourceSections318.derived (K := K) e
      (algebraMap B K (algebraMap R B r)) = 0 := by
  rw [FractionSourceSections318.derived_integral, Derivation.map_algebraMap, map_zero]

/-- Actual integral tensor preimages under precisely reduced base-fiber
geometry. This handles a ramified base parameter without assuming the
rational prime has multiplicity one in B. -/
theorem integral_sections (e : KaehlerDifferential R B ≃ₗ[B] B)
    (r : R) (hr0 : algebraMap R B r ≠ 0) (hru : ¬IsUnit (algebraMap R B r))
    [IsReduced (B ⧸ Ideal.span ({algebraMap R B r} : Set B))] (t : K) :
    (∃ x0, IntegralCotangentTensor318.map e x0 = VerticalCotangentSections318.q0 (R := R) t) ∧
    (∃ x1, IntegralCotangentTensor318.map e x1 = VerticalCotangentSections318.q1 (R := R) t) := by
  have hirr := ReducedVerticalUniformizer318.irreducible_of_reduced_quotient
    (algebraMap R B r) hr0 hru
  obtain ⟨h0,h1⟩ := KilledUniformizerSections318.sections_integral
    (FractionSourceSections318.derived (K := K) e)
    (FractionSourceSections318.derived_preserves e) (algebraMap R B r) hirr
    (derived_kills_base e r) t
  constructor
  · apply (IntegralCotangentTensor318.integral_iff e (VerticalCotangentSections318.q0 t)).mpr
    rwa [VerticalCotangentSections318.q0_coefficient]
  · apply (IntegralCotangentTensor318.integral_iff e (VerticalCotangentSections318.q1 t)).mpr
    rwa [VerticalCotangentSections318.q1_coefficient]

end ReducedBaseTensorSections318
