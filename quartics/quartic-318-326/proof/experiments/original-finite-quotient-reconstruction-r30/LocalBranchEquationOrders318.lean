module
public import AffinePrimeOriginalInertia318
public section
noncomputable section
namespace LocalBranchEquationOrders318
open IsLocalRing IsDiscreteValuationRing
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- A genuine local parameter equation gives canonical index one. -/
lemma unramified (x : R) (hx : x ≠ 0)
    (h : maximalIdeal R = Ideal.span {x}) : addVal R x = 1 := by
  exact addVal_uniformizer (irreducible_of_span_eq_maximalIdeal x hx h)

/-- A genuine quadratic branch equation with a unit coefficient gives
canonical index two on the SAME local ring. -/
lemma quadratic (x π : R) (hπ : π ≠ 0)
    (hparam : maximalIdeal R = Ideal.span {π})
    (u : Rˣ) (heq : x = (u : R) * π ^ 2) : addVal R x = 2 := by
  have hp : Irreducible π := irreducible_of_span_eq_maximalIdeal π hπ hparam
  rw [heq, addVal_mul, addVal_eq_zero_of_unit, hp.addVal_pow, zero_add]
  norm_num
end LocalBranchEquationOrders318
