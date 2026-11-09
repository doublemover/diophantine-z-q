module
public import LocalBranchEquationOrders318
public import Mathlib.RingTheory.RamificationInertia.Ramification
public section
noncomputable section
namespace CanonicalDVRQuotientLength318
open IsDiscreteValuationRing IsLocalRing
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The canonical local order is the ACTUAL module length of the quotient
by the original element, with no chosen valuation normalization. -/
theorem length_span (x : R) (hx : x ≠ 0) :
    Module.length R (R ⧸ Ideal.span {x}) = addVal R x := by
  obtain ⟨π,hπ⟩ := exists_irreducible R
  obtain ⟨n,u,rfl⟩ := eq_unit_mul_pow_irreducible hx hπ
  rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
    ← hπ.maximalIdeal_eq, length_quotient_pow_maximalIdeal,
    addVal_mul, addVal_eq_zero_of_unit, hπ.addVal_pow, zero_add]
end CanonicalDVRQuotientLength318
