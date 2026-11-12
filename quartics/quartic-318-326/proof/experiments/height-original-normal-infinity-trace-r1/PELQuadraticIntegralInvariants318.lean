module
public import PELIntegralOverorder318
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Polynomial.RationalRoot
public section
noncomputable section
namespace PELQuadraticIntegralInvariants318
set_option maxHeartbeats 1000000
variable (a b : ℚ)
abbrev Q := QuadraticAlgebra ℚ a b

/-- Conjugation is used in a genuine COMMUTATIVE quadratic carrier. Integral
elements of the ambient noncommutative quaternion ring are not asserted to
be closed under arbitrary sums or products. -/
theorem star_integral (z : Q a b) (hz : IsIntegral ℤ z) : IsIntegral ℤ (star z) :=
  map_isIntegral_int (starRingEnd (Q a b) : Q a b →+* Q a b) hz

theorem scalar_integral (q : ℚ)
    (hq : IsIntegral ℤ (algebraMap ℚ (Q a b) q)) : IsIntegral ℤ q := by
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ (Q a b))
    QuadraticAlgebra.algebraMap_injective).mp hq

theorem trace_integral (z : Q a b) (hz : IsIntegral ℤ z) :
    ∃ n : ℤ,QuadraticAlgebra.trace z=(n:ℚ) := by
  have hs := star_integral a b z hz
  have hq : IsIntegral ℤ (QuadraticAlgebra.trace z) := scalar_integral a b _ (by
    rw [QuadraticAlgebra.algebraMap_trace_eq_add_star]
    exact hz.add hs)
  obtain ⟨n,hn⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hq
  exact ⟨n,hn.symm⟩

theorem norm_integral (z : Q a b) (hz : IsIntegral ℤ z) :
    ∃ n : ℤ,QuadraticAlgebra.norm z=(n:ℚ) := by
  have hs := star_integral a b z hz
  have hq : IsIntegral ℤ (QuadraticAlgebra.norm z) := scalar_integral a b _ (by
    rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    exact hz.mul hs)
  obtain ⟨n,hn⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hq
  exact ⟨n,hn.symm⟩
end PELQuadraticIntegralInvariants318
