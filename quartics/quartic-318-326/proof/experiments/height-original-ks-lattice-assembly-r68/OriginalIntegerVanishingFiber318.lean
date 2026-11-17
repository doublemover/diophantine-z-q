module
public import OriginalIntegerAffineModel318
public import FourRootVanishingFiber318
public section
noncomputable section
namespace OriginalIntegerVanishingFiber318
open Polynomial
open scoped TensorProduct
variable (c : Fin 4 → ℚˣ)
variable {S : Type*} [CommRing S] [Nontrivial S] [Algebra ℤ[X] S]

/-- If one literal cleared coefficient vanishes in the fiber, the actual
integral model's base change contains a nonzero element with square zero.
This hypothesis is not asserted at every excluded prime. -/
theorem cleared_coefficient_vanishes (i : Fin 4)
    (hi : algebraMap ℤ[X] S
      (C ((c i : ℚ).num * ((c i : ℚ).den : ℤ))) = 0) :
    ∃ x : S ⊗[ℤ[X]] OriginalIntegerAffineModel318.Order c, x ≠ 0 ∧ x^2 = 0 := by
  apply FourRootVanishingFiber318.baseChange_nonzero_square_zero
    (OriginalIntegerAffineModel318.coefficient c) i
  rw [OriginalIntegerAffineModel318.coefficient, map_mul, hi, zero_mul]

/-- A concrete sufficient condition, satisfied when a twist denominator
becomes zero in the residual characteristic. No regularity or normality of
the integral model can remove this calculation for its displayed fiber. -/
theorem denominator_vanishes (i : Fin 4)
    (hi : ((c i : ℚ).den : S) = 0) :
    ∃ x : S ⊗[ℤ[X]] OriginalIntegerAffineModel318.Order c, x ≠ 0 ∧ x^2 = 0 := by
  apply cleared_coefficient_vanishes c i
  have hC (z : ℤ) : algebraMap ℤ[X] S (C z) = (z : S) := by simp
  rw [hC, Int.cast_mul, Int.cast_natCast, hi, mul_zero]

end OriginalIntegerVanishingFiber318
