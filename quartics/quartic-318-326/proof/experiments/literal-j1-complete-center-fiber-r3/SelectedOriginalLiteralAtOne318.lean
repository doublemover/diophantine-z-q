module
public import SelectedOriginalLiteralScalarUniqueness318
import Mathlib.Tactic.NormNum
public section
noncomputable section

open Polynomial SelectedOriginalLiteralScalarUniqueness318

namespace SelectedOriginalLiteralAtOne318

variable (L : Type*) [Field L] [CharZero L]
variable (N : ℕ) [NeZero N]

@[expose] def polyAtOne : ℤ[X] →+* L :=
  Polynomial.eval₂RingHom (Int.castRingHom L) (1 : L)

theorem denominator_value :
    polyAtOne L (OpenJModel318.denominator N) = (6 * (N : L)) * (1 - 1728) := by
  simp only [polyAtOne, OpenJModel318.denominator, Polynomial.coe_eval₂RingHom,
    eval₂_mul, eval₂_sub, eval₂_natCast, eval₂_ofNat, eval₂_X, mul_one]

theorem denominator_unit : IsUnit (polyAtOne L (OpenJModel318.denominator N)) := by
  rw [denominator_value L N]
  exact isUnit_iff_ne_zero.mpr
    (mul_ne_zero (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (NeZero.ne N))) (by norm_num))

/-- The literal original coefficient map at J=1, constructed on the
original open-j ring, without going through a newly chosen root. -/
@[expose] def atOne : OpenJModel318.Base N →+* L :=
  IsLocalization.Away.lift (OpenJModel318.denominator N) (denominator_unit L N)

theorem atOne_j : atOne L N (OpenJModel318.jCoord N) = 1 := by
  rw [OpenJModel318.jCoord, atOne, IsLocalization.Away.lift_eq]
  exact eval₂_X _ _

theorem atOne_change {E : Type*} [Field E] [CharZero E] (f : L →+* E) :
    f.comp (atOne L N) = atOne E N := by
  apply over_original_j_eq
  rw [RingHom.comp_apply, atOne_j, map_one, atOne_j]

end SelectedOriginalLiteralAtOne318

#print axioms SelectedOriginalLiteralAtOne318.atOne_j
#print axioms SelectedOriginalLiteralAtOne318.atOne_change
