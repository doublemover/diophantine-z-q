module

public import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Cast.Order

public section

namespace CheckedHomogeneousTwistPoint318

/-- Integer data for an affine point on the twist with parameter m. The
denominator pertains to x/m; the ordinate is m² times c/b². -/
structure Certificate where
  a : ℤ
  b : ℤ
  c : ℤ

/-- This is an exact point check, not a rank, local solubility, or
primitivity test. It excludes the zero ordinate. -/
@[expose] def check (m : ℤ) (k : Certificate) : Bool :=
  decide (0 < k.b ∧ k.c ≠ 0 ∧
    k.a * k.b * (k.a - k.b) * (k.a + 3 * k.b) = m * k.c ^ 2)

/-- Recover the two coordinates on the same input twist. Only this adapter,
not the closed check, needs m to be nonzero. -/
theorem exists_affine_of_check {m : ℤ} {k : Certificate}
    (hm : m ≠ 0) (hk : check m k = true) :
    ∃ x y : ℚ, y ≠ 0 ∧ y ^ 2 = x * (x - (m : ℚ)) * (x + 3 * (m : ℚ)) := by
  have h : 0 < k.b ∧ k.c ≠ 0 ∧
      k.a * k.b * (k.a - k.b) * (k.a + 3 * k.b) = m * k.c ^ 2 :=
    of_decide_eq_true hk
  have hb : (k.b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr h.1.ne'
  have hc : (k.c : ℚ) ≠ 0 := Int.cast_ne_zero.mpr h.2.1
  have hmQ : (m : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hm
  have heq : (k.a : ℚ) * (k.b : ℚ) * ((k.a : ℚ) - (k.b : ℚ)) *
      ((k.a : ℚ) + 3 * (k.b : ℚ)) = (m : ℚ) * (k.c : ℚ) ^ 2 := by
    simpa only [Int.cast_mul, Int.cast_sub, Int.cast_add, Int.cast_pow, Int.cast_ofNat]
      using congrArg (fun z : ℤ => (z : ℚ)) h.2.2
  refine ⟨(m : ℚ) * (k.a : ℚ) / (k.b : ℚ),
    (m : ℚ)^2 * (k.c : ℚ) / (k.b : ℚ)^2, ?_, ?_⟩
  · exact div_ne_zero (mul_ne_zero (pow_ne_zero _ hmQ) hc) (pow_ne_zero _ hb)
  · calc
      ((m : ℚ)^2 * (k.c : ℚ) / (k.b : ℚ)^2)^2 =
          (m : ℚ)^3 * ((m : ℚ) * (k.c : ℚ)^2) / (k.b : ℚ)^4 := by
            ring
      _ = (m : ℚ) * (k.a : ℚ) / (k.b : ℚ) *
          ((m : ℚ) * (k.a : ℚ) / (k.b : ℚ) - (m : ℚ)) *
          ((m : ℚ) * (k.a : ℚ) / (k.b : ℚ) + 3 * (m : ℚ)) := by
            rw [← heq]
            field_simp [hb]

end CheckedHomogeneousTwistPoint318
