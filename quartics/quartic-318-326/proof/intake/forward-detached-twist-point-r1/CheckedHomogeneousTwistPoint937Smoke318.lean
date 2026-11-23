module

public import CheckedHomogeneousTwistPoint318

public section

namespace CheckedHomogeneousTwistPoint937Smoke318

open CheckedHomogeneousTwistPoint318

/-- Detached arithmetic controls: these are not a source index or a Request. -/
@[expose] def first : Certificate := ⟨59151481, 38318848, -106050280386960⟩

@[expose] def second : Certificate :=
  ⟨100724351641, 70629156016, -9885122309276171100⟩

theorem first_accepts : check 731 first = true := by decide +kernel
theorem second_accepts : check (731 * 937) second = true := by decide +kernel

theorem ordinate_sign_also_accepts : check 731 { first with c := -first.c } = true := by
  decide +kernel

theorem wrong_ordinate_rejects : check 731 { first with c := first.c + 1 } = false := by
  decide +kernel

theorem wrong_arm_rejects : check 731 second = false := by decide +kernel

theorem other_wrong_arm_rejects : check (731 * 937) first = false := by decide +kernel

theorem zero_denominator_rejects : check 731 { first with b := 0 } = false := by
  decide +kernel

theorem negative_denominator_rejects : check 731 { first with b := -first.b } = false := by
  decide +kernel

/-- Deliberately satisfy the polynomial identity, so this control tests the
separate nonzero ordinate guard. -/
theorem torsion_ordinate_rejects : check 731 ⟨1, 1, 0⟩ = false := by decide +kernel

theorem first_affine : ∃ x y : ℚ, y ≠ 0 ∧ y^2 = x * (x - 731) * (x + 3 * 731) :=
  exists_affine_of_check (by decide : (731 : ℤ) ≠ 0) first_accepts

theorem second_affine : ∃ x y : ℚ,
    y ≠ 0 ∧ y^2 = x * (x - (731 * 937)) * (x + 3 * (731 * 937)) := by
  have hp := exists_affine_of_check (by decide : (731 * 937 : ℤ) ≠ 0) second_accepts
  simpa only [Int.cast_mul, Int.cast_ofNat] using hp

end CheckedHomogeneousTwistPoint937Smoke318
