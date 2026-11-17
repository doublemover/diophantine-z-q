module
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Tactic
public section
noncomputable section
namespace RCBinaryDigit318

/-- Lucas at a binary place, with the result kept in the actual two-element
coefficient field. This is not an assumed digit-polynomial representation. -/
theorem choose_two_pow (n j : ℕ) :
    (n.choose (2 ^ j) : ZMod 2) = (n / 2 ^ j : ℕ) := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
      have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
        (n := n) (k := 2 ^ (j + 1)) (p := 2)
      have hk : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ']
      have hcast : (n.choose (2 ^ (j + 1)) : ZMod 2) =
          ((n / 2).choose (2 ^ j) : ℕ) := by
        have hh := (ZMod.natCast_eq_natCast_iff _ _ 2).mpr h
        simpa [hk] using hh
      rw [hcast, ih]
      simp only [Nat.div_div_eq_div_mul, hk]

/-- Vanishing of the actual first M binomial digits forces the stated
integer divisibility, including the vacuous M=0 case. -/
theorem pow_two_dvd_of_choose_zero (n M : ℕ)
    (h : ∀ j < M, (n.choose (2 ^ j) : ZMod 2) = 0) :
    2 ^ M ∣ n := by
  induction M generalizing n with
  | zero => simp
  | succ M ih =>
      have hn : 2 ∣ n := by
        have hz := h 0 (by omega)
        simpa only [pow_zero, Nat.choose_one_right, ZMod.natCast_eq_zero_iff]
          using hz
      have hhalf : 2 ^ M ∣ n / 2 := by
        apply ih
        intro j hj
        rw [choose_two_pow]
        have hz := h (j + 1) (by omega)
        rw [choose_two_pow] at hz
        simpa only [Nat.div_div_eq_div_mul, pow_succ', Nat.mul_comm] using hz
      obtain ⟨a,ha⟩ := hhalf
      refine ⟨a, ?_⟩
      calc
        n = 2 * (n / 2) := (Nat.mul_div_cancel' hn).symm
        _ = 2 ^ (M + 1) * a := by rw [ha, pow_succ']; ac_rfl

end RCBinaryDigit318
