module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Rational separation from integers

These lemmas formalize the denominator-gap argument in section 6 of
`z-in-q-exact-value-bridge-audit.txt` and `z-in-q-variable-shift-bridge.txt`.
-/

public section

namespace ZInQ

private theorem sub_int_eq_num_sub_mul_den_div (q : ℚ) (n : ℤ) :
    q - (n : ℚ) = ((q.num - n * (q.den : ℤ) : ℤ) : ℚ) / (q.den : ℚ) := by
  have hd : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  calc
    q - (n : ℚ) = (q.num : ℚ) / (q.den : ℚ) - (n : ℚ) := by
      rw [q.num_div_den]
    _ = ((q.num : ℚ) - (n : ℚ) * (q.den : ℚ)) / (q.den : ℚ) := by
      rw [sub_div, mul_div_cancel_right₀ _ hd]
    _ = ((q.num - n * (q.den : ℤ) : ℤ) : ℚ) / (q.den : ℚ) := by
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast]

/-- A nonintegral rational is separated from an integer by its inverse denominator. -/
theorem inv_den_le_abs_sub_int (q : ℚ) (n : ℤ) (hne : q ≠ (n : ℚ)) :
    (q.den : ℚ)⁻¹ ≤ |q - (n : ℚ)| := by
  have hid := sub_int_eq_num_sub_mul_den_div q n
  have hm : q.num - n * (q.den : ℤ) ≠ 0 := by
    intro hzero
    apply hne
    apply sub_eq_zero.mp
    rw [hid, hzero, Int.cast_zero, zero_div]
  have hInt : (1 : ℤ) ≤ |q.num - n * (q.den : ℤ)| := by
    have hpos := abs_pos.mpr hm
    omega
  have hRat : (1 : ℚ) ≤ |((q.num - n * (q.den : ℤ) : ℤ) : ℚ)| := by
    exact_mod_cast hInt
  have hd : (0 : ℚ) < q.den := Nat.cast_pos.mpr q.den_pos
  rw [hid, abs_div, abs_of_pos hd]
  simpa only [one_div] using (div_le_div_iff_of_pos_right hd).mpr hRat

/-- The strict inverse-denominator threshold forces exact equality. -/
theorem eq_int_of_abs_sub_lt_inv_den (q : ℚ) (n : ℤ)
    (h : |q - (n : ℚ)| < (q.den : ℚ)⁻¹) : q = (n : ℚ) := by
  by_contra hne
  exact (not_lt_of_ge (inv_den_le_abs_sub_int q n hne)) h

theorem abs_sub_int_lt_inv_den_iff (q : ℚ) (n : ℤ) :
    |q - (n : ℚ)| < (q.den : ℚ)⁻¹ ↔ q = (n : ℚ) := by
  constructor
  · exact eq_int_of_abs_sub_lt_inv_den q n
  · intro h
    rw [h, sub_self, abs_zero]
    exact inv_pos.mpr (Nat.cast_pos.mpr (Rat.den_pos (n : ℚ)))

theorem inv_den_le_real_abs_sub_int (q : ℚ) (n : ℤ) (hne : q ≠ (n : ℚ)) :
    (q.den : ℝ)⁻¹ ≤ |(q : ℝ) - (n : ℝ)| := by
  have h := inv_den_le_abs_sub_int q n hne
  have hreal := (Rat.cast_le (K := ℝ)).mpr h
  simpa only [Rat.cast_inv, Rat.cast_natCast, Rat.cast_abs, Rat.cast_sub,
    Rat.cast_intCast] using hreal

/-- Any positive upper bound for the denominator gives a sufficient real threshold. -/
theorem eq_int_of_real_abs_sub_lt_inv_of_den_le
    (q : ℚ) (n : ℤ) (D : ℝ) (hD : 0 < D) (hden : (q.den : ℝ) ≤ D)
    (h : |(q : ℝ) - (n : ℝ)| < D⁻¹) : q = (n : ℚ) := by
  by_contra hne
  have hd : (0 : ℝ) < q.den := Nat.cast_pos.mpr q.den_pos
  have hinv : D⁻¹ ≤ (q.den : ℝ)⁻¹ := (inv_le_inv₀ hD hd).mpr hden
  exact (not_lt_of_ge (hinv.trans (inv_den_le_real_abs_sub_int q n hne))) h

/-- The logarithmic rational height used in the two exact-value bridge sources. -/
@[expose] noncomputable def rationalLogHeight (q : ℚ) : ℝ :=
  Real.log (max |(q.num : ℝ)| (q.den : ℝ))

theorem exp_rational_log_height (q : ℚ) :
    Real.exp (rationalLogHeight q) = max |(q.num : ℝ)| (q.den : ℝ) := by
  have hd : (0 : ℝ) < q.den := Nat.cast_pos.mpr q.den_pos
  exact Real.exp_log (hd.trans_le (le_max_right _ _))

theorem den_le_exp_rational_log_height (q : ℚ) :
    (q.den : ℝ) ≤ Real.exp (rationalLogHeight q) := by
  rw [exp_rational_log_height]
  exact le_max_right _ _

/-- A logarithmic height bound turns exponential closeness into exact equality. -/
theorem eq_int_of_real_abs_sub_lt_exp_neg_of_height_le
    (q : ℚ) (n : ℤ) (B : ℝ) (hheight : rationalLogHeight q ≤ B)
    (h : |(q : ℝ) - (n : ℝ)| < Real.exp (-B)) : q = (n : ℚ) := by
  apply eq_int_of_real_abs_sub_lt_inv_of_den_le q n (Real.exp B) (Real.exp_pos B)
  · exact (den_le_exp_rational_log_height q).trans (Real.exp_le_exp.mpr hheight)
  · simpa only [Real.exp_neg] using h

end ZInQ

