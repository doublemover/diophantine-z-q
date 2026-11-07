module
public import HeightSeparation318
public import RationalSeparationBase
public section
namespace HeightSeparation318

/-- Subtracting an integer preserves the reduced denominator exactly. -/
theorem numerator_sub_integer (q : ℚ) (n : ℤ) :
    (q-n).num=q.num-n*q.den := by
  have hi := Rat.sub_num_den' q (n:ℚ)
  simp only [Rat.den_intCast, Rat.num_intCast, Rat.sub_intCast_den, Nat.cast_one, mul_one] at hi
  exact (mul_left_inj' (by exact_mod_cast q.den_ne_zero : (q.den:ℤ)≠0)).mp hi

theorem rational_height_nonneg (q : ℚ) : 0≤ZInQ.rationalLogHeight q := by
  apply Real.log_nonneg
  exact (by exact_mod_cast q.den_pos : (1:ℝ)≤q.den).trans (le_max_right _ _)

/-- The reduced numerator bound used in the literal order-four comparison. -/
theorem numerator_bound (q : ℚ) (n : ℤ) (B : ℝ)
    (hB : 1≤B) (hn : |(n:ℝ)|≤B) :
    ((q-n).num.natAbs:ℝ)≤2*Real.exp (ZInQ.rationalLogHeight q)*B := by
  rw [numerator_sub_integer]
  have hnabs : ((q.num-n*q.den).natAbs:ℝ)=|(q.num:ℝ)-(n:ℝ)*q.den| := by
    simp only [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  rw [hnabs]
  have hd : (q.den:ℝ)≤Real.exp (ZInQ.rationalLogHeight q) :=
    ZInQ.den_le_exp_rational_log_height q
  have hq : |(q.num:ℝ)|≤Real.exp (ZInQ.rationalLogHeight q) := by
    rw [ZInQ.exp_rational_log_height]
    exact le_max_left _ _
  have hden0 : (0:ℝ)≤q.den := by positivity
  have ht := abs_sub (q.num:ℝ) ((n:ℝ)*q.den)
  rw [abs_mul,abs_of_nonneg hden0] at ht
  have hmul := mul_le_mul hn hd hden0 (by linarith : 0≤B)
  have hsingle := le_mul_of_one_le_right (Real.exp_nonneg (ZInQ.rationalLogHeight q)) hB
  nlinarith

/-- Height comparison with actual rational logarithmic height, including beta=0. -/
theorem odd_input_integral (q : ℚ) (n : ℤ) (B c : ℝ)
    (hn : Odd n) (hB : 3≤B) (hnB : |(n:ℝ)|≤B)
    (hanchor : (2:ℝ)^49151<c) (hc : 8≤c)
    (hscalar : ZInQ.rationalLogHeight (3723*(2*q+1)^2)≤
      heightConstant*c^((49:ℝ)/64))
    (hlucas : c-4<Real.log B)
    (hheight : 3723*(2*q+1)^2≠n → B^2-6<7*heightConstant*
      (((3723*(2*q+1)^2-n).num.natAbs:ℝ)^((49:ℝ)/32))) :
    ∃ z:ℤ,(z:ℚ)=q := by
  apply odd_affine_integral_from_height_data q n B c
    (ZInQ.rationalLogHeight (3723*(2*q+1)^2)) hn hB
    (rational_height_nonneg _) hanchor hc hscalar hlucas
  · exact numerator_bound _ _ B (by linarith only [hB]) hnB
  · exact hheight

end HeightSeparation318
