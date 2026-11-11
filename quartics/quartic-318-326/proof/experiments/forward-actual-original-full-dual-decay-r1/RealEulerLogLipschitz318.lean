module
public import ActualMovingBoundaryPrimeTail318
public section
noncomputable section
namespace RealEulerLogLipschitz318
set_option maxHeartbeats 16000000

lemma log_difference_upper (x y : ℝ) (hx : 0<x) (hy : 1/2≤y) :
    Real.log x-Real.log y≤2*|x-y| := by
  have hy0 : 0<y := by linarith
  have hl := Real.log_le_sub_one_of_pos (div_pos hx hy0)
  rw [Real.log_div hx.ne' hy0.ne'] at hl
  have he : x/y-1=(x-y)/y := by field_simp [hy0.ne']
  rw [he] at hl
  have ha := div_le_div_of_nonneg_right (le_abs_self (x-y)) hy0.le
  have hi := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/2) hy
  have hb := mul_le_mul_of_nonneg_left hi (abs_nonneg (x-y))
  have hb' : |x-y|/y≤2*|x-y| := by convert hb using 1 <;> ring
  exact hl.trans (ha.trans hb')

/-- Explicit real logarithm control, including both orientations.
The half-interval hypothesis is checked at actual Euler factors below. -/
lemma log_lipschitz (x y : ℝ) (hx : 1/2≤x) (hy : 1/2≤y) :
    |Real.log x-Real.log y|≤2*|x-y| := by
  have hxy := log_difference_upper x y (by linarith) hy
  have hyx := log_difference_upper y x (by linarith) hx
  rw [abs_sub_comm y x] at hyx
  exact abs_le.mpr ⟨by linarith,hxy⟩

lemma one_sub_log_lipschitz (u v : ℝ) (hu : |u|≤1/2) (hv : |v|≤1/2) :
    |Real.log (1-u)-Real.log (1-v)|≤2*|u-v| := by
  have hx : 1/2≤1-u := by linarith [(abs_le.mp hu).2]
  have hy : 1/2≤1-v := by linarith [(abs_le.mp hv).2]
  have hh := log_lipschitz (1-u) (1-v) hx hy
  have he : (1-u)-(1-v)= -(u-v) := by ring
  simpa only [he,abs_neg] using hh

lemma one_sub_log_bound (u : ℝ) (hu : |u|≤1/2) :
    |Real.log (1-u)|≤2*|u| := by
  simpa only [sub_zero,Real.log_one] using
    one_sub_log_lipschitz u 0 hu (by norm_num)

end RealEulerLogLipschitz318
