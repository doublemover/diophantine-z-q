module
public import CuspCauchy318
public section
noncomputable section
namespace CuspLocation318
set_option maxHeartbeats 0

theorem large_j_threshold : (128:ℝ)*Real.exp (20*Real.pi)<1728*2^128 := by
  have hlog : 20*Real.pi<128*Real.log 2 := by
    nlinarith [Real.pi_lt_d2,Real.log_two_gt_d9]
  have he := Real.exp_lt_exp.mpr hlog
  have hid : Real.exp (128*Real.log (2:ℝ))=(2:ℝ)^128 := by
    rw [show (128:ℝ)=(128:ℕ) by norm_num,Real.exp_nat_mul,Real.exp_log (by norm_num)]
  rw [hid] at he
  have hh := mul_lt_mul_of_pos_left he (by norm_num : (0:ℝ)<128)
  nlinarith

/-- Large rational j-value forces every reduced representative into a deep cusp. -/
theorem imaginary_part_gt_ten (y J M:ℝ)
    (hG:J≤128/Real.exp (-2*Real.pi*y))
    (hJ:1728*M≤J) (hM:(2:ℝ)^128≤M) : 10<y := by
  by_contra hy
  have hy' : y≤10 := le_of_not_gt hy
  have he : Real.exp (2*Real.pi*y)≤Real.exp (20*Real.pi) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hid : (128:ℝ)/Real.exp (-2*Real.pi*y)=128*Real.exp (2*Real.pi*y) := by
    rw [show -2*Real.pi*y= -(2*Real.pi*y) by ring,Real.exp_neg,div_inv_eq_mul]
  rw [hid] at hG
  have ht := large_j_threshold
  nlinarith

/-- The fundamental-domain height gives a radius inside the uniform analytic disc. -/
theorem fundamental_q_small (y:ℝ) (hy:Real.sqrt 3/2≤y) :
    Real.exp (-2*Real.pi*y)<(1:ℝ)/100 := by
  have hs : (5:ℝ)/3<Real.sqrt 3 := by
    apply (Real.lt_sqrt (by norm_num)).mpr
    norm_num
  have hyp : (5:ℝ)/6<y := by linarith
  have h5 : (5:ℝ)<2*Real.pi*y := by nlinarith [Real.pi_gt_three]
  have he5 : (100:ℝ)<Real.exp 5 := by
    have hh : ((8:ℝ)/3)^5<(Real.exp 1)^5 :=
      pow_lt_pow_left₀ (by linarith [Real.exp_one_gt_d9]) (by norm_num) (by norm_num)
    rw [←Real.exp_nat_mul] at hh
    norm_num at hh
    linarith
  have he : (100:ℝ)<Real.exp (2*Real.pi*y) :=
    he5.trans (Real.exp_lt_exp.mpr h5)
  rw [show -2*Real.pi*y= -(2*Real.pi*y) by ring, Real.exp_neg,inv_eq_one_div]
  exact one_div_lt_one_div_of_lt (by norm_num) he

end CuspLocation318
#print axioms CuspLocation318.large_j_threshold
#print axioms CuspLocation318.imaginary_part_gt_ten
#print axioms CuspLocation318.fundamental_q_small
