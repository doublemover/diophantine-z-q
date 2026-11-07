module
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic
public section
noncomputable section
namespace Contact49Growth318
set_option maxHeartbeats 0

/-- The exact new Euler-factor exponent used in the49/8 refinement. -/
theorem euler_factor_32 (p : ℝ) (hp : 13≤p) : (1+1/p)^32≤p := by
  have hp0 : 0<p := by linarith
  have hrec : 1/p≤1/13 := one_div_le_one_div_of_le (by norm_num) hp
  calc
    (1+1/p)^32 ≤ (1+(1:ℝ)/13)^32 := pow_le_pow_left₀ (by positivity) (by linarith) _
    _ ≤ 13 := by norm_num
    _ ≤ p := hp

theorem small_euler_product :
    (1+(1:ℚ)/2)*(1+1/3)*(1+1/5)*(1+1/7)*(1+1/11)=1152/385 := by norm_num

theorem small_euler_product_lt_three :
    (1+(1:ℚ)/2)*(1+1/3)*(1+1/5)*(1+1/7)*(1+1/11)<3 := by norm_num

theorem index_prefactor : (3:ℕ)*4608<2^14 := by norm_num

theorem log_radical_bound (R : ℝ) (hR : 1≤R) : Real.log R<12*R^((1:ℝ)/32) := by
  have hR0 : 0<R := by linarith
  let t := Real.log R/32
  have ht : 0≤t := div_nonneg (Real.log_nonneg hR) (by norm_num)
  have he : Real.exp 1*t≤Real.exp t := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (t-1)) (Real.exp_pos 1).le
    have hid : Real.exp 1*Real.exp (t-1)=Real.exp t := by rw [←Real.exp_add]; congr 1; ring
    rw [hid] at h
    nlinarith
  have ht' : 32*t<12*Real.exp t := by
    by_cases hz : t=0
    · rw [hz,Real.exp_zero]; norm_num
    · have htp : 0<t := lt_of_le_of_ne ht (Ne.symm hz)
      have hconst : (8:ℝ)/3<Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have h := mul_lt_mul_of_pos_right hconst htp
      nlinarith
  rw [Real.rpow_def_of_pos hR0]
  have hmul : Real.log R*((1:ℝ)/32)=t := by dsimp [t]; ring
  rw [hmul]
  dsimp [t] at ht'
  linarith

theorem log_weight_bound (R : ℝ) (hR : 1≤R) :
    4096+6*Real.log R<2^13*R^((1:ℝ)/32) := by
  have he := log_radical_bound R hR
  have hp : 1≤R^((1:ℝ)/32) := Real.one_le_rpow hR (by norm_num)
  norm_num only [pow_succ,pow_zero] at *
  nlinarith

theorem exponent_arithmetic : 2*((97:ℚ)/32)+2*((1:ℚ)/32)=49/8 := by norm_num

/-- The finite exponent calculation consuming the actual quadratic-log height bound. -/
theorem jacobian_growth (R C d L h : ℝ) (hR : 1≤R) (hC : 0<C)
    (hd0 : 0≤d) (hL0 : 0≤L)
    (hd : d<2^14*C*R^((97:ℝ)/32))
    (hL : L<2^13*R^((1:ℝ)/32))
    (hh : h≤2^11*d^2*L^2) : h<2^65*C^2*R^((49:ℝ)/8) := by
  have hRp : 0<R := by linarith
  have hdR : 0<2^14*C*R^((97:ℝ)/32) := by positivity
  have hLR : 0<2^13*R^((1:ℝ)/32) := by positivity
  have hd2 : d^2<(2^14*C*R^((97:ℝ)/32))^2 := by nlinarith
  have hL2 : L^2<(2^13*R^((1:ℝ)/32))^2 := by nlinarith
  have hb : d^2*L^2<(2^14*C*R^((97:ℝ)/32))^2*(2^13*R^((1:ℝ)/32))^2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hd2.le (sq_nonneg L))
      (mul_lt_mul_of_pos_left hL2 (by positivity))
  have hc := mul_lt_mul_of_pos_left hb (by norm_num : (0:ℝ)<2^11)
  have he : 2^11*((2^14*C*R^((97:ℝ)/32))^2*(2^13*R^((1:ℝ)/32))^2)=
      2^65*C^2*R^((49:ℝ)/8) := by
    rw [mul_pow,mul_pow,mul_pow,←Real.rpow_natCast (R^((97:ℝ)/32)) 2,
      ←Real.rpow_natCast (R^((1:ℝ)/32)) 2,←Real.rpow_mul hRp.le,←Real.rpow_mul hRp.le]
    have he : R^(((97:ℝ)/32)*2)*R^(((1:ℝ)/32)*2)=R^((49:ℝ)/8) := by
      rw [←Real.rpow_add hRp]; norm_num
    nlinarith [he]
  rw [he] at hc
  exact hh.trans_lt (by nlinarith)

end Contact49Growth318
#print axioms Contact49Growth318.euler_factor_32
#print axioms Contact49Growth318.log_radical_bound
#print axioms Contact49Growth318.jacobian_growth
