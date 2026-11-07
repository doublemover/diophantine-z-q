module
public import CuspRadius318
public section
noncomputable section
namespace CuspDerivative318
set_option maxHeartbeats 0

/-- The coefficient majorant used for E4 is safely below four. -/
theorem eisenstein_majorant :
    (1:ℚ)+240*((1/100)*(1+11*(1/100)+11*(1/100)^2+(1/100)^3)/(1-1/100)^5)<4 := by
  norm_num

/-- The product-factor logarithm is strictly below log 2. -/
theorem product_log_majorant : (24:ℝ)*(1/100)/(1-1/100)^2<Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num at *
  linarith

theorem tiny_q : Real.exp (-20*Real.pi)<(1:ℝ)/102400 := by
  have hpi := Real.pi_gt_three
  have h60 : Real.exp (60:ℝ) ≥ 2^60 := by
    have h : (2:ℝ)^60≤(Real.exp 1)^60 := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le _
    simpa only [←Real.exp_nat_mul, Nat.cast_ofNat, mul_one] using h
  have hlarge : (102400:ℝ)<Real.exp (20*Real.pi) := by
    have he : Real.exp (60:ℝ)<Real.exp (20*Real.pi) := Real.exp_lt_exp.mpr (by linarith)
    norm_num at h60
    linarith
  rw [show -20*Real.pi= -(20*Real.pi) by ring, Real.exp_neg, inv_eq_one_div]
  exact one_div_lt_one_div_of_lt (by norm_num) hlarge

/-- Exact algebra of the derivative of 1728 q/G(q), with the analytic
Cauchy bounds recorded explicitly rather than an assumed derivative bound. -/
theorem derivative_formula_lower (q G G':ℂ)
    (hG:‖G-1‖≤(1:ℝ)/4) (hq:‖q*G'‖≤(1:ℝ)/4) :
    (128:ℝ)≤‖1728*(G-q*G')/G^2‖ := by
  have hGupper : ‖G‖≤(5:ℝ)/4 := by
    have ht := norm_add_le (G-1) (1:ℂ)
    simp only [sub_add_cancel, norm_one] at ht
    linarith
  have hGlower : (3:ℝ)/4≤‖G‖ := by
    have ht := norm_sub_norm_le (1:ℂ) G
    rw [norm_one, norm_sub_rev] at ht
    linarith
  have hG0 : G≠0 := by
    intro hz; rw [hz,norm_zero] at hGlower; norm_num at hGlower
  have hdiff : (1:ℝ)/2≤‖G-q*G'‖ := by
    have ht := norm_sub_norm_le G (q*G')
    linarith
  rw [norm_div,norm_mul,norm_pow]
  norm_num only [Complex.norm_ofNat]
  apply (le_div_iff₀ (pow_pos (lt_of_lt_of_le (by norm_num : (0:ℝ)<3/4) hGlower) _)).mpr
  nlinarith [sq_nonneg ‖G‖]

/-- The reciprocal q bound follows from the same constant term estimate. -/
theorem inverse_q_bound (q j G:ℂ) (hq:q≠0) (hG:G=q*j)
    (hnear:‖G-1‖≤(1:ℝ)/4) : ‖q‖⁻¹≤2*‖j‖ := by
  have ht := norm_sub_norm_le (1:ℂ) G
  rw [norm_one,norm_sub_rev] at ht
  have hl : (3:ℝ)/4≤‖G‖ := by linarith
  rw [hG,norm_mul] at hl
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr hq)).mpr
  nlinarith

/-- The width factor in q=q_c^m is retained, not silently discarded. -/
theorem chain_factor_lower (r D:ℝ) (m:ℕ) (hm:1≤m)
    (hr:0<r) (hr1:r≤1) (hD:128≤D) :
    r^m≤D*(m:ℝ)*r^(m-1) := by
  have hmR : (1:ℝ)≤m := by exact_mod_cast hm
  have he : r^m=r^(m-1)*r := by
    rw [←pow_succ]; congr 1; omega
  rw [he]
  have hfac : r≤D*(m:ℝ) := by nlinarith
  nlinarith [pow_pos hr (m-1)]

/-- The actual logarithmic differential target once the q and j identities
have been supplied by the modular coordinate. -/
theorem log_differential_bound (D q M:ℝ) (hD:0<D) (hq:0<q) (hM:0<M)
    (hsmall:q≤D) (hinv:q⁻¹≤2*(1728*M)) :
    -Real.log D≤Real.log M+9 := by
  have hl := Real.log_le_log hq hsmall
  have hi := Real.log_le_log (inv_pos.mpr hq) hinv
  rw [Real.log_inv] at hi
  have hlog : Real.log (2*(1728*M))=Real.log (3456:ℝ)+Real.log M := by
    rw [show 2*(1728*M)=(3456:ℝ)*M by ring, Real.log_mul (by norm_num) hM.ne']
  rw [hlog] at hi
  have h3456 : Real.log (3456:ℝ)<9 := by
    have he : (3456:ℝ)<Real.exp 9 := by
      have hp : ((8:ℝ)/3)^9<(Real.exp 1)^9 := pow_lt_pow_left₀ (by linarith [Real.exp_one_gt_d9]) (by norm_num) (by norm_num)
      rw [←Real.exp_nat_mul] at hp
      norm_num at hp
      linarith
    exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr he
  linarith

end CuspDerivative318
#print axioms CuspDerivative318.derivative_formula_lower
#print axioms CuspDerivative318.chain_factor_lower
#print axioms CuspDerivative318.log_differential_bound
