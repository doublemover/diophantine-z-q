module
public import ActualOriginalPolynomialMinorScale318
public section
noncomputable section
namespace ActualOriginalPolynomialKernelBudget318
open ActualOriginalPolynomialMinorScale318 ActualOriginalMinorQuadraticSupremum318
open ActualOriginalUniformLogKernel318 ActualOriginalIntegratedMinorMoment318

@[expose] def kernelPolynomialConstant (c : ℤ) (A : ℝ) : ℝ :=
  32*|((c : ℤ) : ℝ)|*A*(2*A+1)+1824*|((c : ℤ) : ℝ)|*A+4*(2*A+1)+228

lemma actual_kernel_polynomial_nonneg (c : ℤ) (A : ℝ) (hA : 0≤A) :
    0≤kernelPolynomialConstant c A := by unfold kernelPolynomialConstant; positivity

/-- All four expanded terms are bounded independently. The largest
power is n^58, leaving a square-root budget n^29. Log(n^56) is bounded
by 56*n, not treated as a constant. -/
theorem actual_polynomial_kernel (c : ℤ) (H n : ℕ) (A : ℝ)
    (hn : 2≤n) (hA : 0≤A) (hH : (H : ℝ)≤A*(n : ℝ)^32) :
    minorQuadraticBudget c H (minorCutoff n) (n^56)≤kernelPolynomialConstant c A*(n : ℝ)^58 := by
  have hx1 : (1 : ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hx : (0 : ℝ)<n := by linarith
  have hx32 : (1 : ℝ)≤(n : ℝ)^32 := one_le_pow₀ hx1
  have hL : 2*(H : ℝ)+1≤(2*A+1)*(n : ℝ)^32 := by nlinarith
  have hK : |(c : ℝ)|*(H : ℝ)≤|(c : ℝ)|*A*(n : ℝ)^32 := by
    nlinarith [mul_le_mul_of_nonneg_left hH (abs_nonneg (c : ℝ))]
  have hlog : 1+Real.log ((n : ℝ)^56)≤57*(n : ℝ) := by
    rw [Real.log_pow]
    norm_num
    have hh := Real.log_le_sub_one_of_pos hx
    nlinarith
  have hlog0 : 0≤1+Real.log ((n : ℝ)^56) := by
    have hh := Real.log_nonneg (one_le_pow₀ hx1 : (1 : ℝ)≤(n : ℝ)^56)
    linarith
  have h56 := actual_power_degree_mono (n : ℝ) hx1 56 58 (by omega)
  have h33 := actual_power_degree_mono (n : ℝ) hx1 33 58 (by omega)
  have h32 := actual_power_degree_mono (n : ℝ) hx1 32 58 (by omega)
  have h57 := actual_power_degree_mono (n : ℝ) hx1 57 58 (by omega)
  have h1 : 32*(|(c : ℝ)|*(H : ℝ))*(2*(H : ℝ)+1)/(n : ℝ)^8≤
      (32*|(c : ℝ)|*A*(2*A+1))*(n : ℝ)^58 := by
    have hh := mul_le_mul hK hL (by positivity : (0 : ℝ)≤2*(H : ℝ)+1) (by positivity)
    have hd := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ)≤32))
      (pow_nonneg hx.le 8)
    have he : 32*(|(c : ℝ)|*A*(n : ℝ)^32)*((2*A+1)*(n : ℝ)^32)/(n : ℝ)^8=
        (32*|(c : ℝ)|*A*(2*A+1))*(n : ℝ)^56 := by field_simp [ne_of_gt hx]; ring
    rw [he] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left h56 (by positivity))
  have h2 : 32*(|(c : ℝ)|*(H : ℝ))*(1+Real.log ((n : ℝ)^56))≤
      (1824*|(c : ℝ)|*A)*(n : ℝ)^58 := by
    have hh := mul_le_mul hK hlog hlog0 (by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ)≤32)
    have he : 32*((|(c : ℝ)|*A*(n : ℝ)^32)*(57*(n : ℝ)))=
        (1824*|(c : ℝ)|*A)*(n : ℝ)^33 := by ring
    have hb : 32*(|(c : ℝ)|*(H : ℝ))*(1+Real.log ((n : ℝ)^56))≤
        (1824*|(c : ℝ)|*A)*(n : ℝ)^33 := by nlinarith only [hh',he]
    exact hb.trans (mul_le_mul_of_nonneg_left h33 (by positivity))
  have h3 : 4*(2*(H : ℝ)+1)≤(4*(2*A+1))*(n : ℝ)^58 := by
    have hh := mul_le_mul_of_nonneg_left hL (by norm_num : (0 : ℝ)≤4)
    have hh' := mul_le_mul_of_nonneg_left h32 (show 0≤4*(2*A+1) by positivity)
    nlinarith only [hh,hh']
  have h4 : 4*(n : ℝ)^56*(1+Real.log ((n : ℝ)^56))≤228*(n : ℝ)^58 := by
    have hh := mul_le_mul_of_nonneg_left hlog (show 0≤4*(n : ℝ)^56 by positivity)
    have he : 4*(n : ℝ)^56*(57*(n : ℝ))=228*(n : ℝ)^57 := by ring
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left h57 (by norm_num))
  simp only [minorQuadraticBudget,uniformLogBudget,minorCutoff,Int.cast_mul,Int.cast_abs,
    Int.cast_natCast,Nat.cast_pow,kernelPolynomialConstant]
  nlinarith only [h1,h2,h3,h4]

lemma actual_polynomial_kernel_sqrt (c : ℤ) (H n : ℕ) (A : ℝ)
    (hn : 2≤n) (hA : 0≤A) (hH : (H : ℝ)≤A*(n : ℝ)^32) :
    Real.sqrt (minorQuadraticBudget c H (minorCutoff n) (n^56))≤
      Real.sqrt (kernelPolynomialConstant c A)*(n : ℝ)^29 := by
  have hh := Real.sqrt_le_sqrt (actual_polynomial_kernel c H n A hn hA hH)
  have hD := actual_kernel_polynomial_nonneg c A hA
  rw [Real.sqrt_mul hD,show (n : ℝ)^58=((n : ℝ)^29)^2 by ring,
    Real.sqrt_sq (by positivity)] at hh
  exact hh

end ActualOriginalPolynomialKernelBudget318
