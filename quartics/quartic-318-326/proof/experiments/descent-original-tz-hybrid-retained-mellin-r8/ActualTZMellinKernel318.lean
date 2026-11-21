module
public import Mathlib
public section
noncomputable section
namespace ActualTZMellinKernel318
open MeasureTheory Set
open scoped Topology

@[expose] def mode (ξ : ℝ) : ℂ := 1+(ξ:ℂ)*Complex.I

@[expose] def kernel (ξ η : ℝ) : ℂ := mode ξ*mode η/(mode ξ+mode η)

theorem mode_re (ξ : ℝ) : (mode ξ).re=1 := by
  simp [mode,Complex.mul_re]

theorem mode_norm_le (ξ : ℝ) : ‖mode ξ‖≤1+|ξ| := by
  simpa [mode,Complex.norm_real,Real.norm_eq_abs] using
    norm_add_le (1:ℂ) ((ξ:ℂ)*Complex.I)

theorem sum_re (ξ η : ℝ) : (mode ξ+mode η).re=2 := by
  simp only [Complex.add_re,mode_re] <;> norm_num

theorem sum_ne_zero (ξ η : ℝ) : mode ξ+mode η≠0 := by
  intro h
  have hh := sum_re ξ η
  rw [h,Complex.zero_re] at hh
  norm_num at hh

theorem kernel_norm (ξ η : ℝ) : ‖kernel ξ η‖≤((1+|ξ|)*(1+|η|))/2 := by
  have hd : (2:ℝ)≤‖mode ξ+mode η‖ := by
    simpa only [sum_re] using Complex.re_le_norm (mode ξ+mode η)
  have hN := mul_le_mul (mode_norm_le ξ) (mode_norm_le η) (norm_nonneg _) (by positivity)
  rw [kernel,norm_div,norm_mul]
  calc
    _ ≤ ((1+|ξ|)*(1+|η|))/‖mode ξ+mode η‖ :=
      div_le_div_of_nonneg_right hN (norm_nonneg _)
    _ ≤ _ := by
      exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hd

private theorem sum_neg_re (ξ η : ℝ) : (-(mode ξ+mode η)).re<0 := by
  rw [Complex.neg_re,sum_re]
  norm_num

theorem laplace_integrable (ξ η : ℝ) :
    IntegrableOn (fun u : ℝ => Complex.exp (-(mode ξ+mode η)*(u:ℂ))) (Set.Ioi 0) :=
  integrableOn_exp_mul_complex_Ioi (sum_neg_re ξ η) 0

/-- Exact positive-half-line Laplace identity, with the same negative
Fourier phase in both original divisor slots. -/
theorem laplace_inverse (ξ η : ℝ) :
    (∫ u : ℝ in Set.Ioi 0,Complex.exp (-(mode ξ+mode η)*(u:ℂ))) =
      (mode ξ+mode η)⁻¹ := by
  rw [integral_exp_mul_complex_Ioi (sum_neg_re ξ η) 0]
  simp [one_div]

theorem exponential_pair (ξ η u : ℝ) :
    Complex.exp (-(mode ξ+mode η)*(u:ℂ)) =
      Complex.exp (-mode ξ*(u:ℂ))*Complex.exp (-mode η*(u:ℂ)) := by
  rw [←Complex.exp_add]
  congr 1
  ring

theorem kernel_laplace (ξ η : ℝ) :
    kernel ξ η = mode ξ*mode η*
      (∫ u : ℝ in Set.Ioi 0,
        Complex.exp (-mode ξ*(u:ℂ))*Complex.exp (-mode η*(u:ℂ))) := by
  simp only [←exponential_pair,laplace_inverse,kernel,div_eq_mul_inv]

/-- The exact log-R factor; L is positive in the application.
No branch of complex logarithm is needed for this algebra. -/
theorem kernel_scale (L ξ η : ℝ) (hL : L≠0) :
    (L:ℂ)*(((mode ξ/(L:ℂ))*(mode η/(L:ℂ))) /
      ((mode ξ/(L:ℂ))+(mode η/(L:ℂ))))=kernel ξ η := by
  have hC : (L:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hL
  have hs := sum_ne_zero ξ η
  rw [←add_div]
  unfold kernel
  field_simp [hC,hs] <;> ring

end ActualTZMellinKernel318
