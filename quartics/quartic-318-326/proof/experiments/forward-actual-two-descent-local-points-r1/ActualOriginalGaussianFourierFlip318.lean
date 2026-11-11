module
public import ActualOriginalAmbientFourierIdentity318
public section
noncomputable section
namespace ActualOriginalGaussianFourierFlip318
open MeasureTheory Complex Module Real
open scoped FourierTransform RealInnerProductSpace
set_option maxHeartbeats 16000000

/-- An ordinary absolutely integrable Gaussian is paired with an actual
integrable profile before Fourier duality is used. No integrability of the
UNDAMPED transform and no exchange of improper integrals is assumed. -/
theorem actual_gaussian_fourier_flip (f : ℝ→ℂ) (hf : Integrable f) (c : ℝ) (hc : 0<c) :
    (∫t : ℝ,Complex.exp (-(c:ℂ)⁻¹*‖t‖^2) • 𝓕 f t)=
      ∫s : ℝ,((Real.pi*c:ℂ)^(Module.finrank ℝ ℝ/2:ℂ)*
        Complex.exp (-Real.pi^2*c*‖(0:ℝ)-s‖^2)) • f s := by
  have hb : 0<((c:ℂ)⁻¹).re := by simp only [←Complex.ofReal_inv,Complex.ofReal_re];positivity
  have hG : Integrable (fun t : ℝ => Complex.exp (-(c:ℂ)⁻¹*‖t‖^2)) := by
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb (0:ℂ) (0:ℝ)
  have hflip :
      (∫t : ℝ,Complex.exp (-(c:ℂ)⁻¹*‖t‖^2) • 𝓕 f t)=
        ∫s : ℝ,𝓕 (fun t : ℝ => Complex.exp (-(c:ℂ)⁻¹*‖t‖^2)) s • f s := by
    simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L:=innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner hG hf).symm
  rw [hflip]
  apply integral_congr_ae
  filter_upwards with s
  rw [fourier_gaussian_innerProductSpace hb]
  have he : -(Real.pi:ℂ)^2*‖s‖^2*(c:ℂ)=
      -(Real.pi:ℂ)^2*c*‖(0:ℝ)-s‖^2 := by
    simp only [zero_sub,norm_neg]
    ring
  simp only [div_inv_eq_mul,he]

end ActualOriginalGaussianFourierFlip318
