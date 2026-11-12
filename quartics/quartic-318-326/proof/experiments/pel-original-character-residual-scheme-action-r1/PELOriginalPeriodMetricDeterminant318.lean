module
public import PELOriginalPeriodDerivativeCongruence318
public import PELOriginalNormalizedHermitianMatrix318
public section
noncomputable section
namespace PELOriginalPeriodMetricDeterminant318
open PELQuaternionRealRepresentation318 PELOriginalSiegelMatrix318
open PELOriginalSiegelNormalization318 PELOriginalNormalizedHermitianMatrix318
open PELOriginalPeriodMatrixDerivative318 PELOriginalPeriodDerivativeCongruence318

/-- Determinant of the actual normalized original Hermitian matrix, not
an arbitrary positive form with the same dimension. -/
theorem gram_determinant (τ : ℂ) (hτ : 0<τ.im) :
    (gram τ).det=Complex.normSq τ/(42*τ.im^2) := by
  simp only [gram,Matrix.det_fin_two]
  dsimp
  field_simp [alpha_pos.ne',hτ.ne']
  ring_nf
  simp only [alpha_sq,beta_sq]
  ring

/-- Determinant of the imaginary part of the SAME period matrix, obtained
from the proved full inverse relation to its actual Hermitian form. -/
theorem imaginary_determinant (τ : ℂ) (hτ : 0<τ.im) :
    (imaginary τ).det=42*τ.im^2/Complex.normSq τ := by
  have hn : Complex.normSq τ≠0 := (Complex.normSq_pos.mpr (parameter_ne τ hτ)).ne'
  have h := congrArg Matrix.det (gram_imaginary_inverse τ hτ)
  rw [Matrix.det_mul,Matrix.det_one,gram_determinant τ hτ] at h
  apply (eq_div_iff hn).2
  have he := (div_eq_iff (mul_ne_zero (by norm_num : (42:ℝ)≠0) (pow_ne_zero 2 hτ.ne'))).mp
    (show Complex.normSq τ*(imaginary τ).det/(42*τ.im^2)=1 by
      simpa only [div_mul_eq_mul_div] using h)
  nlinarith [he]

/-- Analytic determinant norm in the original normalized coordinates. -/
theorem derivative_determinant_norm (τ : ℂ) (hτ : 0<τ.im) :
    ‖(derivative τ).det‖=42/Complex.normSq τ := by
  rw [derivative_determinant τ (parameter_ne τ hτ),norm_div,norm_pow]
  norm_num [Complex.normSq_eq_norm_sq]

/-- The determinant of the genuine period derivative divided by the
actual period metric is exactly the hyperbolic density. This is an
analytic calculation; it does not identify arithmetic Hodge/KS lattices. -/
theorem metric_determinant_ratio (τ : ℂ) (hτ : 0<τ.im) :
    ‖(derivative τ).det‖/(imaginary τ).det=1/τ.im^2 := by
  rw [derivative_determinant_norm τ hτ,imaginary_determinant τ hτ]
  have hn : Complex.normSq τ≠0 := (Complex.normSq_pos.mpr (parameter_ne τ hτ)).ne'
  field_simp [hn,hτ.ne']
end PELOriginalPeriodMetricDeterminant318
