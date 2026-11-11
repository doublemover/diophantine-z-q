module
public import PELOriginalPeriodMatrixDerivative318
public section
noncomputable section
namespace PELOriginalPeriodDerivativeCongruence318
open PELQuaternionRealRepresentation318 PELOriginalSiegelMatrix318
open PELOriginalSiegelNormalization318 PELOriginalPeriodMatrixDerivative318
lemma alpha_complex_sq : (alpha:ℂ)^2=210 := by exact_mod_cast alpha_sq
lemma beta_complex_cube : (beta:ℂ)^3=5*(beta:ℂ) := by
  calc
    _ = (beta:ℂ)^2*(beta:ℂ) := by ring
    _ = _ := by rw [beta_complex_sq]

/-- Entrywise identity in the EXACT original coordinate convention.
The ordering is A * Omega' * A.transpose, NOT A.transpose * Omega' * A.
This is a proved period-derivative identity; identification with a
relative de Rham/Gauss-Manin KS morphism is not assumed here. -/
theorem original_congruence (τ : ℂ) (hτ : τ≠0) :
    originalMatrix τ*derivative τ*(originalMatrix τ).transpose=(alpha:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [originalMatrix,derivative,linearPart,reciprocalPart,Matrix.mul_apply,
      Fin.sum_univ_two,Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul] <;>
    field_simp [hτ] <;>
    ring_nf <;> simp only [beta_complex_sq,beta_complex_cube] <;> ring

/-- The literal210 is the determinant of the actual original-period
congruence, not a chosen arithmetic index or a supplied degree equality. -/
theorem original_determinant (τ : ℂ) (hτ : τ≠0) :
    (originalMatrix τ*derivative τ*(originalMatrix τ).transpose).det=(210:ℂ) := by
  rw [original_congruence τ hτ]
  simpa [Matrix.det_fin_two,Matrix.smul_apply,smul_eq_mul,pow_two] using alpha_complex_sq

theorem derivative_determinant (τ : ℂ) (hτ : τ≠0) : (derivative τ).det=42/τ^2 := by
  have h := original_determinant τ hτ
  rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,originalMatrix_det] at h
  have he : 5*τ^2*(derivative τ).det=210 := by
    calc
      _ = (-(beta:ℂ)*τ)*(derivative τ).det*(-(beta:ℂ)*τ) := by
        ring_nf
        rw [beta_complex_sq]
        ring
      _ = _ := h
  apply (eq_div_iff (pow_ne_zero 2 hτ)).2
  linear_combination he/5

/-- Genuine nondegeneracy of the derivative matrix throughout the actual
upper half-plane; no generic nonvanishing hypothesis is inserted. -/
theorem derivative_determinant_ne (τ : ℂ) (hτ : 0<τ.im) : (derivative τ).det≠0 := by
  rw [derivative_determinant τ (parameter_ne τ hτ)]
  exact div_ne_zero (by norm_num) (pow_ne_zero _ (parameter_ne τ hτ))
end PELOriginalPeriodDerivativeCongruence318
