module
public import PELOriginalNormedKernelDeterminant318
public import PELOriginalSecondFundamentalMetric318
public section
noncomputable section
namespace PELOriginalDeterminantalPeriodPairing318
open QuaternionicRealPeriod318 PELOriginalKernelDeterminantLine318
open PELOriginalDeterminantCoordinate318 PELOriginalNormedKernelDeterminant318
open PELOriginalPeriodKernelConnection318 PELOriginalSecondFundamentalMetric318
open PELOriginalPeriodMatrixDerivative318 PELOriginalPulledPeriodMetric318
open scoped TensorProduct

abbrev Square (τ : ℂ) := Fiber τ ⊗[ℂ] Fiber τ
@[expose] def squareCoordinate (τ : ℂ) : Square τ ≃ₗ[ℂ] ℂ :=
  (TensorProduct.congr (coordinate τ) (coordinate τ)).trans (TensorProduct.lid ℂ ℂ)
lemma squareCoordinate_pure (τ : ℂ) (x y : Fiber τ) :
    squareCoordinate τ (x ⊗ₜ[ℂ] y)=coordinate τ x*coordinate τ y := by
  simp only [squareCoordinate,LinearEquiv.trans_apply,TensorProduct.congr_tmul,
    TensorProduct.lid_tmul,smul_eq_mul]

/-- Independent determinant of the actual normal derivative paired with
actual kernel vectors, in arbitrary full vector families. -/
lemma full_pairing_matrix (f : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℂ f z)
    (hu : 0<(f z).im) (v w : Fin 2 → ComplexVectors) :
    (fun i j => pulledPairing f z (v i) (w j))=
      (fun i j => v i j)*secondMatrix f z*(fun i j => w i j).transpose := by
  rw [secondMatrix_eq f z hf hu,pulled_derivative f z hf hu]
  ext i j
  rw [pulledPairing_formula f z hf hu,
    secondPairing_formula _ (PELOriginalSiegelNormalization318.parameter_ne _ hu)]
  simp [Matrix.mul_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
    Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul]
  ring

lemma secondMatrix_det_ne (f : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℂ f z)
    (hu : 0<(f z).im) (hd : deriv f z≠0) : (secondMatrix f z).det≠0 := by
  rw [secondMatrix_eq f z hf hu,pulled_derivative f z hf hu,det_scalar]
  exact mul_ne_zero (pow_ne_zero 2 hd)
    (PELOriginalPeriodDerivativeCongruence318.derivative_determinant_ne _ hu)

/-- Actual both-inverse determinant comparison from the tensor square of
the genuine original kernel exterior line to quadratic coordinate
coefficients. Its full exterior determinant identity is proved below. -/
@[expose] def comparison (f : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℂ f z)
    (hu : 0<(f z).im) (hd : deriv f z≠0) : Square (f z) ≃ₗ[ℂ] ℂ :=
  (squareCoordinate (f z)).trans (LinearEquiv.smulOfUnit
    (Units.mk0 (secondMatrix f z).det (secondMatrix_det_ne f z hf hu hd)))
lemma comparison_formula (f : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℂ f z)
    (hu : 0<(f z).im) (hd : deriv f z≠0) (x : Square (f z)) :
    comparison f z hf hu hd x=(secondMatrix f z).det*squareCoordinate (f z) x := rfl

/-- On ALL exterior generators the map is literally the determinant of
the actual second-fundamental pairing. Thus it is not obtained by merely
identifying abstract one-dimensional carriers or their numerical norms. -/
theorem comparison_exterior (f : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℂ f z)
    (hu : 0<(f z).im) (hd : deriv f z≠0) (v w : Fin 2 → ComplexVectors) :
    comparison f z hf hu hd
      (frame (f z) (exteriorPower.ιMulti ℂ 2 v) ⊗ₜ[ℂ]
        frame (f z) (exteriorPower.ιMulti ℂ 2 w))=
      (fun i j => pulledPairing f z (v i) (w j)).det := by
  rw [comparison_formula,squareCoordinate_pure,full_pairing_matrix f z hf hu,
    Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose]
  change (secondMatrix f z).det*
    (coefficient (exteriorPower.ιMulti ℂ 2 v)*coefficient (exteriorPower.ιMulti ℂ 2 w))=_
  simp only [coefficient,exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change (secondMatrix f z).det*((fun i j => v i j).det*(fun i j => w i j).det)=_
  ring
end PELOriginalDeterminantalPeriodPairing318
