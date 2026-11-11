module
public import PELOriginalDeterminantalPeriodNorm318
public section
noncomputable section
namespace PELOriginalDeterminantalMonodromy318
open QuaternionicRealPeriod318 PELOriginalKernelDeterminantLine318
open PELOriginalDeterminantCoordinate318 PELOriginalNormedKernelDeterminant318
open PELOriginalDeterminantalPeriodPairing318 PELOriginalDeterminantalPeriodNorm318
open PELOriginalPeriodMatrixDerivative318 PELOriginalPeriodKernelConnection318
open PELOriginalKernelMonodromyCovariance318 PELOriginalFlatPeriodSquare318
open PELOriginalDeterminantMetricTransition318 PELOriginalSecondFundamentalMetric318
open scoped TensorProduct

lemma connection_matrix_covariance (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) :
    transitionMatrix u τ hτ*derivative τ*(transitionMatrix u τ hτ).transpose=
      deriv (parameter u) τ • derivative (parameter u τ) := by
  ext i j
  have h := secondPairing_covariance u τ hτ (Pi.single i 1) (Pi.single j 1)
  rw [secondPairing_formula _ (PELOriginalSiegelNormalization318.parameter_ne τ hτ),
    secondPairing_formula _ (PELOriginalSiegelNormalization318.parameter_ne _
      (parameter_positive u τ hτ))] at h
  fin_cases i <;> fin_cases j <;>
    simp [dotProduct,Matrix.mulVec,Fin.sum_univ_two,transitionMatrix,
      Matrix.mul_apply,Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul] at h ⊢ <;>
    linear_combination h
lemma connection_determinant_covariance (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) :
    (derivative τ).det*(transitionScalar u τ hτ)^2=
      (deriv (parameter u) τ)^2*(derivative (parameter u τ)).det := by
  have h := congrArg Matrix.det (connection_matrix_covariance u τ hτ)
  rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,PELOriginalPulledPeriodMetric318.det_scalar] at h
  dsimp [transitionScalar]
  linear_combination h

@[expose] def squareTransport (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) : Square (parameter u τ) ≃ₗ[ℂ] Square τ :=
  TensorProduct.congr (PELOriginalKernelDeterminantLine318.transport u τ hτ)
    (PELOriginalKernelDeterminantLine318.transport u τ hτ)
lemma squareCoordinate_transport (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) (x : Square (parameter u τ)) :
    squareCoordinate τ (squareTransport u τ hτ x)=
      (transitionScalar u τ hτ)^2*squareCoordinate (parameter u τ) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v w =>
      simp only [squareTransport,TensorProduct.congr_tmul,squareCoordinate_pure,coordinate_transport]
      ring
  | add x y hx hy => simp only [map_add,hx,hy,mul_add]

@[expose] def baseComparison (τ : ℂ) (hτ : 0<τ.im) : Square τ ≃ₗ[ℂ] ℂ :=
  comparison id τ differentiableAt_id hτ (by simp)
lemma baseComparison_formula (τ : ℂ) (hτ : 0<τ.im) (x : Square τ) :
    baseComparison τ hτ x=(derivative τ).det*squareCoordinate τ x := by
  change comparison id τ differentiableAt_id hτ _ x=_
  rw [comparison_formula,secondMatrix_eq id τ differentiableAt_id hτ,
    PELOriginalPulledPeriodMetric318.pulled_derivative id τ differentiableAt_id hτ]
  simp

/-- Actual determinant comparison obeys the genuine quadratic cotangent
transition law on EVERY tensor, retaining the literal base derivative. -/
theorem comparison_covariance (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) (x : Square (parameter u τ)) :
    baseComparison τ hτ (squareTransport u τ hτ x)=
      (deriv (parameter u) τ)^2*
        baseComparison (parameter u τ) (parameter_positive u τ hτ) x := by
  rw [baseComparison_formula,baseComparison_formula,squareCoordinate_transport]
  rw [←mul_assoc,connection_determinant_covariance u τ hτ]
  ring

/-- The actual whole tensor-square transport is isometric for the
independently produced determinant metrics. -/
theorem squareNorm_transport (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) (x : Square (parameter u τ)) :
    squareNorm τ hτ (squareTransport u τ hτ x)=
      squareNorm (parameter u τ) (parameter_positive u τ hτ) x := by
  rw [squareNorm_formula,squareNorm_formula,squareCoordinate_transport,norm_mul,norm_pow,
    imaginary_det_transport u τ hτ]
  ring
end PELOriginalDeterminantalMonodromy318
