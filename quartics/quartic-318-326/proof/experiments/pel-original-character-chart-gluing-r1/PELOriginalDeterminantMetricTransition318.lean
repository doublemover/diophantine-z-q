module
public import PELOriginalDeterminantCoordinate318
public import PELOriginalKernelMetricMonodromy318
public section
noncomputable section
namespace PELOriginalDeterminantMetricTransition318
open QuaternionicRealPeriod318 PELOriginalSiegelMatrix318
open PELOriginalFlatPeriodSquare318 PELOriginalKernelMonodromyCovariance318
open PELOriginalDeterminantCoordinate318 PELOriginalPolarizedKernelMetric318
open PELOriginalKernelMetricMonodromy318 PELOriginalPeriodMetricDeterminant318

@[expose] def starTranspose (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => star (M j i)
lemma starTranspose_det (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (starTranspose M).det=star M.det := by
  simp [starTranspose,Matrix.det_fin_two]
  ring

/-- Whole actual Hermitian Gram matrix transport in the true kernel
frames, not an equality inserted only at the determinant level. -/
lemma metricMatrix_transport (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) :
    metricMatrix (parameter u τ)=transitionMatrix u τ hτ*metricMatrix τ*
      starTranspose (transitionMatrix u τ hτ) := by
  ext i j
  change metric (parameter u τ) (Pi.single i 1) (Pi.single j 1)=_
  rw [←metric_transport u τ hτ,metric_formula]
  simp [Matrix.mul_apply,Fin.sum_univ_two,metricMatrix,metric_basis,
    transitionMatrix,starTranspose]
  ring

/-- The true determinant metric transforms by the squared absolute value
of the literal exterior-line transition scalar. -/
theorem imaginary_det_transport (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) :
    (imaginary (parameter u τ)).det=‖transitionScalar u τ hτ‖^2*(imaginary τ).det := by
  have h := congrArg Matrix.det (metricMatrix_transport u τ hτ)
  rw [Matrix.det_mul,Matrix.det_mul,starTranspose_det] at h
  have hn := congrArg (fun z : ℂ => ‖z‖) h
  rw [metricMatrix_det_norm _ (parameter_positive u τ hτ)] at hn
  simp only [norm_mul,norm_star,metricMatrix_det_norm τ hτ] at hn
  dsimp [transitionScalar]
  calc
    _ = (‖(transitionMatrix u τ hτ).det‖*(imaginary τ).det)*
      ‖(transitionMatrix u τ hτ).det‖ := hn
    _ = _ := by ring

@[expose] def scale (τ : ℂ) : ℝ := Real.sqrt (imaginary τ).det
lemma scale_positive (τ : ℂ) (hτ : 0<τ.im) : 0<scale τ := by
  apply Real.sqrt_pos.mpr
  rw [imaginary_determinant τ hτ]
  exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos hτ))
    (Complex.normSq_pos.mpr (PELOriginalSiegelNormalization318.parameter_ne τ hτ))
lemma scale_transport (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) :
    scale (parameter u τ)=‖transitionScalar u τ hτ‖*scale τ := by
  unfold scale
  rw [imaginary_det_transport u τ hτ,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
end PELOriginalDeterminantMetricTransition318
