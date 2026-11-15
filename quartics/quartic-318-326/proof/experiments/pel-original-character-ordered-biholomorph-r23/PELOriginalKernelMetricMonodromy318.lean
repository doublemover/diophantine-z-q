module
public import PELOriginalPolarizedKernelMetric318
public import PELOriginalSecondFundamentalMetric318
public section
noncomputable section
namespace PELOriginalKernelMetricMonodromy318
open QuaternionicRealPeriod318 PELOriginalFlatPeriodKernel318
open PELOriginalComplexifiedOrder318 PELOriginalUnitFlatTransport318
open PELOriginalFlatPeriodSquare318 PELOriginalFlatSymplecticTransport318
open PELOriginalKernelMonodromyCovariance318 PELOriginalPolarizedKernelMetric318
open PELOriginalPeriodMetricDeterminant318 PELOriginalSecondFundamentalMetric318

lemma split_conjugate (p : Ambient) :
    split (conjugate p)=fun i j => star (split p i j) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [split,conjugate,Complex.star_def] <;> ring
lemma transport_conjugate (u : PELPrincipalOrderCoordinates318.orderˣ) (p : Ambient) :
    transport u (conjugate p)=conjugate (transport u p) := by
  apply splitEquiv.injective
  change split (transport u (conjugate p))=split (conjugate (transport u p))
  rw [split_transport,split_conjugate,split_conjugate,split_transport]
  ext i j
  simp [Matrix.mul_apply,Fin.sum_univ_two,unitMatrixC,Complex.star_def]
  ring

/-- The genuine polarized kernel Hermitian metric is preserved by the
SAME full original integral monodromy, on all vector pairs. -/
theorem metric_transport (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) (v w : ComplexVectors) :
    metric τ (coefficientEquiv u τ hτ v) (coefficientEquiv u τ hτ w)=
      metric (parameter u τ) v w := by
  have hv : kernelLift τ (coefficientEquiv u τ hτ v)=
      transport u.val (kernelLift (parameter u τ) v) :=
    kernel_recover τ _ ((kernel_transport u τ hτ _).mpr (kernelLift_period _ v))
  have hw : kernelLift τ (coefficientEquiv u τ hτ w)=
      transport u.val (kernelLift (parameter u τ) w) :=
    kernel_recover τ _ ((kernel_transport u τ hτ _).mpr (kernelLift_period _ w))
  unfold metric
  rw [hv,hw,←transport_conjugate,symplectic_transport]

@[expose] def metricMatrix (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => metric τ (Pi.single i 1) (Pi.single j 1)
lemma metricMatrix_det (τ : ℂ) :
    (metricMatrix τ).det=((PELOriginalSiegelMatrix318.imaginary τ).det:ℂ) := by
  simp [metricMatrix,metric_basis,Matrix.det_fin_two]
lemma metricMatrix_det_norm (τ : ℂ) (hτ : 0<τ.im) :
    ‖(metricMatrix τ).det‖=(PELOriginalSiegelMatrix318.imaginary τ).det := by
  rw [metricMatrix_det,Complex.norm_real,Real.norm_eq_abs,abs_of_pos]
  rw [imaginary_determinant τ hτ]
  exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos hτ))
    (Complex.normSq_pos.mpr (PELOriginalSiegelNormalization318.parameter_ne τ hτ))

/-- Exact norm identity between the actual connection determinant and the
actual polarized kernel metric determinant. Both sides are independently
constructed from the original periods, pairing, conjugation and derivative. -/
theorem second_fundamental_metric (f : ℂ → ℂ) (z : ℂ)
    (hf : DifferentiableAt ℂ f z) (hu : 0<(f z).im) (hd : deriv f z≠0) :
    PeterssonSectionNorm318.quadraticNorm (MobiusPoincarePullback318.density f z)
      (secondMatrix f z).det=4*‖(metricMatrix (f z)).det‖ := by
  rw [metricMatrix_det_norm _ hu]
  exact secondMatrix_petersson f z hf hu hd
end PELOriginalKernelMetricMonodromy318
