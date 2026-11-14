module
public import PELOriginalMovingKernelConnection318
public import PELOriginalChartPeriodMetric318
public section
noncomputable section
namespace PELOriginalSecondFundamentalMetric318
open QuaternionicRealPeriod318 PELQuaternionRealRepresentation318
open PELOriginalSiegelMatrix318 PELOriginalSiegelNormalization318
open PELOriginalPeriodMatrixDerivative318 PELOriginalPeriodKernelConnection318
open PELOriginalFlatPeriodKernel318 PELOriginalPulledPeriodMetric318
open MobiusPoincarePullback318 PeterssonSectionNorm318

/-- Actual scalar extension of the original symplectic form paired with
the derivative of the actual period-kernel frame along a holomorphic base map. -/
@[expose] def pulledPairing (f : ℂ → ℂ) (z : ℂ) (v w : ComplexVectors) : ℂ :=
  symplectic (kernelLift (f z) v) (deriv (fun x => kernelLift (f x) w) z)
lemma pulledPairing_formula (f : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℂ f z)
    (hu : 0<(f z).im) (v w : ComplexVectors) :
    pulledPairing f z v w=deriv f z*secondPairing (f z) v w := by
  have hd := (hasDerivAt_kernelLift (f z) (parameter_ne (f z) hu) w).scomp z hf.hasDerivAt
  unfold pulledPairing
  rw [hd.deriv,secondPairing_formula _ (parameter_ne (f z) hu)]
  simp [symplectic,kernelLift,dotProduct,Fin.sum_univ_two,smul_eq_mul]
  ring

/-- Matrix of the genuine whole second-fundamental tensor in its actual
kernel frame, NOT a redefinition by the previously calculated Omega'. -/
@[expose] def secondMatrix (f : ℂ → ℂ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => pulledPairing f z (Pi.single i 1) (Pi.single j 1)
lemma secondMatrix_eq (f : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℂ f z)
    (hu : 0<(f z).im) : secondMatrix f z=deriv (fun x => omega (f x)) z := by
  rw [pulled_derivative f z hf hu]
  ext i j
  rw [secondMatrix,pulledPairing_formula f z hf hu,
    secondPairing_formula _ (parameter_ne (f z) hu)]
  simp [dotProduct,Matrix.mulVec,Matrix.smul_apply,smul_eq_mul]

/-- The actual period-kernel connection tensor has the SAME produced
Poincare density as the original base chart, with no arbitrary tensor matching. -/
theorem secondMatrix_density (f : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℂ f z)
    (hu : 0<(f z).im) :
    ‖(secondMatrix f z).det‖=density f z*(imaginary (f z)).det := by
  rw [secondMatrix_eq f z hf hu]
  exact determinant_density f z hf hu

theorem secondMatrix_petersson (f : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℂ f z)
    (hu : 0<(f z).im) (hd : deriv f z≠0) :
    quadraticNorm (density f z) (secondMatrix f z).det=4*(imaginary (f z)).det := by
  rw [secondMatrix_eq f z hf hu]
  exact determinant_petersson f z hf hu hd

/-- Original-coordinate normalization of the actual connection tensor,
including the derivative of the true base uniformizer. -/
theorem original_pulledPairing (f : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℂ f z)
    (hu : 0<(f z).im) (v w : ComplexVectors) :
    pulledPairing f z ((originalMatrix (f z)).transpose.mulVec v)
      ((originalMatrix (f z)).transpose.mulVec w)=
      deriv f z*(alpha:ℂ)*(v 0*w 0+v 1*w 1) := by
  rw [pulledPairing_formula f z hf hu,
    original_secondPairing _ (parameter_ne (f z) hu)]
  ring
end PELOriginalSecondFundamentalMetric318
