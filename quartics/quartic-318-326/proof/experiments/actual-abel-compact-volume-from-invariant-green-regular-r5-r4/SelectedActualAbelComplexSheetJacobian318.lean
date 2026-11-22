module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Tactic.Ring

public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace SelectedActualAbelComplexSheetJacobian318

/-- Exact real norm of multiplication on ℂ, in the pinned (1,I) basis. -/
theorem complex_real_fieldNorm (z : ℂ) : Algebra.norm ℝ z = Complex.normSq z := by
  rw [Algebra.norm_eq_matrix_det Complex.basisOneI, Matrix.det_fin_two]
  simp [Algebra.leftMulMatrix_eq_repr_mul, Complex.coe_basisOneI,
    Complex.coe_basisOneI_repr, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

/-- The real Jacobian factor of an actual complex-linear derivative
is the square of its complex determinant norm, with no scale choice. -/
theorem abs_real_det_eq_complex_det_sq (D : E →L[ℂ] E) :
    |(D.restrictScalars ℝ).toLinearMap.det| =
      ‖D.toLinearMap.det‖ ^ 2 := by
  change |(D.toLinearMap.restrictScalars ℝ).det| = ‖D.toLinearMap.det‖ ^ 2
  rw [LinearMap.det_restrictScalars, complex_real_fieldNorm, Complex.normSq_eq_norm_sq,
    abs_of_nonneg (sq_nonneg _)]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Native local sheet change of variables with exactly the holomorphic
determinant weight. For the Abel atlas, specialize to the given inverse
branch expressed in the actual fixed holomorphic coordinate frames.
This constructs the local sheet pushforward; it does not assume it. -/
theorem complex_density_sheet_pushforward
    (μ : Measure E) [IsAddHaarMeasure μ] (f : E → E)
    (D : E → E →L[ℂ] E) (S U : Set E)
    (hS : MeasurableSet S)
    (hderiv : ∀ x ∈ S, HasFDerivWithinAt f (D x) S x)
    (hinj : InjOn f S) (himage : f '' S = U) :
    Measure.map f ((μ.withDensity fun x =>
      ENNReal.ofReal (‖(D x).toLinearMap.det‖ ^ 2)).restrict S) = μ.restrict U := by
  have hreal : ∀ x ∈ S, HasFDerivWithinAt f ((D x).restrictScalars ℝ) S x :=
    fun x hx => (hderiv x hx).restrictScalars ℝ
  have he := MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar μ
    hS.nullMeasurableSet hreal hinj
  rw [restrict_withDensity hS]
  simpa only [abs_real_det_eq_complex_det_sq, himage] using he

end SelectedActualAbelComplexSheetJacobian318

#print axioms SelectedActualAbelComplexSheetJacobian318.complex_real_fieldNorm
#print axioms SelectedActualAbelComplexSheetJacobian318.abs_real_det_eq_complex_det_sq
#print axioms SelectedActualAbelComplexSheetJacobian318.complex_density_sheet_pushforward
