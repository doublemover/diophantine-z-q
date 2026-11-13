module
public import PELOriginalCM210NativeDiscriminant318
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public section
noncomputable section
namespace PELOriginalCM210NativeElementNorm318
open PELOriginalCM210IntegralConjugation318 PELOriginalCM210NativeIntegerOrder318
open PELOriginalCM210IntegralTraceMatrix318 PELOriginalCM210NativeDiscriminant318
lemma element_norm (z:R) : Algebra.norm ℤ (integerEquiv z)=z.re^2+210*z.im^2 := by
  change Algebra.norm ℤ (integerAlgEquiv z)=_
  rw [Algebra.norm_eq_of_algEquiv,Algebra.norm_eq_matrix_det integralBasis,left_matrix]
  simp [Matrix.det_fin_two] <;> ring
lemma norm_nonneg (z:R) : 0≤z.re^2+210*z.im^2 := by nlinarith [sq_nonneg z.re,sq_nonneg z.im]
lemma principal_norm (z:R) :
    Ideal.absNorm (Ideal.span ({integerEquiv z}:Set O))=(z.re^2+210*z.im^2).natAbs := by
  rw [Ideal.absNorm_span_singleton,element_norm]
lemma norm_coordinates (z:O) : Algebra.norm ℤ z=
    (integerEquiv.symm z).re^2+210*(integerEquiv.symm z).im^2 := by
  simpa only [RingEquiv.apply_symm_apply] using element_norm (integerEquiv.symm z)
end PELOriginalCM210NativeElementNorm318
