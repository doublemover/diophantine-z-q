module
public import PELOriginalCM210NativeIntegerOrder318
public import Mathlib.RingTheory.Discriminant
public import Mathlib.LinearAlgebra.Matrix.ToLin
public section
noncomputable section
namespace PELOriginalCM210IntegralTraceMatrix318
open PELOriginalCM210IntegralConjugation318
@[expose] def integralBasis : Module.Basis (Fin 2) ℤ R := QuadraticAlgebra.basis (-210) 0
lemma basis_zero : integralBasis 0=(1:R) := by
  ext <;> simp [integralBasis,QuadraticAlgebra.basis]
lemma basis_one : integralBasis 1=thetaR := by
  ext <;> simp [integralBasis,QuadraticAlgebra.basis,thetaR,QuadraticAlgebra.omega]
lemma left_matrix (z:R) : Algebra.leftMulMatrix integralBasis z=
    ![![z.re,-210*z.im],![z.im,z.re]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Algebra.leftMulMatrix_eq_repr_mul,integralBasis,QuadraticAlgebra.basis,
      QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul] <;> ring
lemma native_trace (z:R) : Algebra.trace ℤ R z=2*z.re := by
  rw [Algebra.trace_eq_matrix_trace integralBasis,left_matrix]
  simp [Matrix.trace,Fin.sum_univ_two] <;> ring
lemma trace_matrix : Algebra.traceMatrix ℤ integralBasis=(![![2,0],![0,-420]]:Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Algebra.traceMatrix_apply,Algebra.traceForm_apply,native_trace,
      integralBasis,QuadraticAlgebra.basis,QuadraticAlgebra.re_mul]
lemma basis_discriminant : Algebra.discr ℤ integralBasis=(-840:ℤ) := by
  rw [Algebra.discr_def,trace_matrix]
  norm_num [Matrix.det_fin_two]

end PELOriginalCM210IntegralTraceMatrix318
