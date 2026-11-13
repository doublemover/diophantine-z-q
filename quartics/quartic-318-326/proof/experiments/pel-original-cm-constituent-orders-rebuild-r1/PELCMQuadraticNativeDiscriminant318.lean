module
public import PELCMQuadraticNativeIntegerOrder318
public import Mathlib.RingTheory.Discriminant
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public section
noncomputable section
namespace PELCMQuadraticNativeDiscriminant318
open PELCMQuadraticIntegralTraceData318 PELCMQuadraticNativeIntegerOrder318
@[expose] def basis (a b:ℤ) : Module.Basis (Fin 2) ℤ (R a b) := QuadraticAlgebra.basis a b
lemma left_matrix (a b:ℤ) (z:R a b) : Algebra.leftMulMatrix (basis a b) z=
    ![![z.re,a*z.im],![z.im,z.re+b*z.im]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Algebra.leftMulMatrix_eq_repr_mul,basis,QuadraticAlgebra.basis,
      QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul] <;> ring
lemma trace (a b:ℤ) (z:R a b) : Algebra.trace ℤ (R a b) z=2*z.re+b*z.im := by
  rw [Algebra.trace_eq_matrix_trace (basis a b),left_matrix]
  simp [Matrix.trace,Fin.sum_univ_two] <;> ring
lemma trace_matrix (a b:ℤ) :
    Algebra.traceMatrix ℤ (basis a b)=(![![2,b],![b,2*a+b^2]]:Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Algebra.traceMatrix_apply,Algebra.traceForm_apply,trace,basis,
      QuadraticAlgebra.basis,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul] <;> ring
lemma basis_discriminant (a b:ℤ) : Algebra.discr ℤ (basis a b)=D a b := by
  rw [Algebra.discr_def,trace_matrix]
  simp [Matrix.det_fin_two,D] <;> ring
variable (a b:ℤ) [Fact (∀x:ℚ,x^2≠(a:ℚ)+(b:ℚ)*x)]
@[expose] def nativeBasis (hcoords:Coordinates a b) : Module.Basis (Fin 2) ℤ (O a b) :=
  (basis a b).map (integerAlgEquiv a b hcoords).toLinearEquiv
/-- The coordinate premise is explicit here and supplied for every actual row below. -/
lemma native_discriminant (hcoords:Coordinates a b) : NumberField.discr (F a b)=D a b := by
  calc
    NumberField.discr (F a b)=Algebra.discr ℤ (nativeBasis a b hcoords) :=
      (NumberField.discr_eq_discr (F a b) (nativeBasis a b hcoords)).symm
    _=Algebra.discr ℤ (basis a b) := by
      change Algebra.discr ℤ ((integerAlgEquiv a b hcoords) ∘ basis a b)=_
      exact (Algebra.discr_eq_discr_of_algEquiv (basis a b) (integerAlgEquiv a b hcoords)).symm
    _=D a b := basis_discriminant a b
end PELCMQuadraticNativeDiscriminant318
