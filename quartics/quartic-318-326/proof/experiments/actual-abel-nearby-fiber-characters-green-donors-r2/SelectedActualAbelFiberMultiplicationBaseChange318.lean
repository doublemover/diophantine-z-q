module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Basic

public section

noncomputable section

open Polynomial
open scoped TensorProduct

namespace SelectedActualAbelFiberMultiplicationBaseChange318

/-- The scalar dictionary for the actual fibre at the value z of J. -/
@[expose] def evaluationAlgebra (z : ℂ) : Algebra ℂ[X] ℂ :=
  (Polynomial.evalRingHom z).toAlgebra

variable {B : Type*} [CommRing B] [Algebra ℂ[X] B]

/-- Base change of the entire normalization algebra, not a selected
irreducible component or a reduced replacement of this fibre. -/
abbrev Fiber (z : ℂ) : Type _ :=
  letI : Algebra ℂ[X] ℂ := evaluationAlgebra z
  ℂ ⊗[ℂ[X]] B

@[expose] def intoFiber (z : ℂ) :
    letI : Algebra ℂ[X] ℂ := evaluationAlgebra z
    B →ₐ[ℂ[X]] Fiber (B := B) z := by
  letI : Algebra ℂ[X] ℂ := evaluationAlgebra z
  exact Algebra.TensorProduct.includeRight

/-- The apparent finite matrix family is the actual multiplication
matrix on the entire base-changed algebra, in the genuine tensor basis.
This holds at exceptional nonreduced levels as well as the simple ones. -/
theorem actual_fiber_leftMulMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (basis : Module.Basis ι ℂ[X] B) (b : B) (z : ℂ) :
    letI : Algebra ℂ[X] ℂ := evaluationAlgebra z
    Algebra.leftMulMatrix (basis.baseChange ℂ) (intoFiber z b) =
      (Algebra.leftMulMatrix basis b).map (Polynomial.evalRingHom z) := by
  letI : Algebra ℂ[X] ℂ := evaluationAlgebra z
  ext i j
  simp only [Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply]
  have hprod :
      intoFiber z b * (basis.baseChange ℂ) j = (1 : ℂ) ⊗ₜ[ℂ[X]] (b * basis j) := by
    change Algebra.TensorProduct.includeRight b * (basis.baseChange ℂ) j = _
    rw [Algebra.TensorProduct.includeRight_apply, Module.Basis.baseChange_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [hprod, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one] <;> rfl

end SelectedActualAbelFiberMultiplicationBaseChange318

#print axioms SelectedActualAbelFiberMultiplicationBaseChange318.actual_fiber_leftMulMatrix
