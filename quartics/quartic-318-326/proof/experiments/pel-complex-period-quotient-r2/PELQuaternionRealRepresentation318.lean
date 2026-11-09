module
public import PELQuaternionAlternatingForm318
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Notation
public section
noncomputable section
namespace PELQuaternionRealRepresentation318
open PELQuaternionAlgebra318 QuaternionAlgebra Matrix
set_option maxHeartbeats 1200000
@[expose] def alpha : ℝ := Real.sqrt 210
@[expose] def beta : ℝ := Real.sqrt 5

theorem alpha_sq : alpha^2=210 := Real.sq_sqrt (by norm_num)
theorem beta_sq : beta^2=5 := Real.sq_sqrt (by norm_num)
theorem alpha_pos : 0<alpha := Real.sqrt_pos.mpr (by norm_num)
theorem beta_pos : 0<beta := Real.sqrt_pos.mpr (by norm_num)

/-- The actual rational quaternion action on a split real two-dimensional
carrier. The signs make μ a positive multiple of the standard rotation. -/
@[expose] def matrix (x : B) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(x.re:ℝ)+beta*(x.imJ:ℝ), -alpha*(x.imI:ℝ)+alpha*beta*(x.imK:ℝ);
      alpha*(x.imI:ℝ)+alpha*beta*(x.imK:ℝ), (x.re:ℝ)-beta*(x.imJ:ℝ)]

theorem matrix_add (x y : B) : matrix (x+y)=matrix x+matrix y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix] <;> ring

theorem matrix_mul (x y : B) : matrix (x*y)=matrix x*matrix y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix,Matrix.mul_apply,Fin.sum_univ_two] <;>
    push_cast <;> ring_nf <;> simp only [alpha_sq,beta_sq] <;> ring

@[expose] def representation : B →+* Matrix (Fin 2) (Fin 2) ℝ where
  toFun := matrix
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [matrix]
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [matrix]
  map_add' := matrix_add
  map_mul' := matrix_mul

/-- The fixed positive involution becomes actual matrix transpose, so the
period carrier receives the same adjoint convention as the rational algebra. -/
theorem rosati_transpose (x : B) : representation (rosati x)=(representation x).transpose := by
  rw [rosati_coordinates]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [representation,matrix,Matrix.transpose_apply] <;> ring

/-- This is a faithful representation of the specified rational algebra,
not merely a collection of matrices satisfying some generator equations. -/
theorem representation_injective : Function.Injective representation := by
  intro x y h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) h
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) h
  simp only [representation,matrix,Matrix.cons_val_zero,Matrix.cons_val_one] at h00 h01 h10 h11
  have hr : (x.re:ℝ)=(y.re:ℝ) := by linarith
  have hj : beta*((x.imJ:ℝ)-(y.imJ:ℝ))=0 := by linarith
  have hi : alpha*((x.imI:ℝ)-(y.imI:ℝ))=0 := by linarith
  have hk : (alpha*beta)*((x.imK:ℝ)-(y.imK:ℝ))=0 := by linarith
  have hj' := (mul_eq_zero.mp hj).resolve_left (ne_of_gt beta_pos)
  have hi' := (mul_eq_zero.mp hi).resolve_left (ne_of_gt alpha_pos)
  have hk' := (mul_eq_zero.mp hk).resolve_left (mul_ne_zero (ne_of_gt alpha_pos) (ne_of_gt beta_pos))
  apply QuaternionAlgebra.ext
  · exact_mod_cast hr
  · exact_mod_cast sub_eq_zero.mp hi'
  · exact_mod_cast sub_eq_zero.mp hj'
  · exact_mod_cast sub_eq_zero.mp hk'
end PELQuaternionRealRepresentation318
