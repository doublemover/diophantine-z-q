module
public import PELUnramifiedPadicConic318
public section
noncomputable section
namespace PELConicMatrixSplitting318
open QuaternionAlgebra Matrix
set_option maxHeartbeats 1600000
universe u
variable {F : Type u} [Field F] [hF : CharZero F]
abbrev B (F : Type u) [Field F] := QuaternionAlgebra F (-210) 0 5
include hF

/-- The original generators are I=[0,-210;1,0] and
J=[x,210y;y,-x]. The conic equation supplies J²=5. -/
@[expose] def matrix (x y : F) (q : B F) : Matrix (Fin 2) (Fin 2) F :=
  !![q.re+x*q.imJ-210*y*q.imK, -210*q.imI+210*y*q.imJ+210*x*q.imK;
     q.imI+y*q.imJ+x*q.imK, q.re-x*q.imJ+210*y*q.imK]

theorem matrix_mul (x y : F) (hxy : x^2+210*y^2=5) (a b : B F) :
    matrix x y (a*b)=matrix x y a*matrix x y b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix,Matrix.mul_apply,Fin.sum_univ_two]
  · linear_combination -(a.imJ*b.imJ+210*a.imK*b.imK)*hxy
  · linear_combination (210*(a.imK*b.imJ-a.imJ*b.imK))*hxy
  · linear_combination (a.imJ*b.imK-a.imK*b.imJ)*hxy
  · linear_combination -(a.imJ*b.imJ+210*a.imK*b.imK)*hxy

@[expose] def representation (x y : F) (hxy : x^2+210*y^2=5) :
    B F →+* Matrix (Fin 2) (Fin 2) F where
  toFun := matrix x y
  map_zero' := by ext i j;fin_cases i <;> fin_cases j <;> simp [matrix]
  map_one' := by ext i j;fin_cases i <;> fin_cases j <;> simp [matrix]
  map_add' a b := by ext i j;fin_cases i <;> fin_cases j <;> simp [matrix] <;> ring
  map_mul' := matrix_mul x y hxy

/-- An explicit inverse on ALL matrices, not just a faithful representation
of the generators or a dimension argument. -/
@[expose] def unmatrix (x y : F) (M : Matrix (Fin 2) (Fin 2) F) : B F :=
  ⟨(M 0 0+M 1 1)/2, (M 1 0-M 0 1/210)/2,
    (x*(M 0 0-M 1 1)+210*y*(M 1 0+M 0 1/210))/10,
    (-y*(M 0 0-M 1 1)+x*(M 1 0+M 0 1/210))/10⟩

theorem unmatrix_matrix (x y : F) (hxy : x^2+210*y^2=5) (q : B F) :
    unmatrix x y (matrix x y q)=q := by
  apply QuaternionAlgebra.ext
  · change ((q.re+x*q.imJ-210*y*q.imK)+(q.re-x*q.imJ+210*y*q.imK))/2=q.re
    ring
  · change ((q.imI+y*q.imJ+x*q.imK)-(-210*q.imI+210*y*q.imJ+210*x*q.imK)/210)/2=q.imI
    ring
  · change (x*((q.re+x*q.imJ-210*y*q.imK)-(q.re-x*q.imJ+210*y*q.imK))+
      210*y*((q.imI+y*q.imJ+x*q.imK)+(-210*q.imI+210*y*q.imJ+210*x*q.imK)/210))/10=q.imJ
    linear_combination (q.imJ/5)*hxy
  · change (-y*((q.re+x*q.imJ-210*y*q.imK)-(q.re-x*q.imJ+210*y*q.imK))+
      x*((q.imI+y*q.imJ+x*q.imK)+(-210*q.imI+210*y*q.imJ+210*x*q.imK)/210))/10=q.imK
    linear_combination (q.imK/5)*hxy

theorem matrix_unmatrix (x y : F) (hxy : x^2+210*y^2=5)
    (M : Matrix (Fin 2) (Fin 2) F) : matrix x y (unmatrix x y M)=M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix,unmatrix]
  · linear_combination ((M 0 0-M 1 1)/10)*hxy
  · linear_combination ((M 0 1+210*M 1 0)/10)*hxy
  · linear_combination ((M 0 1+210*M 1 0)/2100)*hxy
  · linear_combination (-(M 0 0-M 1 1)/10)*hxy

/-- Literal splitting of the original quaternion presentation. -/
@[expose] def splitting (x y : F) (hxy : x^2+210*y^2=5) :
    B F ≃+* Matrix (Fin 2) (Fin 2) F :=
  { representation x y hxy with
    invFun := unmatrix x y
    left_inv := unmatrix_matrix x y hxy
    right_inv := matrix_unmatrix x y hxy }

theorem splitting_scalar (x y : F) (hxy : x^2+210*y^2=5) (a : F) :
    splitting x y hxy (algebraMap F (B F) a)=
      algebraMap F (Matrix (Fin 2) (Fin 2) F) a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitting,representation,matrix,QuaternionAlgebra.algebraMap_eq,
      Matrix.algebraMap_matrix_apply]

theorem matrix_det (x y : F) (hxy : x^2+210*y^2=5) (q : B F) :
    (matrix x y q).det=q.re^2+210*q.imI^2-5*q.imJ^2-1050*q.imK^2 := by
  rw [Matrix.det_fin_two]
  change (q.re+x*q.imJ-210*y*q.imK)*(q.re-x*q.imJ+210*y*q.imK)-
    (-210*q.imI+210*y*q.imJ+210*x*q.imK)*(q.imI+y*q.imJ+x*q.imK)=_
  linear_combination -(q.imJ^2+210*q.imK^2)*hxy
end PELConicMatrixSplitting318
