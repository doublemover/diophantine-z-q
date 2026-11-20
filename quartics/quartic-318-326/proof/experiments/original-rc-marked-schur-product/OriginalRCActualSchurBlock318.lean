module
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Data.Matrix.Block
public section

namespace OriginalRCActualSchurBlock318
open Matrix

variable {R I J : Type*} [CommRing R] [Fintype I] [DecidableEq I]
variable [Fintype J] [DecidableEq J]

/-- Actual target change for the chosen pivot chart, not a determinant
unit stipulated separately. -/
@[expose] def leftElim (Ai : Matrix I I R) (C : Matrix J I R) :
    Matrix (I ⊕ J) (I ⊕ J) R := fromBlocks 1 0 (-(C * Ai)) 1

@[expose] def rightElim (Ai : Matrix I I R) (B : Matrix I J R) :
    Matrix (I ⊕ J) (I ⊕ J) R := fromBlocks 1 (-(Ai * B)) 0 1

theorem leftElim_det (Ai : Matrix I I R) (C : Matrix J I R) :
    (leftElim Ai C).det = 1 := by
  simp only [leftElim,Matrix.det_fromBlocks_zero₁₂,Matrix.det_one,mul_one]

theorem rightElim_det (Ai : Matrix I I R) (B : Matrix I J R) :
    (rightElim Ai B).det = 1 := by
  simp only [rightElim,Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,mul_one]

/-- The actual two elementary changes in the V13 elimination chart. -/
theorem schur_chart {K : Type*} [Fintype K] [DecidableEq K]
    (A Ai : Matrix I I R) (B : Matrix I J R)
    (C : Matrix K I R) (D : Matrix K J R)
    (hi : Ai * A = 1) (hj : A * Ai = 1) :
    leftElim Ai C * fromBlocks A B C D * rightElim Ai B =
      fromBlocks A 0 0 (D - C * Ai * B) := by
  have hleft : leftElim Ai C * fromBlocks A B C D =
      fromBlocks A B 0 (D - C * Ai * B) := by
    simp only [leftElim,Matrix.fromBlocks_multiply,Matrix.one_mul,
      Matrix.zero_mul,add_zero,Matrix.neg_mul,Matrix.mul_assoc,hi,
      Matrix.mul_one,neg_add_cancel,sub_eq_add_neg,add_comm]
  rw [hleft]
  simp only [rightElim,Matrix.fromBlocks_multiply,Matrix.mul_one,Matrix.mul_zero,
    Matrix.zero_mul,Matrix.mul_neg,←Matrix.mul_assoc,hj,Matrix.one_mul,
    add_zero,zero_add,neg_add_cancel]

/-- The determinant factor of the actual chart: both elementary changes
have determinant one, including if a surviving block is singular. -/
theorem schur_det (A Ai : Matrix I I R) (B : Matrix I J R)
    (C : Matrix J I R) (D : Matrix J J R)
    (hi : Ai * A = 1) (hj : A * Ai = 1) :
    (fromBlocks A B C D).det = A.det * (D - C * Ai * B).det := by
  have h := congrArg (fun M : Matrix (I ⊕ J) (I ⊕ J) R => M.det)
    (schur_chart A Ai B C D hi hj)
  simpa only [Matrix.det_mul,leftElim_det,rightElim_det,Matrix.det_fromBlocks_zero₂₁,
    one_mul,mul_one] using h

/-- Drop the inverse completely: the lower cleared survivor row
(−C adj A, det A·I) annihilates the actual pivot columns. -/
theorem cleared_incoming (A : Matrix I I R) (C : Matrix J I R) :
    (-(C * A.adjugate)) * A + A.det • C = 0 := by
  rw [Matrix.neg_mul,Matrix.mul_assoc,Matrix.adjugate_mul,Matrix.mul_smul,
    Matrix.mul_one,neg_add_cancel]

/-- The actual cleared outgoing inclusion is (−adj A·B, det A·I)^T.
This companion identity holds over the SAME finite coefficient ring. -/
theorem cleared_outgoing (A : Matrix I I R) (B : Matrix I J R) :
    A * (-(A.adjugate * B)) + A.det • B = 0 := by
  rw [Matrix.mul_neg,←Matrix.mul_assoc,Matrix.mul_adjugate,Matrix.smul_mul,
    Matrix.one_mul,neg_add_cancel]

/-- A real inverse identifies its cleared row or column with the adjugate;
no appeal to a choice of diagonal factors. -/
theorem adjugate_of_right_inverse (A Ai : Matrix I I R) (h : A * Ai = 1) :
    A.adjugate = A.det • Ai := by
  calc
    _ = A.adjugate * (A * Ai) := by rw [h,Matrix.mul_one]
    _ = _ := by
      rw [←Matrix.mul_assoc,Matrix.adjugate_mul,Matrix.smul_mul,Matrix.one_mul]

/-- The following differential keeps its genuine surviving columns:
the old composition relation kills exactly the altered pivot columns. -/
theorem following_pivot_zero {L : Type*} (A Ai : Matrix I I R) (C : Matrix J I R)
    (Y : Matrix L I R) (Z : Matrix L J R) (hInv : A * Ai = 1)
    (hComp : Y * A + Z * C = 0) :
    Y + (Z * C) * Ai = 0 := by
  have hs := congrArg (fun x : Matrix L I R => x * Ai) hComp
  simpa only [Matrix.add_mul,Matrix.zero_mul,
    Matrix.mul_assoc Y A Ai,hInv,Matrix.mul_one] using hs

/-- The preceding differential keeps its genuine surviving rows as well. -/
theorem preceding_pivot_zero {L : Type*} (A Ai : Matrix I I R) (B : Matrix I J R)
    (Y : Matrix I L R) (Z : Matrix J L R) (hInv : Ai * A = 1)
    (hComp : A * Y + B * Z = 0) :
    Y + (Ai * B) * Z = 0 := by
  have hs := congrArg (fun x : Matrix I L R => Ai * x) hComp
  simpa only [Matrix.mul_add,Matrix.mul_zero,
    ←Matrix.mul_assoc,hInv,Matrix.one_mul] using hs

end OriginalRCActualSchurBlock318

#print axioms OriginalRCActualSchurBlock318.schur_det
#print axioms OriginalRCActualSchurBlock318.cleared_incoming
