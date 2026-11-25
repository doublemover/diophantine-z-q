module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section

namespace OriginalSameJRealificationDet318

open Matrix
open scoped ComplexConjugate Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Mat (K : Type*) (I : Type*) := Matrix I I K

def realification (A : Mat ℂ I) : Mat ℝ (I ⊕ I) :=
  Matrix.fromBlocks (A.map Complex.re) (-(A.map Complex.im))
    (A.map Complex.im) (A.map Complex.re)

def rotations : Mat ℂ (I ⊕ I) :=
  Matrix.fromBlocks 1 (Complex.I • (1 : Mat ℂ I)) 1 ((-Complex.I) • (1 : Mat ℂ I))

theorem rotations_det_value : (rotations (I:=I)).det =
    ((-Complex.I)-Complex.I)^Fintype.card I := by
  rw [rotations, Matrix.det_fromBlocks_one₁₁, Matrix.mul_smul, Matrix.one_mul,
    ←sub_smul, Matrix.det_smul, Matrix.det_one, mul_one]

private theorem rotations_det : (rotations (I:=I)).det ≠ 0 := by
  have hI : (-Complex.I) - Complex.I ≠ 0 := by
    intro h
    have h' := congrArg Complex.im h
    norm_num at h'
  rw [rotations_det_value]
  exact pow_ne_zero _ hI

omit [Fintype I] [DecidableEq I] in
private theorem real_neg_map (S : Mat ℝ I) :
    (-S).map Complex.ofReal = -(S.map Complex.ofReal) := by
  ext i j
  exact Complex.ofReal_neg _

/-- The actual grouped real coordinate matrix is diagonalized by using
z and conjugate z as coordinate functions. No invertibility assumption
on the complex matrix, normal form, or diagonalizability of A is used. -/
theorem block_intertwine (A : Mat ℂ I) :
    rotations (I:=I) * (realification A).map Complex.ofReal =
      Matrix.fromBlocks A 0 0 (A.map (starRingEnd ℂ)) * rotations (I:=I) := by
  unfold rotations realification
  rw [Matrix.fromBlocks_map, real_neg_map]
  simp only [Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, add_zero, zero_add]
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_,?_,?_,?_⟩ <;> ext i j <;> apply Complex.ext <;>
    simp [Matrix.add_apply,Matrix.neg_apply,Matrix.smul_apply,Matrix.map_apply,
      Complex.mul_re,Complex.mul_im]

/-- The determinant of a change of COMPLEX coframe as a real map is
the square of the complex determinant norm, in every genus. -/
theorem real_det (A : Mat ℂ I) :
    (realification A).det = ‖A.det‖ ^ 2 := by
  have hconj : (A.map (starRingEnd ℂ)).det = conj A.det := by
    change ((starRingEnd ℂ).mapMatrix A).det = (starRingEnd ℂ) A.det
    exact ((starRingEnd ℂ).map_det A).symm
  have h := congrArg Matrix.det (block_intertwine A)
  rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_fromBlocks_zero₂₁,hconj] at h
  have he : ((realification A).map Complex.ofReal).det = A.det * conj A.det :=
    mul_left_cancel₀ rotations_det (h.trans (mul_comm _ _))
  have hcast : ((realification A).map Complex.ofReal).det =
      Complex.ofReal ((realification A).det) :=
    (Complex.ofRealHom.map_det _).symm
  rw [hcast,Complex.mul_conj'] at he
  exact Complex.ofReal_injective (he.trans (Complex.ofReal_pow _ _).symm)

end OriginalSameJRealificationDet318

#print axioms OriginalSameJRealificationDet318.rotations_det_value
#print axioms OriginalSameJRealificationDet318.block_intertwine
#print axioms OriginalSameJRealificationDet318.real_det
