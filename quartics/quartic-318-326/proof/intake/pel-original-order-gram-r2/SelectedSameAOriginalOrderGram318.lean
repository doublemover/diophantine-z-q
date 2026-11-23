module

public import SelectedActualPELPeriodColumns318
import all SelectedActualPELPeriodColumns318
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

public section
noncomputable section

open QuaternionicRealPeriod318 SelectedActualPELPeriodColumns318
open scoped Matrix

namespace SelectedSameAOriginalOrderGram318

/-- Fixed splitting of the original discriminant-210 order, with the
basis 1, i, (1+j)/2, i/2+k/10, in that order. Here i²=-210 and j²=5. -/
def splitBasis (a b : ℝ) : Fin 4 → RealMatrices :=
  ![!![1,0;0,1], !![0,-a;a,0], !![(1+b)/2,0;0,(1-b)/2],
    !![0,-a/2+a*b/10;a/2+a*b/10,0]]

def splitMu (a : ℝ) : RealMatrices := !![0,-a;a,0]

/-- The inverse in the same real splitting, not an independently
scaled Rosati parameter. -/
def splitNu (a : ℝ) : RealMatrices := !![0,a/210;-a/210,0]

theorem splitMu_inverse (a : ℝ) (ha : a ^ 2 = 210) :
    splitMu a * splitNu a = 1 ∧ splitNu a * splitMu a = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [splitMu, splitNu, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    nlinarith only [ha]

/-- The positive period orientation is the negative of the raw rational
trace convention with upper entries (-2,0,-1,1,0,0). -/
def principalGram : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0,2,0,1; -2,0,-1,0; 0,1,0,0; -1,0,0,0]

theorem principalGram_det : principalGram.det = 1 := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  norm_num [principalGram, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove]

set_option maxHeartbeats 500000 in
private theorem signed_entry (a b : ℝ) (ha : a ^ 2 = 210) (hb : b ^ 2 = 5)
    (i j : Fin 4) :
    (principalGram i j : ℝ) =
      -(Matrix.trace ((splitNu a * splitBasis a b i) * adj (splitBasis a b j))) := by
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [principalGram, splitNu, splitBasis, adj, Matrix.trace, Matrix.diag_apply,
      Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring_nf
  all_goals norm_num [ha, hb]

/-- Canonical orientation and integrality for every one of the sixteen
entries in the same split basis as the period columns. -/
theorem signed_gram (a b : ℝ) (ha : a ^ 2 = 210) (hb : b ^ 2 = 5) :
    (((leftBlock (splitNu a)) * basisMatrix (splitBasis a b)).transpose * G) *
      basisMatrix (splitBasis a b) = principalGram.map (Int.castRingHom ℝ) :=
  compare_integral_gram (splitNu a) (splitBasis a b) principalGram
    (signed_entry a b ha hb)

theorem real_gram_det (a b : ℝ) (ha : a ^ 2 = 210) (hb : b ^ 2 = 5) :
    ((((leftBlock (splitNu a)) * basisMatrix (splitBasis a b)).transpose * G) *
      basisMatrix (splitBasis a b)).det = 1 := by
  rw [signed_gram a b ha hb]
  have h : (principalGram.map (Int.castRingHom ℝ)).det = (principalGram.det : ℝ) :=
    (Int.cast_det principalGram).symm
  exact h.trans ((congrArg (fun z : ℤ => (z : ℝ)) principalGram_det).trans
    (Int.cast_one : ((1 : ℤ) : ℝ) = 1))

private theorem four_column_det (a u v w z : ℝ) :
    (!![1,0,u,0;0,a,0,v;0,-a,0,w;1,0,z,0] : R4).det =
      (u-z)*a*(w+v) := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  norm_num [Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove]
  ring

/-- In the frozen column ordering (a,c;b,d), the signed real order
determinant itself is +210. No principal determinant is supplied. -/
theorem order_det (a b : ℝ) (ha : a ^ 2 = 210) (hb : b ^ 2 = 5) :
    (basisMatrix (splitBasis a b)).det = 210 := by
  have hm : basisMatrix (splitBasis a b) =
      (!![1,0,(1+b)/2,0;0,a,0,a/2+a*b/10;0,-a,0,-a/2+a*b/10;
         1,0,(1-b)/2,0] : R4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [basisMatrix, flatten, splitBasis]
  rw [hm, four_column_det]
  calc
    ((1+b)/2 - (1-b)/2) * a * ((-a/2+a*b/10) + (a/2+a*b/10))
      = a^2*b^2/5 := by ring
    _ = 210 := by norm_num [ha,hb]

/-- Exact joint output for the actual ordered basis in the original
real chart, after the geometric complex coframe X has been identified.
This does not assert analytical identification of an arbitrary A. -/
theorem original_outputs (τ : ℂ) (X : C2) :
    let a := Real.sqrt 210
    let b := Real.sqrt 5
    let T := basisMatrix (splitBasis a b)
    coframedPeriods τ X (splitBasis a b) = ((RX X) * (Bτ τ)) * T ∧
    (((leftBlock (splitNu a)) * T).transpose * G) * T =
      principalGram.map (Int.castRingHom ℝ) ∧
    ((((leftBlock (splitNu a)) * T).transpose * G) * T).det = 1 ∧
    T.det = 210 := by
  have ha : (Real.sqrt 210)^2 = 210 := Real.sq_sqrt (by norm_num)
  have hb : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num)
  exact ⟨coframedPeriods_eq _ _ _, signed_gram _ _ ha hb, real_gram_det _ _ ha hb,
    order_det _ _ ha hb⟩

end SelectedSameAOriginalOrderGram318

#print axioms SelectedSameAOriginalOrderGram318.splitMu_inverse
#print axioms SelectedSameAOriginalOrderGram318.original_outputs
