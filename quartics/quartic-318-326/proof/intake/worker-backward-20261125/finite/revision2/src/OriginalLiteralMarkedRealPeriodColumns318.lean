module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

@[expose] public section
noncomputable section

namespace OriginalLiteralMarkedRealPeriodColumns318
open scoped Matrix
open Matrix

abbrev R4 := Fin 4→ℝ
abbrev C2 := Fin 2→ℂ
abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev M4 := Matrix (Fin 4) (Fin 4) ℝ

/-- Frozen original integral order basis: 1,i,(1+j)/2,i/2+k/10.
The split normalization has i=(0,-α;α,0) and j=(β,0;0,-β).
The row order is (m₀₀,m₁₀,m₀₁,m₁₁), not row-major. -/
def orderMatrix (α β:ℝ):M4 :=
  !![1,0,(1+β)/2,0; 0,α,0,α/2+α*β/10;
    0,-α,0,-α/2+α*β/10; 1,0,(1-β)/2,0]

def groupedRead (z:C2):R4 :=
  ![(z 0).re,(z 1).re,(z 0).im,(z 1).im]

def groupedWrite (v:R4):C2 :=
  ![(v 0:ℂ)+(v 2:ℂ)*Complex.I,(v 1:ℂ)+(v 3:ℂ)*Complex.I]

/-- Literal historical grouped order (Re z₀, Re z₁, Im z₀, Im z₁).
This is not the interleaved complex orientation; Haar uses absolute volume. -/
def groupedCoordinates : C2≃L[ℝ]R4 where
  toFun := groupedRead
  invFun := groupedWrite
  left_inv z := by
    funext i
    fin_cases i <;> apply Complex.ext <;>
      simp [groupedRead,groupedWrite]
  right_inv v := by
    funext i
    fin_cases i <;> simp [groupedRead,groupedWrite,Complex.mul_re,Complex.mul_im]
  map_add' z w := by
    funext i
    fin_cases i <;> simp [groupedRead]
  map_smul' a z := by
    funext i
    fin_cases i <;> simp [groupedRead,Complex.real_smul,Complex.mul_re,Complex.mul_im]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp only [groupedRead] <;> fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp only [groupedWrite] <;> fun_prop

/-- Real matrix evaluation M↦M(τ,1), exactly with the historical
column grouping, not chosen by an equality of determinants. -/
def rowMatrix (τ:ℂ):M4 :=
  !![τ.re,0,1,0; 0,τ.re,0,1; τ.im,0,0,0; 0,τ.im,0,0]

def matrixRead (v:R4):M2 := !![v 0,v 2;v 1,v 3]
def evaluation (τ:ℂ) (M:M2):C2 :=
  fun i=>(M i 0:ℂ)*τ+(M i 1:ℂ)

theorem row_matrix_exact (τ:ℂ) (v:R4):
    groupedRead (evaluation τ (matrixRead v))=(rowMatrix τ).mulVec v := by
  funext i
  fin_cases i <;> simp [groupedRead,evaluation,matrixRead,rowMatrix,Matrix.mulVec,dotProduct,
    Fin.sum_univ_succ,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im] <;> ring

def markedRealMatrix (α β:ℝ) (τ:ℂ):M4 := rowMatrix τ * orderMatrix α β

theorem order_matrix_det (α β:ℝ) (ha:α^2=210) (hb:β^2=5):
    (orderMatrix α β).det=210 := by
  have h : (orderMatrix α β).det=α^2*β^2/5 := by
    rw [Matrix.det_succ_row_zero,Fin.sum_univ_four]
    norm_num [orderMatrix,Matrix.det_fin_three,Matrix.submatrix_apply,Fin.succAbove]
    ring
  rw [h,ha,hb]
  norm_num

theorem row_matrix_det (τ:ℂ): (rowMatrix τ).det=τ.im^2 := by
  rw [Matrix.det_succ_row_zero,Fin.sum_univ_four]
  norm_num [rowMatrix,Matrix.det_fin_three,Matrix.submatrix_apply,Fin.succAbove]
  ring

/-- The exact real determinant in the original period ordering. It
literally gives the absolute covolume for positive Im τ. This proof
has no premise involving the selected Hodge Jacobian. -/
theorem exact_signed_period_det (α β:ℝ) (ha:α^2=210) (hb:β^2=5) (τ:ℂ):
    (markedRealMatrix α β τ).det=210*τ.im^2 := by
  rw [markedRealMatrix,Matrix.det_mul,row_matrix_det,order_matrix_det α β ha hb,mul_comm]

theorem real_summation_continuous (M:M4):Continuous (fun v:R4=>M.mulVec v) := by
  apply continuous_pi
  intro i
  simp only [Matrix.mulVec,dotProduct]
  exact continuous_finsetSum _ fun j _=>continuous_const.mul (continuous_apply j)

def realMatrixEquiv (M:M4) (d:IsUnit M.det):R4≃L[ℝ]R4 := by
  let b := Pi.basisFun ℝ (Fin 4)
  let q := Matrix.toLinearEquiv b M d
  refine ⟨q,?_,?_⟩
  · change Continuous (fun v:R4=>Matrix.toLin b b M v)
    rw [Matrix.toLin_eq_toLin']
    exact real_summation_continuous M
  · change Continuous (fun v:R4=>Matrix.toLin b b M⁻¹ v)
    rw [Matrix.toLin_eq_toLin']
    exact real_summation_continuous M⁻¹

def actualColumns (α β:ℝ) (ha:α^2=210) (hb:β^2=5) (τ:ℂ) (hy:0<τ.im):
    R4≃L[ℝ]C2 :=
  (realMatrixEquiv (markedRealMatrix α β τ)
    (isUnit_iff_ne_zero.mpr (by rw [exact_signed_period_det α β ha hb τ]; positivity))).trans
    groupedCoordinates.symm

theorem columns_are_actual_evaluation (α β:ℝ) (ha:α^2=210) (hb:β^2=5)
    (τ:ℂ) (hy:0<τ.im) (v:R4):
    actualColumns α β ha hb τ hy v=evaluation τ (matrixRead ((orderMatrix α β).mulVec v)) := by
  apply groupedCoordinates.injective
  unfold actualColumns
  simp only [ContinuousLinearEquiv.trans_apply,ContinuousLinearEquiv.apply_symm_apply]
  change Matrix.toLin (Pi.basisFun ℝ (Fin 4)) (Pi.basisFun ℝ (Fin 4))
    (markedRealMatrix α β τ) v = groupedRead (evaluation τ (matrixRead ((orderMatrix α β).mulVec v)))
  rw [Matrix.toLin_eq_toLin',row_matrix_exact]
  exact (Matrix.mulVec_mulVec v (rowMatrix τ) (orderMatrix α β)).symm

/-- The kernel lattice uses exactly the four integral columns of the
same original order, not their rational span or a finite-index subset. -/
def integerPeriods (α β:ℝ) (ha:α^2=210) (hb:β^2=5) (τ:ℂ) (hy:0<τ.im):
    (Fin 4→ℤ)→+C2 where
  toFun m := actualColumns α β ha hb τ hy (fun i=>((m i:ℤ):ℝ))
  map_zero' := by
    have h : (fun i:Fin 4=>(((0:Fin 4→ℤ) i:ℤ):ℝ))=0 := by
      funext i
      exact Int.cast_zero
    rw [h,map_zero]
  map_add' m n := by
    have h : (fun i=>(((m+n) i:ℤ):ℝ))=(fun i=>((m i:ℤ):ℝ))+(fun i=>((n i:ℤ):ℝ)) := by
      funext i
      exact Int.cast_add _ _
    rw [h,map_add]

end OriginalLiteralMarkedRealPeriodColumns318
