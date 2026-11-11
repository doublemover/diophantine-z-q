module
public import ActualTwoDescentThreeSymbol318
public section
noncomputable section
namespace ActualTwoDescentMatrixCompletion318
open ActualTwoDescentZeroSumCompletion318 ActualTwoDescentPrimeLaplacian318
open ActualTwoDescentThreeSymbol318 ActualTwoDescentIncidence318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000

lemma eq_of_add_zero (a b : ZMod 2) (h : a+b=0) : a=b :=
  add_right_cancel (h.trans (actual_two_add b).symm)

/-- Zero row and column sums identify the entire original full matrix
with the unique completion of its actual deleted q0 core. -/
theorem actual_completion_unique {ι : Type*} [Fintype ι]
    (M : Matrix (Option ι) (Option ι) (ZMod 2))
    (hr : M *ᵥ ones (Option ι)=0) (hc : M.transpose *ᵥ ones (Option ι)=0) :
    M=completion (fun i j => M (some i) (some j)) := by
  have row (i : Option ι) : M i none=∑ j, M i (some j) := by
    apply eq_of_add_zero
    simpa [Matrix.mulVec,dotProduct,ones,Fintype.sum_option,add_comm] using congrFun hr i
  have col (j : Option ι) : M none j=∑ i, M (some i) j := by
    apply eq_of_add_zero
    simpa [Matrix.mulVec,dotProduct,ones,Fintype.sum_option,add_comm] using congrFun hc j
  ext i j
  cases i with
  | some i =>
    cases j with
    | some j => rfl
    | none => exact row (some i)
  | none =>
    cases j with
    | some j => exact col (some j)
    | none =>
      change M none none=∑ i, ∑ j, M (some i) (some j)
      rw [row none]
      simp_rw [col]
      exact Finset.sum_comm

lemma completion_transpose {ι : Type*} [Fintype ι] (A : Matrix ι ι (ZMod 2)) :
    (completion A).transpose=completion A.transpose := by
  ext i j
  cases i <;> cases j <;> simp [completion,Matrix.transpose_apply,Finset.sum_comm]

lemma actual_completion_transpose_kernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (ZMod 2)) (hA : IsUnit A)
    (x : Option ι → ZMod 2) (hx : (completion A).transpose *ᵥ x=0) :
    x=x none • ones (Option ι) := by
  rw [completion_transpose] at hx
  exact actual_completion_kernel A.transpose (Matrix.isUnit_transpose.mpr hA) x hx

def sharp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (a : ι → ZMod 2) : Matrix ι ι (ZMod 2) :=
  laplacian p+outer (lambda p) a

lemma outer_transpose {ι : Type*} (v w : ι → ZMod 2) :
    (outer v w).transpose=outer w v := by
  ext i j
  exact mul_comm _ _

/-- K-sharp is the actual prime-symbol matrix with its specified rank-one
correction. Its full row/column normalization is now discharged from the
actual product residue and the selector parity. -/
theorem actual_sharp_normalization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hd : Function.Injective p)
    (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (hn : ((∏ i, p i : ℕ) : ZMod 12)=11)
    (a : ι → ZMod 2) (ha : ∑ i, a i=0) :
    sharp p a *ᵥ ones ι=0 ∧ (sharp p a).transpose *ᵥ ones ι=0 := by
  constructor
  · rw [sharp,Matrix.add_mulVec,actual_laplacian_ones,zero_add,outer_mulVec]
    funext i
    simp only [dotProduct,ones,mul_one,ha,mul_zero,Pi.zero_apply]
  · rw [sharp,Matrix.transpose_add,outer_transpose,Matrix.add_mulVec,
      actual_laplacian_transpose_ones p hd hp2 hn,zero_add,outer_mulVec]
    have hλ := actual_lambda_sum p hp3 hn
    funext i
    simp only [dotProduct,ones,mul_one,hλ,mul_zero,Pi.zero_apply]

/-- The genuine arithmetic correction is the same completion consumed by
the earlier nonsingular-core proof. No replacement full matrix is chosen. -/
theorem actual_sharp_completion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Option ι → ℕ) [∀ i, Fact (p i).Prime] (hd : Function.Injective p)
    (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (hn : ((∏ i, p i : ℕ) : ZMod 12)=11)
    (a : Option ι → ZMod 2) (ha : ∑ i, a i=0) :
    sharp p a=completion (fun i j => sharp p a (some i) (some j)) := by
  obtain ⟨hr,hc⟩ := actual_sharp_normalization p hd hp2 hp3 hn a ha
  exact actual_completion_unique _ hr hc

end ActualTwoDescentMatrixCompletion318
