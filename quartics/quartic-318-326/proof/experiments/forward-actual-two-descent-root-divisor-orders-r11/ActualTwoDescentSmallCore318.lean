module
public import ActualTwoDescentSmallPattern318
public section
noncomputable section
namespace ActualTwoDescentSmallCore318
open ActualTwoDescentSmallPattern318 ActualTwoDescentPrimeLaplacian318
open ActualTwoDescentThreeSymbol318 ActualTwoDescentMatrixCompletion318
open ActualTwoDescentIncidence318 ActualTwoDescentCore318 ActualTwoDescentArithmeticKernel318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000

def betaBlock (d : ℕ) (p : Index d → ℕ) : Matrix (BetaIndex d) (BetaIndex d) (ZMod 2) :=
  fun b c => sharp p (selector d) (bIndex b) (bIndex c)

lemma actual_I_row_sum (d : ℕ) (p : Index d → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) (H : Pattern d p) (i : Fin d) :
    (∑ j, edges p (iIndex i) j)=0 := by
  rw [Fintype.sum_option,Fintype.sum_sum_type]
  change edges p (iIndex i) none+((∑ b, edges p (iIndex i) (bIndex b))+
    (∑ j, edges p (iIndex i) (iIndex j)))=0
  have hz : (∑ j, edges p (iIndex i) (iIndex j))=0 :=
    Finset.sum_eq_zero (fun j _ => H.internal i j)
  rw [H.to_q0,hz,add_zero,zero_add]
  simp_rw [actual_cross_reverse d p hd hp2 H]
  exact incidence_column_sum d i

lemma actual_K_II (d : ℕ) (p : Index d → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) (H : Pattern d p) (i j : Fin d) :
    laplacian p (iIndex i) (iIndex j)=0 := by
  change edges p (iIndex i) (iIndex j)+
    Matrix.diagonal (fun k => ∑ l, edges p k l) (iIndex i) (iIndex j)=0
  rw [H.internal,zero_add,Matrix.diagonal_apply]
  split_ifs
  · exact actual_I_row_sum d p hd hp2 H i
  · rfl

/-- The entire deleted actual prime-symbol core has the retained D,C,Ct,0
shape. In particular the zero I block is proved from actual symbols/types. -/
lemma actual_small_core_shape (d : ℕ) (p : Index d → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) (H : Pattern d p) :
    (fun i j => sharp p (selector d) (some i) (some j) : Matrix (CoreIndex d) (CoreIndex d) (ZMod 2))=
      core d (betaBlock d p) := by
  ext i j
  cases i with
  | inl b =>
    cases j with
    | inl c => rfl
    | inr j =>
      change sharp p (selector d) (bIndex b) (iIndex j)=incidence d b j
      have hn : bIndex b ≠ iIndex j := by simp [bIndex,iIndex]
      simp only [sharp,Matrix.add_apply,outer,selector,iIndex,mul_zero,add_zero,
        laplacian,Matrix.add_apply,Matrix.diagonal_apply,hn,if_false,add_zero]
      exact H.cross b j
  | inr i =>
    cases j with
    | inl b =>
      change sharp p (selector d) (iIndex i) (bIndex b)=incidence d b i
      have hn : iIndex i ≠ bIndex b := by simp [bIndex,iIndex]
      rw [sharp,Matrix.add_apply,outer,actual_lambda_I d p H i,zero_mul,add_zero]
      simp only [laplacian,Matrix.add_apply,Matrix.diagonal_apply,hn,if_false,add_zero]
      exact actual_cross_reverse d p hd hp2 H i b
    | inr j =>
      change sharp p (selector d) (iIndex i) (iIndex j)=0
      rw [sharp,Matrix.add_apply,outer,actual_lambda_I d p H i,zero_mul,add_zero]
      exact actual_K_II d p hd hp2 H i j

/-- The decisive D sum1 comes from the actual beta-kernel equation and
actual [3/p] sum, not from a freely chosen replacement diagonal. -/
lemma actual_beta_block_sum (d : ℕ) (p : Index d → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (hn : ((∏ i, p i : ℕ) : ZMod 12)=11) (H : Pattern d p) :
    (∑ b, ∑ c, betaBlock d p b c)=1 := by
  have hbeta := actual_small_beta_kernel d p hd hp2 hn H
  have hrow (b : BetaIndex d) : (∑ c, laplacian p (bIndex b) (bIndex c))=0 := by
    simpa [Matrix.mulVec,dotProduct,beta,bIndex,Fintype.sum_option,Fintype.sum_sum_type] using
      congrFun hbeta (bIndex b)
  simp only [betaBlock,sharp,Matrix.add_apply,outer,Finset.sum_add_distrib,
    ←Finset.mul_sum,hrow,zero_add,selector_on_beta_sum,mul_one]
  exact actual_beta_lambda_sum d p hp3 hn H

/-- Nonsingularity of the literal arithmetic small core is now produced
from the actual prime prescriptions, closing this former premise. -/
theorem actual_small_core_unit (d : ℕ) (p : Index d → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (hn : ((∏ i, p i : ℕ) : ZMod 12)=11) (H : Pattern d p) :
    IsUnit (fun i j => sharp p (selector d) (some i) (some j) :
      Matrix (CoreIndex d) (CoreIndex d) (ZMod 2)) := by
  rw [actual_small_core_shape d p hd hp2 H]
  exact actual_core_unit d (betaBlock d p) (actual_beta_block_sum d p hd hp2 hp3 hn H)

/-- Both small-support arithmetic kernel conclusions now consume only
actual primes, exact prescribed symbols/types, and the actual product. -/
theorem actual_small_kernel (d : ℕ) (p : Index d → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (hn : ((∏ i, p i : ℕ) : ZMod 12)=11) (H : Pattern d p) :
    (∀ x, laplacian p *ᵥ x=0 ↔ ∃ c e : ZMod 2,
      x=c • ActualTwoDescentZeroSumCompletion318.ones (Index d)+e • beta d) ∧
    (∀ x, laplacian p *ᵥ x ≠ lambda p) := by
  exact actual_arithmetic_kernel p hd hp2 hp3 hn (selector d) (beta d)
    (selector_sum d) (actual_small_beta_kernel d p hd hp2 hn H) (selector_beta d)
    (actual_small_core_unit d p hd hp2 hp3 hn H)

end ActualTwoDescentSmallCore318
