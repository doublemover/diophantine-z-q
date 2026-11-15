module
public import ActualTwoDescentArithmeticKernel318
public section
noncomputable section
namespace ActualTwoDescentLocalCoefficientBound318
open ActualTwoDescentZeroSumCompletion318 ActualTwoDescentPrimeLaplacian318
open ActualTwoDescentThreeSymbol318 ActualTwoDescentMatrixCompletion318
open ActualTwoDescentArithmeticKernel318 ActualTwoDescentSupportParity318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000

lemma ones_dot_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s x : ι → ZMod 2) :
    dotProduct (ones ι) (Matrix.diagonal s *ᵥ x)=dotProduct s x := by
  simp [dotProduct,Matrix.mulVec,ones]

/-- Solve all three finite coefficient equations from local two-descent
on the ACTUAL prime-symbol matrix. This is an exact coefficient theorem,
not an assertion that the Selmer/Kummer interpretation has been proved. -/
theorem actual_local_coefficient_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Option ι → ℕ) [∀ i, Fact (p i).Prime] (hd : Function.Injective p)
    (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (hn : ((∏ i, p i : ℕ) : ZMod 12)=11)
    (a beta : Option ι → ZMod 2) (ha : ∑ i, a i=0)
    (hbeta : laplacian p *ᵥ beta=0) (hab : dotProduct a beta=1)
    (hcore : IsUnit (fun i j => sharp p a (some i) (some j) : Matrix ι ι (ZMod 2)))
    (u v : Option ι → ZMod 2) (δ : ZMod 2)
    (hfirst : laplacian p *ᵥ u+Matrix.diagonal (lambda p) *ᵥ v=δ • lambda p)
    (hsecond : (laplacian p+Matrix.diagonal (parity p)) *ᵥ v=0)
    (hthird : dotProduct (lambda p+parity p) v=0) :
    δ=0 ∧ v=0 ∧ ∃ c d : ZMod 2, u=c • ones (Option ι)+d • beta := by
  have hKcol := actual_laplacian_transpose_ones p hd hp2 hn
  have hKdot : dotProduct (ones (Option ι)) (laplacian p *ᵥ v)=0 := by
    rw [←Matrix.dotProduct_transpose_mulVec,hKcol,dotProduct_zero]
  have hs : dotProduct (parity p) v=0 := by
    have hz := congrArg (dotProduct (ones (Option ι))) hsecond
    rw [Matrix.add_mulVec,dotProduct_add,hKdot,ones_dot_diagonal,zero_add,dotProduct_zero] at hz
    exact hz
  have hKv : laplacian p *ᵥ v=Matrix.diagonal (parity p) *ᵥ v := by
    funext i
    apply eq_of_add_zero
    simpa only [Matrix.add_mulVec,Pi.add_apply,Pi.zero_apply] using congrFun hsecond i
  have houter : outer (parity p) (parity p) *ᵥ v=0 := by
    rw [outer_mulVec]
    funext i
    simp only [hs,mul_zero,Pi.zero_apply]
  have hKt : (laplacian p).transpose *ᵥ v=0 := by
    have h := congrArg (fun M : Matrix (Option ι) (Option ι) (ZMod 2) => M *ᵥ v)
      (actual_laplacian_reciprocity p hd hp2)
    rw [Matrix.add_mulVec,Matrix.add_mulVec,houter,zero_add,←hKv] at h
    apply add_left_cancel (a:=laplacian p *ᵥ v)
    simpa only [add_zero] using h
  have hλ : dotProduct (lambda p) v=0 := by
    have hh : dotProduct (lambda p) v+dotProduct (parity p) v=0 := by
      simpa only [dotProduct,Pi.add_apply,add_mul,Finset.sum_add_distrib] using hthird
    simpa only [hs,add_zero] using hh
  have hMt : (sharp p a).transpose *ᵥ v=0 := by
    rw [sharp,Matrix.transpose_add,outer_transpose,Matrix.add_mulVec,hKt,zero_add,outer_mulVec]
    funext i
    simp only [hλ,mul_zero,Pi.zero_apply]
  let A : Matrix ι ι (ZMod 2) := fun i j => sharp p a (some i) (some j)
  have he : sharp p a=completion A := actual_sharp_completion p hd hp2 hp3 hn a ha
  have hvconst : v=v none • ones (Option ι) := by
    rw [he] at hMt
    exact actual_completion_transpose_kernel A hcore v hMt
  have hsum : (∑ i, parity p i)=1 := actual_total_parity p hp2 hn
  have hvnone : v none=0 := by
    have h := congrArg (dotProduct (parity p)) hvconst
    rw [hs,dotProduct_smul] at h
    have hdot : dotProduct (parity p) (ones (Option ι))=1 := by
      simpa only [dotProduct,ones,mul_one] using hsum
    rw [hdot,smul_eq_mul,mul_one] at h
    exact h.symm
  have hv : v=0 := by rw [hvconst,hvnone,zero_smul]
  have hfir : laplacian p *ᵥ u=δ • lambda p := by
    simpa only [hv,Matrix.mulVec_zero,add_zero] using hfirst
  obtain ⟨hkernel,himage⟩ := actual_arithmetic_kernel p hd hp2 hp3 hn a beta ha hbeta hab hcore
  have hδ : δ=0 := by
    by_contra hh
    have hδone : δ=1 := by fin_cases δ <;> norm_num at hh ⊢
    apply himage u
    simpa only [hδone,one_smul] using hfir
  refine ⟨hδ,hv,(hkernel u).mp ?_⟩
  simpa only [hδ,zero_smul] using hfir

end ActualTwoDescentLocalCoefficientBound318
