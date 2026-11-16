module
public import ActualTwoDescentRetainedSmallPattern318
public section
noncomputable section
namespace ActualTwoDescentFiniteConclusion318
open ActualTwoDescentPrimeLaplacian318 ActualTwoDescentThreeSymbol318
open ActualTwoDescentMatrixCompletion318 ActualTwoDescentArithmeticKernel318
open ActualTwoDescentLocalCoefficientBound318 ActualTwoDescentZeroSumCompletion318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000

/-- The finite arithmetic conclusions needed before the genuine local
Selmer interpretation and global Kummer-point existence step. -/
structure Conclusion {U : Type*} [Fintype U] [DecidableEq U]
    (p : Option U → ℕ) (a beta : Option U → ZMod 2) (N : ℕ) : Prop where
  residue : ((∏ i, p i : ℕ) : ZMod 12)=11
  squarefree : Squarefree (∏ i, p i)
  large : N < ∏ i, p i
  beta_kernel : laplacian p *ᵥ beta=0
  core_unit : IsUnit (fun i j => sharp p a (some i) (some j) : Matrix U U (ZMod 2))
  kernel : ∀ x, laplacian p *ᵥ x=0 ↔
    ∃ c e : ZMod 2, x=c • ones (Option U)+e • beta
  lambda_excluded : ∀ x, laplacian p *ᵥ x ≠ lambda p
  local_coefficients : ∀ u v δ,
    laplacian p *ᵥ u+Matrix.diagonal (lambda p) *ᵥ v=δ • lambda p →
    (laplacian p+Matrix.diagonal (parity p)) *ᵥ v=0 →
    dotProduct (lambda p+parity p) v=0 →
    δ=0 ∧ v=0 ∧ ∃ c e : ZMod 2, u=c • ones (Option U)+e • beta

theorem actual_finite_conclusion {U : Type*} [Fintype U] [DecidableEq U]
    (p : Option U → ℕ) [∀ i, Fact (p i).Prime] (hd : Function.Injective p)
    (hc : ∀ i, Nat.Coprime (p i) 12) (hn : ((∏ i, p i : ℕ) : ZMod 12)=11)
    (a beta : Option U → ZMod 2) (ha : ∑ i, a i=0) (hab : dotProduct a beta=1)
    (hb : laplacian p *ᵥ beta=0)
    (hcore : IsUnit (fun i j => sharp p a (some i) (some j) : Matrix U U (ZMod 2)))
    (N : ℕ) (hN : N < p none) : Conclusion p a beta N := by
  have hp2 : ∀ i, p i ≠ 2 := by
    intro i he
    have h := hc i
    rw [he] at h
    norm_num at h
  have hp3 : ∀ i, p i ≠ 3 := by
    intro i he
    have h := hc i
    rw [he] at h
    norm_num at h
  have hsquare : Squarefree (∏ i, p i) := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i _ j _ hij
      apply Nat.coprime_iff_isRelPrime.mp
      apply (Nat.coprime_primes (Fact.out : (p i).Prime) (Fact.out : (p j).Prime)).mpr
      exact fun he => hij (hd he)
    · intro i _
      exact (Fact.out : (p i).Prime).squarefree
  have hpos : 0 < ∏ i, p i := by
    apply Finset.prod_pos
    intro i _
    exact (Fact.out : (p i).Prime).pos
  have hlarge : N < ∏ i, p i := lt_of_lt_of_le hN
    (Nat.le_of_dvd hpos (Finset.dvd_prod_of_mem p (Finset.mem_univ none)))
  obtain ⟨hker,himage⟩ := actual_arithmetic_kernel p hd hp2 hp3 hn a beta ha hb hab hcore
  refine ⟨hn,hsquare,hlarge,hb,hcore,hker,himage,?_⟩
  intro u v δ hfirst hsecond hthird
  exact actual_local_coefficient_bound p hd hp2 hp3 hn a beta ha hb hab hcore
    u v δ hfirst hsecond hthird

end ActualTwoDescentFiniteConclusion318
