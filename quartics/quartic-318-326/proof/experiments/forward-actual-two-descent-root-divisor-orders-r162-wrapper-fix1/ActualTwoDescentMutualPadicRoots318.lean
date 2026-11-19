module
public import ActualTwoDescentThreeAdicTorsion318
public section
noncomputable section
namespace ActualTwoDescentMutualPadicRoots318
open ActualTwoDescentMutualSymbolRows318 ActualTwoDescentBaselineSupport318
open ActualTwoDescentJacobiPadicSquare318 ActualTwoDescentTwoAdicSquare318
open scoped BigOperators
set_option maxHeartbeats 16000000

/-- The original mutual PRODUCT-square symbol conditions now supply actual
nonzero roots in the corresponding p-adic fields, at every original prime. -/
theorem actual_mutual_padic_roots {B J : Type*} [Fintype B] [Fintype J]
    (qB : B → ℕ) (qJ : J → ℕ) [∀ b, Fact (qB b).Prime] [∀ j, Fact (qJ j).Prime]
    (hdis : ∀ b j, qB b ≠ qJ j)
    (hB2 : ∀ b, qB b ≠ 2) (hJ2 : ∀ j, qJ j ≠ 2) (H : MutualSymbols qB qJ) :
    (∀ b, ∃ r : ℚ_[qB b], r ≠ 0 ∧ r^2=((∏ j, qJ j : ℕ) : ℚ_[qB b])) ∧
    (∀ j, ∃ r : ℚ_[qJ j], r ≠ 0 ∧ r^2=((∏ b, qB b : ℕ) : ℚ_[qJ j])) := by
  have hB0 : (∏ b, qB b) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun b _ => (Fact.out : (qB b).Prime).ne_zero)
  have hJ0 : (∏ j, qJ j) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun j _ => (Fact.out : (qJ j).Prime).ne_zero)
  constructor
  · intro b
    apply actual_jacobi_padic_unit_square (hB2 b) _ hJ0 _ (H.theta_at_beta b)
    apply Nat.coprime_prod_left_iff.mpr
    intro j _
    exact (Nat.coprime_primes Fact.out Fact.out).mpr (Ne.symm (hdis b j))
  · intro j
    apply actual_jacobi_padic_unit_square (hJ2 j) _ hB0 _ (H.beta_at_theta j)
    apply Nat.coprime_prod_left_iff.mpr
    intro b _
    exact (Nat.coprime_primes Fact.out Fact.out).mpr (hdis b j)

/-- The same original beta/theta products are actual squares at2 and at
infinity. The statement does not replace p-adic roots by residue symbols. -/
theorem actual_two_and_real_roots {B J : Type*} [Fintype B] [Fintype J]
    (qB : B → ℕ) (qJ : J → ℕ) [∀ b, Fact (qB b).Prime] [∀ j, Fact (qJ j).Prime]
    (hβ : ((∏ b, qB b : ℕ) : ZMod 24)=17) (hθ : ((∏ j, qJ j : ℕ) : ZMod 24)=1) :
    (∃ r : ℚ_[2], r^2=((∏ b, qB b : ℕ) : ℚ_[2])) ∧
    (∃ r : ℚ_[2], r^2=((∏ j, qJ j : ℕ) : ℚ_[2])) ∧
    (∃ r : ℝ, r ≠ 0 ∧ r^2=((∏ b, qB b : ℕ) : ℝ)) ∧
    (∃ r : ℝ, r ≠ 0 ∧ r^2=((∏ j, qJ j : ℕ) : ℝ)) := by
  have hB : 0 < ((∏ b, qB b : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun b _ => (Fact.out : (qB b).Prime).pos)
  have hJ : 0 < ((∏ j, qJ j : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun j _ => (Fact.out : (qJ j).Prime).pos)
  exact ⟨actual_two_adic_square_of_mod24 _ (Or.inr hβ),
    actual_two_adic_square_of_mod24 _ (Or.inl hθ),
    ⟨Real.sqrt _,(Real.sqrt_pos.mpr hB).ne',Real.sq_sqrt hB.le⟩,
    ⟨Real.sqrt _,(Real.sqrt_pos.mpr hJ).ne',Real.sq_sqrt hJ.le⟩⟩

end ActualTwoDescentMutualPadicRoots318
