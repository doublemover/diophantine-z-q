module
public import SelectedEntryDenominatorDivisibility318
public section
noncomputable section
namespace SelectedUniformOrderGrowth318
open SelectedEntryDenominatorDivisibility318 SelectedQuotientOrders318
@[expose] def bound (T : ℕ) : ℕ := ∑ M ∈ Finset.Icc 1 T, multipleDenominator M
lemma term_le (T M : ℕ) (hM : 0<M) (hT : M≤T) : multipleDenominator M≤bound T := by
  apply Finset.single_le_sum (fun _ _ => Nat.zero_le _)
  exact Finset.mem_Icc.mpr ⟨hM,hT⟩
variable (p : ℕ) [Fact p.Prime]
theorem large_order (rho : ℚ_[p]) (hr : rho^2=2) (T : ℕ) (hp : bound T<p) :
    T<order p rho hr := by
  by_contra h
  have hn := order_positive p rho hr
  have hle := prime_le p rho hr (order p rho hr) hn dvd_rfl
  exact (not_le_of_gt hp) (hle.trans (term_le T _ hn (Nat.le_of_not_gt h)))
/-- Uniform in the prime and chosen embedding; no fixed-divisor coverage is inferred. -/
theorem uniform (T : ℕ) : ∃ B : ℕ, ∀ p : ℕ, ∀ hp : p.Prime,
    letI : Fact p.Prime := ⟨hp⟩
    ∀ rho : ℚ_[p], ∀ hr : rho^2=2, B<p → T<order p rho hr := by
  refine ⟨bound T,?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  exact fun rho hr h => large_order p rho hr T h
end SelectedUniformOrderGrowth318
