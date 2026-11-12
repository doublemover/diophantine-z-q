module
public import SelectedUniformOrderGrowth318
public section
noncomputable section
namespace SelectedFixedEntrySupport318
open SelectedEntryDenominatorDivisibility318
@[expose] def support (M : ℕ) : Finset ℕ :=
  (Finset.range (multipleDenominator M+1)).filter (fun p => p.Prime ∧ p∣multipleDenominator M)
variable (p : ℕ) [Fact p.Prime]
lemma mem_support (rho : ℚ_[p]) (hr : rho^2=2) (M : ℕ) (hM : 0<M)
    (he : SelectedFormalEntry318.Entry p rho hr M) : p∈support M := by
  have hd := entry_divides p rho hr M hM he
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_dvd (positive M) hd)),
    Fact.out,hd⟩
/-- Fixed annihilator obstruction, not obstruction to that number dividing the order. -/
lemma no_fixed_entry (rho : ℚ_[p]) (hr : rho^2=2) (M : ℕ) (hM : 0<M)
    (hp : multipleDenominator M<p) : ¬SelectedFormalEntry318.Entry p rho hr M := by
  intro he
  exact (not_le_of_gt hp) (Nat.le_of_dvd (positive M) (entry_divides p rho hr M hM he))
end SelectedFixedEntrySupport318
