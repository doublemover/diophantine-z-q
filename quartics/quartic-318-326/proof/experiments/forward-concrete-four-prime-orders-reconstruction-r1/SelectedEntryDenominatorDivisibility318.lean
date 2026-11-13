module
public import SelectedIntegralPointNonformal318
public section
noncomputable section
namespace SelectedEntryDenominatorDivisibility318
open GlobalGeneratorPoints318 (R)
@[expose] def multipleDenominator (M : ℕ) : ℕ :=
  SelectedIntegralPointNonformal318.pointDenominator ((M:ℤ) • R)
lemma positive (M : ℕ) : 0<multipleDenominator M :=
  SelectedIntegralPointNonformal318.positive _
variable (p : ℕ) [Fact p.Prime]
/-- Necessary, not sufficient: formal entry forces a global denominator divisor. -/
theorem entry_divides (rho : ℚ_[p]) (hr : rho^2=2) (M : ℕ) (hM : 0<M)
    (he : SelectedFormalEntry318.Entry p rho hr M) : p∣multipleDenominator M := by
  by_contra hd
  exact SelectedIntegralPointNonformal318.not_formal p rho hr ((M:ℤ) • R)
    (GlobalReductionCounts318.R_infinite_order _ (by exact_mod_cast Nat.ne_of_gt hM)) hd he
lemma order_divides (rho : ℚ_[p]) (hr : rho^2=2) (M : ℕ) (hM : 0<M)
    (ho : SelectedQuotientOrders318.order p rho hr∣M) : p∣multipleDenominator M :=
  entry_divides p rho hr M hM (SelectedQuotientOrders318.entry_of_order_dvd p rho hr M ho)
lemma prime_le (rho : ℚ_[p]) (hr : rho^2=2) (M : ℕ) (hM : 0<M)
    (ho : SelectedQuotientOrders318.order p rho hr∣M) : p≤multipleDenominator M :=
  Nat.le_of_dvd (positive M) (order_divides p rho hr M hM ho)
end SelectedEntryDenominatorDivisibility318
