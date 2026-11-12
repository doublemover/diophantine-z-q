module
public import SelectedDenominatorPrimeFactor318
public section
noncomputable section
namespace SelectedDenominatorExactOrder318
open SelectedEntryDenominatorDivisibility318 SelectedQuotientOrders318
variable (p : ℕ) [Fact p.Prime]
/-- Testing ALL prime drops upgrades a genuine upper multiple to the
EXACT actual order. This is a finite sufficient test, not automatic
success merely because N is a curve count. -/
theorem exact_order (rho : ℚ_[p]) (hr : rho^2=2) (N : ℕ) (hN : 0<N)
    (hn : order p rho hr∣N)
    (hden : ∀ q : ℕ,q.Prime→q∣N→¬p∣multipleDenominator (N/q)) : order p rho hr=N := by
  apply SelectedExactOrderCertificates318.exact_order p rho hr N hN
    (entry_of_order_dvd p rho hr N hn)
  intro q hq hqd
  exact SelectedDenominatorPrimeFactor318.no_entry p rho hr (N/q)
    (NatDivisorDropCertificate318.quotient_positive N q hN hq hqd) (hden q hq hqd)
end SelectedDenominatorExactOrder318
