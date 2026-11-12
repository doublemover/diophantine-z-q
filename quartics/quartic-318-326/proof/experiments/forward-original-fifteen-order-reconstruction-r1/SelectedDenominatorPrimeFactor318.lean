module
public import NatDivisorDropCertificate318
public section
noncomputable section
namespace SelectedDenominatorPrimeFactor318
open SelectedEntryDenominatorDivisibility318 SelectedQuotientOrders318
variable (p : ℕ) [Fact p.Prime]
/-- A concrete GLOBAL denominator nondivisibility test proves an actual
order prime divisor. It excludes the smaller multiple at EVERY root, so
this sufficient certificate is deliberately not asserted complete. -/
theorem prime_factor (rho : ℚ_[p]) (hr : rho^2=2) (N q : ℕ)
    (hN : 0<N) (hq : q.Prime) (hqN : q∣N) (hn : order p rho hr∣N)
    (hden : ¬p∣multipleDenominator (N/q)) : q∣order p rho hr := by
  apply NatDivisorDropCertificate318.prime_divides (order p rho hr) N q hq hqN hn
  intro hdrop
  exact hden (order_divides p rho hr (N/q)
    (NatDivisorDropCertificate318.quotient_positive N q hN hq hqN) hdrop)
/-- No supplied no-entry statement is needed: the old global denominator
producer discharges it, with M>0 retained. -/
lemma no_entry (rho : ℚ_[p]) (hr : rho^2=2) (M : ℕ) (hM : 0<M)
    (hden : ¬p∣multipleDenominator M) : ¬SelectedFormalEntry318.Entry p rho hr M :=
  fun he => hden (entry_divides p rho hr M hM he)
end SelectedDenominatorPrimeFactor318
