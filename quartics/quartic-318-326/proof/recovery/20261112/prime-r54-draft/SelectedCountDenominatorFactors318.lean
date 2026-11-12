module
public import SelectedDenominatorExactOrder318
public section
noncomputable section
namespace SelectedCountDenominatorFactors318
open SelectedReductionOrder318 SelectedQuotientOrders318 SelectedEntryDenominatorDivisibility318
variable (p : ℕ) [Fact p.Prime]
/-- The upper multiple is PRODUCED by the actual cardinality theorem. -/
theorem full_count (rho : ℚ_[p]) (hr : rho^2=2) (hp : p≠2) (h7 : ¬p∣49)
    (q : ℕ) (hq : q.Prime) (hqd : q∣pointCount p rho hr)
    (hden : ¬p∣multipleDenominator (pointCount p rho hr/q)) : q∣order p rho hr := by
  have hn:=actual_order_dvd p rho hr hp h7
  have hN : 0<pointCount p rho hr := by simp [pointCount]
  exact SelectedDenominatorPrimeFactor318.prime_factor p rho hr _ q hN hq hqd hn hden
/-- Extra native eighth/fourth roots PRODUCE the smaller quarter bound,
which is often a much cheaper denominator certificate. -/
theorem quarter_count (rho : ℚ_[p]) (hr : rho^2=2) (hp : p≠2) (h7 : ¬p∣49)
    (z t : ZMod p) (hz : z^8=-1) (ht : t^4=2)
    (q : ℕ) (hq : q.Prime) (hN : 0<pointCount p rho hr/4)
    (hqd : q∣pointCount p rho hr/4)
    (hden : ¬p∣multipleDenominator ((pointCount p rho hr/4)/q)) : q∣order p rho hr :=
  SelectedDenominatorPrimeFactor318.prime_factor p rho hr _ q hN hq hqd
    (SelectedQuarterOrder318.actual_order_dvd_quarter p rho hr hp h7 z t hz ht) hden
end SelectedCountDenominatorFactors318
