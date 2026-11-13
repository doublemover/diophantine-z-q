module
public import SelectedOriginalGeneratorNonzero318
public section
noncomputable section
namespace SelectedExactOrderCertificates318
open SelectedQuotientOrders318 SelectedExactEntryOrders318
variable (p : ℕ) [Fact p.Prime]
theorem exact_order (rho : ℚ_[p]) (hr : rho^2=2) (N : ℕ) (hN : 0<N)
    (hkill : SelectedFormalEntry318.Entry p rho hr N)
    (hdrop : ∀ q : ℕ, q.Prime → q∣N → ¬SelectedFormalEntry318.Entry p rho hr (N/q)) :
    order p rho hr=N := by
  apply addOrderOf_eq_of_nsmul_and_div_prime_nsmul hN
    ((multiple_zero_iff p rho hr N).mpr hkill)
  intro q hq hqN hz
  exact hdrop q hq hqN ((multiple_zero_iff p rho hr (N/q)).mp hz)
lemma prime_upper (rho : ℚ_[p]) (hr : rho^2=2) (q : ℕ) (hq : q.Prime)
    (hd : order p rho hr∣q) : order p rho hr=q := by
  rcases (Nat.dvd_prime hq).mp hd with h|h
  · exact ((ne_of_gt (SelectedOriginalGeneratorNonzero318.order_gt_one p rho hr)) h).elim
  · exact h
end SelectedExactOrderCertificates318
