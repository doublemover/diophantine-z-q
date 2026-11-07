module
public import LucasCongruence318
public section
namespace BetaCongruence318
variable (p:ℕ) [Fact p.Prime]
set_option maxHeartbeats 0

/-- An integral denominator cannot destroy a rational numerator's certified
p-adic depth. The zero rational is included. -/
theorem rational_numerator_dvd (q:ℚ) (k:ℕ)
    (h:((k:ℤ):WithTop ℤ)≤Padic.addValuation (q:ℚ_[p])) : (p:ℤ)^k∣q.num := by
  apply LucasCongruence318.integer_depth_dvd p q.num k
  have he:(q.num:ℚ_[p])=(q:ℚ_[p])*(q.den:ℚ_[p]) := by
    exact_mod_cast (Rat.mul_den_eq_num q).symm
  have hd:(0:WithTop ℤ)≤Padic.addValuation (q.den:ℚ_[p]) := by
    simpa only [Int.cast_natCast] using LucasCongruence318.int_integral p (q.den:ℤ)
  rw [he,Padic.addValuation.map_mul]
  exact h.trans (le_add_of_nonneg_right hd)

/-- The two literal depth-four tests transfer to beta minus the coherent
integer label; no integrality assumption on the intermediary is needed. -/
theorem beta_depth (L:ℚ_[p]) (beta:ℚ) (N:ℤ)
    (hbeta:(4:WithTop ℤ)≤Padic.addValuation (L-(beta:ℚ_[p])))
    (hN:(4:WithTop ℤ)≤Padic.addValuation (L-(N:ℚ_[p]))) :
    (4:WithTop ℤ)≤Padic.addValuation ((beta-(N:ℚ):ℚ):ℚ_[p]) := by
  have hh:=Padic.addValuation.map_le_sub hN hbeta
  have he:(L-(N:ℚ_[p]))-(L-(beta:ℚ_[p]))=((beta-(N:ℚ):ℚ):ℚ_[p]) := by
    push_cast
    ring
  rwa [he] at hh

theorem beta_numerator_dvd (L:ℚ_[p]) (beta:ℚ) (N:ℤ)
    (hbeta:(4:WithTop ℤ)≤Padic.addValuation (L-(beta:ℚ_[p])))
    (hN:(4:WithTop ℤ)≤Padic.addValuation (L-(N:ℚ_[p]))) :
    (p:ℤ)^4∣(beta-(N:ℚ)).num :=
  rational_numerator_dvd p _ 4 (beta_depth p L beta N hbeta hN)

end BetaCongruence318
#print axioms BetaCongruence318.rational_numerator_dvd
#print axioms BetaCongruence318.beta_numerator_dvd
