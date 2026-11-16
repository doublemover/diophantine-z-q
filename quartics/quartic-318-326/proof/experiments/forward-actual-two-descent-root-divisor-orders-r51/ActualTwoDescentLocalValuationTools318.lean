module
public import ActualTwoDescentSameSupportLocalPoints318
public import Mathlib.NumberTheory.Padics.RingHoms
public section
noncomputable section
namespace ActualTwoDescentLocalValuationTools318
set_option maxHeartbeats 16000000
variable {p : ℕ} [Fact p.Prime]

lemma actual_valuation_div (x y : ℚ_[p]) (hx : x ≠ 0) (hy : y ≠ 0) :
    (x/y).valuation=x.valuation-y.valuation := by
  rw [div_eq_mul_inv,Padic.valuation_mul hx (inv_ne_zero hy),Padic.valuation_inv,sub_eq_add_neg]

lemma actual_norm_one_of_valuation_zero (x : ℚ_[p]) (hx : x ≠ 0) (h : x.valuation=0) :
    ‖x‖=1 := by rw [Padic.norm_eq_zpow_neg_valuation hx,h,neg_zero,zpow_zero]

lemma actual_valuation_pos_of_norm_lt_one (x : ℚ_[p]) (hx : x ≠ 0) (h : ‖x‖ < 1) :
    0 < x.valuation := by
  rw [Padic.norm_eq_zpow_neg_valuation hx,←zpow_zero (p : ℝ)] at h
  have he := (zpow_lt_zpow_iff_right₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)).mp h
  omega

lemma actual_prime_unit_valuation (n : ℕ) (hn : ¬p ∣ n) : (n : ℚ_[p]).valuation=0 := by
  rw [Padic.valuation_natCast,padicValNat.eq_zero_of_not_dvd hn,Int.natCast_zero]

end ActualTwoDescentLocalValuationTools318
