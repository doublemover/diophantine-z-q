module
public import ActualTwoDescentNearTorsion318
public section
noncomputable section
namespace ActualTwoDescentOddSupportImage318
open ActualTwoDescentGoodPrimeValuations318 ActualTwoDescentNearTorsion318
open ActualTwoDescentCloseSquare318 ActualTwoDescentTorsionSquarePairs318
open ActualTwoDescentPadicValuationPairs318
set_option maxHeartbeats 16000000
variable {p : ℕ} [Fact p.Prime]

lemma actual_norm_lt_of_val_lt (x y : ℚ_[p]) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : y.valuation < x.valuation) : ‖x‖ < ‖y‖ := by
  have hratio := actual_small_ratio x y hx hy h
  rwa [norm_div,div_lt_one (norm_pos_iff.mpr hy)] at hratio

/-- Every actual non-two-torsion local point at an odd support prime has
one of the FOUR actual torsion squareclasses. The nonzero square witnesses
are constructed by Hensel near the appropriate root, not postulated from
valuation vectors or a Selmer dimension. -/
theorem actual_odd_support_image (n : ℕ) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hnval : (n : ℚ_[p]).valuation=1) (P : LocalPoint (p:=p) n) :
    TorsionPair (n : ℚ_[p]) (P.x+3*n) (P.x-n) := by
  have hn : (n : ℚ_[p]) ≠ 0 := by
    intro he
    rw [he,Padic.valuation_zero] at hnval
    norm_num at hnval
  have hy : P.y ≠ 0 := by
    intro he
    have h := P.curve
    rw [he,zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
    exact (mul_ne_zero (mul_ne_zero P.x_ne P.minus_ne) P.plus_ne) h.symm
  by_cases hfar : P.x.valuation < 1
  · exact Or.inl (actual_far_torsion hp2 n P.x P.y P.x_ne hy P.curve
      (actual_norm_lt_of_val_lt n P.x hn P.x_ne (by simpa only [hnval] using hfar)))
  by_cases hzero : 1 < P.x.valuation
  · exact Or.inr (Or.inr (Or.inr (actual_zero_torsion hp2 hp3 n P.x hn
      (actual_norm_lt_of_val_lt P.x n P.x_ne hn (by simpa only [hnval] using hzero)))))
  have hxval : P.x.valuation=1 := by omega
  by_cases hminus : 1 < (P.x-n).valuation
  · exact Or.inr (Or.inl (actual_positive_torsion hp2 n P.x P.y hn hy P.curve
      (actual_norm_lt_of_val_lt (P.x-n) n P.minus_ne hn (by simpa only [hnval] using hminus))))
  by_cases hplus : 1 < (P.x+3*n).valuation
  · exact Or.inr (Or.inr (Or.inl (actual_negative_torsion hp2 hp3 n P.x P.y hn hy P.curve
      (actual_norm_lt_of_val_lt (P.x+3*n) n P.plus_ne hn (by simpa only [hnval] using hplus)))))
  have hminuslo : 1 ≤ (P.x-n).valuation := by
    have h := Padic.le_valuation_add (x:=P.x) (y:= -(n : ℚ_[p]))
      (by simpa only [sub_eq_add_neg] using P.minus_ne)
    simpa only [←sub_eq_add_neg,actual_valuation_neg,hnval,hxval,min_self] using h
  have v3 : (3 : ℚ_[p]).valuation=0 := by
    letI : Fact (Nat.Prime 3) := ⟨by decide⟩
    rw [show (3 : ℚ_[p])=((3 : ℕ) : ℚ_[p]) from rfl,Padic.valuation_natCast,
      padicValNat_primes hp3,Int.natCast_zero]
  have hpluslo : 1 ≤ (P.x+3*n).valuation := by
    have h := Padic.le_valuation_add P.plus_ne
    rw [Padic.valuation_mul (by norm_num : (3 : ℚ_[p]) ≠ 0) hn,v3,zero_add,hnval,hxval,min_self] at h
    exact h
  have hmval : (P.x-n).valuation=1 := by omega
  have hpval : (P.x+3*n).valuation=1 := by omega
  have hcurve := congrArg Padic.valuation P.curve
  rw [Padic.valuation_pow,Padic.valuation_mul (mul_ne_zero P.x_ne P.minus_ne) P.plus_ne,
    Padic.valuation_mul P.x_ne P.minus_ne,hxval,hmval,hpval] at hcurve
  omega

end ActualTwoDescentOddSupportImage318
