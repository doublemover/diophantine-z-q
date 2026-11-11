module
public import ActualTwoDescentUnitDifferenceParity318
public section
noncomputable section
namespace ActualTwoDescentGoodPrimeValuations318
open ActualTwoDescentPadicValuationPairs318 ActualTwoDescentUnitDifferenceParity318
set_option maxHeartbeats 16000000
variable {p : ℕ} [Fact p.Prime]

/-- An actual non-two-torsion point of the original twist over Q_p. The
coordinates, cubic equation and nonzero factors are all retained literally. -/
structure LocalPoint (n : ℕ) where
  x : ℚ_[p]
  y : ℚ_[p]
  x_ne : x ≠ 0
  minus_ne : x-n ≠ 0
  plus_ne : x+3*n ≠ 0
  curve : y^2=x*(x-n)*(x+3*n)

/-- At an odd good prime, all three original coordinate factors have
actual even p-adic valuation. This proves the unramified NECESSARY local
condition without assuming a local-image description. -/
theorem actual_good_prime_valuations (n : ℕ) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hn : ¬p ∣ n) (P : LocalPoint (p:=p) n) :
    Even P.x.valuation ∧ Even (P.x-n).valuation ∧ Even (P.x+3*n).valuation := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hn0 : n ≠ 0 := by intro he; apply hn; rw [he]; exact dvd_zero _
  have hnc : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have vn : (n : ℚ_[p]).valuation=0 := by
    rw [Padic.valuation_natCast,padicValNat.eq_zero_of_not_dvd hn,Int.natCast_zero]
  have v3 : (3 : ℚ_[p]).valuation=0 := by
    rw [show (3 : ℚ_[p])=((3 : ℕ) : ℚ_[p]) from rfl,Padic.valuation_natCast,
      padicValNat_primes hp3,Int.natCast_zero]
  have v4 : (4 : ℚ_[p]).valuation=0 := by
    rw [show (4 : ℚ_[p])=(2 : ℚ_[p])^2 by norm_num,Padic.valuation_pow]
    have v2 : (2 : ℚ_[p]).valuation=0 := by
      rw [show (2 : ℚ_[p])=((2 : ℕ) : ℚ_[p]) from rfl,Padic.valuation_natCast,
        padicValNat_primes hp2,Int.natCast_zero]
    rw [v2,mul_zero]
  have h1 : P.x-(P.x-n)=(n : ℚ_[p]) := by ring
  have h2 : P.x-(P.x+3*n)= -(3*(n : ℚ_[p])) := by ring
  have h3 : (P.x-n)-(P.x+3*n)= -(4*(n : ℚ_[p])) := by ring
  apply actual_square_cubic_even P.x (P.x-n) (P.x+3*n) P.y
    P.x_ne P.minus_ne P.plus_ne _ _ _ _ _ _ P.curve
  · rw [h1]; exact hnc
  · rw [h2]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) hnc)
  · rw [h3]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) hnc)
  · rw [h1,vn]
  · rw [h2,actual_valuation_neg,Padic.valuation_mul (by norm_num) hnc,v3,vn,add_zero]
  · rw [h3,actual_valuation_neg,Padic.valuation_mul (by norm_num) hnc,v4,vn,add_zero]

end ActualTwoDescentGoodPrimeValuations318
