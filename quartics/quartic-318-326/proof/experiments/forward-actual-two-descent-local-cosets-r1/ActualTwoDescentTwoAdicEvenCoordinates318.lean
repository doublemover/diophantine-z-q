module
public import ActualTwoDescentTwoAdicOneObstruction318
public section
noncomputable section
namespace ActualTwoDescentTwoAdicEvenCoordinates318
open ActualTwoDescentGoodPrimeValuations318 ActualTwoDescentLocalValuationTools318
open ActualTwoDescentPadicValuationPairs318 ActualTwoDescentTwoAdicUnits318
open ActualTwoDescentTwoAdicOneObstruction318
set_option maxHeartbeats 16000000

/-- Both original Kummer coordinates of EVERY actual Q_2 point have even
valuation when n=3mod4. The sole valuation1 exception is excluded by the
actual modulo8 cubic obstruction proved in the predecessor. -/
theorem actual_two_even_coordinates (n : ℕ) (hn : n%4=3) (P : LocalPoint (p:=2) n) :
    Even (P.x-n).valuation ∧ Even (P.x+3*n).valuation := by
  have hn2 : ¬2 ∣ n := by
    intro hd
    have h := Nat.mod_eq_zero_of_dvd hd
    omega
  have hn0 : n ≠ 0 := by intro he; apply hn2; rw [he]; exact dvd_zero _
  have hnc : (n : ℚ_[2]) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have vn : (n : ℚ_[2]).valuation=0 := actual_prime_unit_valuation n hn2
  have h3n : 3*(n : ℚ_[2]) ≠ 0 := mul_ne_zero (by norm_num) hnc
  have h4n : 4*(n : ℚ_[2]) ≠ 0 := mul_ne_zero (by norm_num) hnc
  have v3 : (3 : ℚ_[2]).valuation=0 := actual_prime_unit_valuation 3 (by decide)
  have v3n : (3*(n : ℚ_[2])).valuation=0 := by
    rw [Padic.valuation_mul (by norm_num) hnc,v3,vn,add_zero]
  have v4n : (4*(n : ℚ_[2])).valuation=2 := by
    rw [Padic.valuation_mul (by norm_num) hnc,vn,add_zero,
      show (4 : ℚ_[2])=(2 : ℚ_[2])^2 by norm_num,Padic.valuation_pow,Padic.valuation_p]
    norm_num
  have hcurve := congrArg Padic.valuation P.curve
  rw [Padic.valuation_pow,Padic.valuation_mul (mul_ne_zero P.x_ne P.minus_ne) P.plus_ne,
    Padic.valuation_mul P.x_ne P.minus_ne] at hcurve
  have hBmin (hx : P.x.valuation ≠ 0) : (P.x-n).valuation=min P.x.valuation 0 := by
    have h := actual_valuation_add_min P.x (-(n : ℚ_[2])) P.x_ne (neg_ne_zero.mpr hnc)
      (by simpa only [sub_eq_add_neg] using P.minus_ne)
      (by simpa only [actual_valuation_neg,vn] using hx)
    simpa only [←sub_eq_add_neg,actual_valuation_neg,vn] using h
  have hAmin (hx : P.x.valuation ≠ 0) : (P.x+3*n).valuation=min P.x.valuation 0 := by
    simpa only [v3n] using actual_valuation_add_min P.x (3*n) P.x_ne h3n P.plus_ne
      (by simpa only [v3n] using hx)
  by_cases hxneg : P.x.valuation < 0
  · have hB : (P.x-n).valuation=P.x.valuation := by
      simpa only [min_eq_left hxneg.le] using hBmin hxneg.ne
    have hA : (P.x+3*n).valuation=P.x.valuation := by
      simpa only [min_eq_left hxneg.le] using hAmin hxneg.ne
    rw [hB,hA] at hcurve ⊢
    have he : Even P.x.valuation := ⟨P.x.valuation/2,by omega⟩
    exact ⟨he,he⟩
  by_cases hxpos : 0 < P.x.valuation
  · have hB : (P.x-n).valuation=0 := by
      simpa only [min_eq_right hxpos.le] using hBmin hxpos.ne'
    have hA : (P.x+3*n).valuation=0 := by
      simpa only [min_eq_right hxpos.le] using hAmin hxpos.ne'
    rw [hB,hA]
    exact ⟨even_zero,even_zero⟩
  have hx : P.x.valuation=0 := by omega
  have hBpos := actual_two_unit_difference_positive P.x n P.x_ne hnc P.minus_ne hx vn
  have heA : P.x+3*n=(P.x-n)+4*n := by ring
  have hnear (hB : (P.x-n).valuation ≠ 2) :
      (P.x+3*n).valuation=min (P.x-n).valuation 2 := by
    have h := actual_valuation_add_min (P.x-n) (4*n) P.minus_ne h4n
      (by rw [←heA]; exact P.plus_ne) (by simpa only [v4n] using hB)
    simpa only [←heA,v4n] using h
  by_cases hBlt : (P.x-n).valuation < 2
  · have hB : (P.x-n).valuation=1 := by omega
    have hA : (P.x+3*n).valuation=1 := by
      have h := hnear (by omega)
      norm_num only [hB,show min (1 : ℤ) 2=1 from rfl] at h
      exact h
    exact False.elim (actual_two_valuation_one_impossible n hn P hx hB hA)
  by_cases hB : (P.x-n).valuation=2
  · rw [hx,hB] at hcurve
    refine ⟨?_,⟨(P.x+3*n).valuation/2,by omega⟩⟩
    rw [hB]
    exact ⟨1,rfl⟩
  · have hA : (P.x+3*n).valuation=2 := by
      simpa only [min_eq_right (by omega : 2 ≤ (P.x-n).valuation)] using hnear hB
    rw [hx,hA] at hcurve
    refine ⟨⟨(P.x-n).valuation/2,by omega⟩,?_⟩
    rw [hA]
    exact ⟨1,rfl⟩

end ActualTwoDescentTwoAdicEvenCoordinates318
