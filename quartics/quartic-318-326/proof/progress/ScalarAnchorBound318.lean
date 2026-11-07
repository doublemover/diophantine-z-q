module
public import SemilocalAnchor318
public import HeightSeparation318
public section
namespace ScalarAnchorBound318
set_option maxRecDepth 100000

/-- The final literal coefficient is S=3^(2^16), not a historical larger anchor. -/
theorem fixed_anchor_three_value : padicValRat 3 ((3:ℚ)^65536)=65536 := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [padicValRat.pow]
  have hv : padicValRat 3 (3:ℚ)=1 := padicValRat.self (by norm_num)
  rw [hv]
  norm_num

/-- The remaining elliptic norm valuation converts the now-proved conic
integrality into exact index divisibility and the final binary lower bound. -/
theorem index_bound (c : ℤ) (nR : ℚ) (hc : c≠0) (heven : Even c) (hnR : nR≠0)
    (hval : padicValRat 3 nR=2+2*(padicValInt 3 c:ℤ))
    (hanchor : 0≤padicValRat 3 (nR/(3:ℚ)^65536)) :
    (2*3^32767:ℤ)∣c ∧ (2:ℝ)^49151<(c.natAbs:ℝ) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hS : ((3:ℚ)^65536)≠0 := by positivity
  rw [padicValRat.div hnR hS, fixed_anchor_three_value,hval] at hanchor
  have hv : 32767≤padicValInt 3 c := by omega
  have hdiv : (3:ℤ)^32767∣c := (padicValInt_dvd_iff 32767 c).mpr (Or.inr hv)
  have hfull : (2*3^32767:ℤ)∣c := by
    obtain ⟨d,hd⟩ := hdiv
    have hod : Odd ((3:ℤ)^32767) := (show Odd (3:ℤ) by norm_num).pow
    have he : Even d := by
      rw [hd] at heven
      exact (Int.even_mul.mp heven).resolve_left (Int.not_even_iff_odd.mpr hod)
    obtain ⟨j,hj⟩ := he
    refine ⟨j,?_⟩
    rw [hd,hj]
    ring
  refine ⟨hfull,?_⟩
  have hn := Int.natAbs_le_of_dvd_ne_zero hfull hc
  have hnat : 2*3^32767≤c.natAbs := by
    simpa only [Int.natAbs_mul,Int.natAbs_pow,
      show Int.natAbs (2:ℤ)=2 by decide,show Int.natAbs (3:ℤ)=3 by decide] using hn
  have hreal : (2:ℝ)*3^32767≤(c.natAbs:ℝ) := by exact_mod_cast hnat
  exact HeightSeparation318.anchor_binary_bound _ hreal

theorem fixed_anchor_two_value : padicValRat 2 ((3:ℚ)^65536)=0 := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [padicValRat.pow]
  have hv : padicValRat 2 (3:ℚ)=0 := by
    calc
      padicValRat 2 (3:ℚ)=(padicValInt 2 (3:ℤ):ℤ) := padicValRat.of_int
      _ = 0 := by
        have hz : padicValInt 2 (3:ℤ)=0 :=
          padicValInt.eq_zero_of_not_dvd (by norm_num)
        exact_mod_cast hz
  rw [hv,mul_zero]

/-- Automatic 2-integrality of the scalar summand from the exact local
elliptic norm formula, with no real positivity assumption. -/
theorem scalar_summand_two_integral (c : ℤ) (nR : ℚ) (hnR : nR≠0)
    (hval : padicValRat 2 nR=3+2*(padicValInt 2 c:ℤ)) :
    0≤padicValRat 2 (nR/(3:ℚ)^65536) := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [padicValRat.div hnR (by positivity),fixed_anchor_two_value,hval]
  omega

end ScalarAnchorBound318
