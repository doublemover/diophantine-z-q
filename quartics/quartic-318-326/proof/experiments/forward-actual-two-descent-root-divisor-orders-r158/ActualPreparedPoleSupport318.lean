module
public import ActualPreparedPoleLocalSquares318
public import DetectorDenominatorPreparation318
public import Mathlib.Data.Nat.Squarefree
public section
noncomputable section
namespace ActualPreparedPoleSupport318
open ActualPreparedPoleSquarefreeClasses318 ActualPreparedPoleLocalSquares318

/-- A square reduced denominator excludes every negative odd valuation.
This is a consequence of the ACTUAL denominator, not a support assumption. -/
theorem nonnegative_or_even (b : ℚ) (hden : IsSquare b.den)
    {p : ℕ} (hp : p.Prime) : 0≤padicValRat p b ∨ Even (padicValRat p b) := by
  have hd : Even (padicValNat p b.den) := by
    simpa only [Nat.factorization_def _ hp] using
      (Nat.isSquare_iff_even_factorization.mp hden p hp)
  rcases Rat.num_or_den_zero_padicVal b hp with hn|hden0
  · right
    obtain ⟨k,hk⟩ := hd
    refine ⟨-(k:ℤ),?_⟩
    simp only [padicValRat_def,hn,Nat.cast_zero,zero_sub,hk,Nat.cast_add]
    ring
  · left
    simp only [padicValRat_def,hden0,Nat.cast_zero,sub_zero]
    exact Int.natCast_nonneg _

lemma support_valuation {a p : ℕ} (ha : Squarefree a) (hp : p.Prime)
    (hpa : p∣a) : padicValNat p a=1 := by
  simpa only [Nat.factorization_def _ hp] using
    Nat.factorization_eq_one_of_squarefree ha hp hpa

/-- Outside17, a prime of beta has positive valuation in the SAME b. -/
theorem beta_support_positive {b : ℚ} (C : Classes b) (hb : b≠0)
    (hden : IsSquare b.den) {p : ℕ} [Fact p.Prime]
    (hp17 : p≠17) (hpb : p∣C.beta) : 0<padicValRat p b := by
  letI : Fact (Nat.Prime 17) := ⟨by decide⟩
  have hbeta : (C.beta:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt C.beta_pos)
  have hv := congrArg (padicValRat p) C.first_class
  rw [padicValRat.mul (by norm_num : (17:ℚ)≠0) hb,
    padicValRat.mul hbeta (pow_ne_zero 2 C.c_ne),padicValRat.pow,
    show (17:ℚ)=((17:ℕ):ℚ) from rfl,padicValRat.of_nat,
    padicValNat_primes hp17,padicValRat.of_nat,
    support_valuation C.beta_squarefree Fact.out hpb] at hv
  have hodd : ¬Even (padicValRat p b) := by
    rintro ⟨k,hk⟩
    omega
  rcases nonnegative_or_even b hden (Fact.out : p.Prime) with hn|he
  · have hz : padicValRat p b≠0 := by
      intro hz
      apply hodd
      rw [hz]
      exact ⟨0,by simp⟩
    omega
  · exact False.elim (hodd he)

/-- Every odd beta-support prime admits an ACTUAL root of theta. At17
the original preparation depth is used explicitly; all other primes use
the square-denominator consequence above. -/
theorem theta_square_at_beta_support {b : ℚ} (C : Classes b) (hb : b≠0)
    (hden : IsSquare b.den) (h17 : 2≤padicValRat 17 b)
    {p : ℕ} [Fact p.Prime] (hp2 : p≠2) (hpb : p∣C.beta) :
    ∃ r : ℚ_[p], r≠0 ∧ r^2=(C.theta:ℚ_[p]) := by
  have hbcast : (b:ℚ_[p])≠0 := Rat.cast_ne_zero.mpr hb
  have hseventeen : (17:ℚ_[p])≠0 := by norm_num
  have hval : (17:ℚ_[p]).valuation < (b:ℚ_[p]).valuation := by
    rw [show (b:ℚ_[p]).valuation=padicValRat p b from Padic.valuation_ratCast]
    by_cases hp17 : p=17
    · subst p
      rw [show (17:ℚ_[17])=((17:ℕ):ℚ_[17]) from rfl,
        Padic.valuation_natCast,padicValNat_self]
      omega
    · letI : Fact (Nat.Prime 17) := ⟨by decide⟩
      rw [show (17:ℚ_[p])=((17:ℕ):ℚ_[p]) from rfl,
        Padic.valuation_natCast,padicValNat_primes hp17]
      exact beta_support_positive C hb hden hp17 hpb
  exact theta_at_small_pole hp2 C
    (ActualTwoDescentCloseSquare318.actual_small_ratio _ _ hbcast hseventeen hval)

/-- In particular beta and theta cannot share an ODD prime. The prime2
exclusion and the mod24 residue conclusions are separate obligations. -/
theorem no_common_odd_prime {b : ℚ} (C : Classes b) (hb : b≠0)
    (hden : IsSquare b.den) (h17 : 2≤padicValRat 17 b)
    {p : ℕ} [Fact p.Prime] (hp2 : p≠2) (hpb : p∣C.beta) : ¬p∣C.theta := by
  intro hpt
  obtain ⟨r,_,hr⟩ := theta_square_at_beta_support C hb hden h17 hp2 hpb
  have hv := congrArg Padic.valuation hr
  rw [Padic.valuation_pow,Padic.valuation_natCast,
    support_valuation C.theta_squarefree Fact.out hpt] at hv
  omega

end ActualPreparedPoleSupport318
