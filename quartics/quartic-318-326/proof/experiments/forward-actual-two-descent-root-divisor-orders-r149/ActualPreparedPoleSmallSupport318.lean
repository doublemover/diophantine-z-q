module
public import ActualPreparedPoleReverseSupport318
public section
noncomputable section
namespace ActualPreparedPoleSmallSupport318
open ActualPreparedPoleSquarefreeClasses318 ActualPreparedPoleSupport318
open ActualTwoDescentPadicValuationPairs318

/-- A local square b excludes the SAME beta-support prime unless it is17.
This applies at both actual small primes2 and3 without a new squareclass. -/
theorem beta_not_dvd_of_local_square {b : ℚ} (C : Classes b) (hb : b≠0)
    {p : ℕ} [Fact p.Prime] (hp17 : p≠17) (hs : IsSquare (b:ℚ_[p])) :
    ¬p∣C.beta := by
  letI : Fact (Nat.Prime 17) := ⟨by decide⟩
  intro hpb
  obtain ⟨r,hr⟩ := hs
  have hr' : (b:ℚ_[p])=r^2 := by simpa only [pow_two] using hr
  have hvb := congrArg Padic.valuation hr'
  rw [Padic.valuation_ratCast,Padic.valuation_pow] at hvb
  have hbeta : (C.beta:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt C.beta_pos)
  have hv := congrArg (padicValRat p) C.first_class
  rw [padicValRat.mul (by norm_num : (17:ℚ)≠0) hb,
    padicValRat.mul hbeta (pow_ne_zero 2 C.c_ne),padicValRat.pow,
    show (17:ℚ)=((17:ℕ):ℚ) from rfl,padicValRat.of_nat,
    padicValNat_primes hp17,padicValRat.of_nat,
    support_valuation C.beta_squarefree Fact.out hpb] at hv
  omega

/-- Whenever b/17 has positive valuation, its complement is a unit and
the literal second class has even valuation. Thus theta cannot contain p,
including p=2 or17; this conclusion does not use odd-prime Hensel. -/
theorem theta_not_dvd_of_depth {b : ℚ} (C : Classes b) (hb : 0<b)
    (hsmall : b<17) {p : ℕ} [Fact p.Prime]
    (hdepth : padicValRat p (17:ℚ)<padicValRat p b) : ¬p∣C.theta := by
  let x : ℚ_[p] := (b:ℚ_[p])/17
  have hb0 : (b:ℚ_[p])≠0 := Rat.cast_ne_zero.mpr (ne_of_gt hb)
  have h17 : (17:ℚ_[p])≠0 := by norm_num
  have hx : x≠0 := div_ne_zero hb0 h17
  have hb17 : (b:ℚ_[p])≠17 := by exact_mod_cast (ne_of_lt hsmall)
  have hcomp : 1-x≠0 := by
    intro he
    have hx1 : x=1 := (sub_eq_zero.mp he).symm
    have hh := (div_eq_iff h17).mp hx1
    exact hb17 (by simpa only [one_mul] using hh)
  have hxcast : x=((b/17:ℚ):ℚ_[p]) := by simp [x]
  have vx : 0<x.valuation := by
    rw [hxcast,Padic.valuation_ratCast,
      padicValRat.div (ne_of_gt hb) (by norm_num : (17:ℚ)≠0)]
    omega
  have vone : (1:ℚ_[p]).valuation=0 := by
    have he := Padic.valuation_ratCast (p:=p) (1:ℚ)
    norm_num at he
    exact he
  have vc : (1-x).valuation=0 := by
    have he := actual_valuation_add_min (1:ℚ_[p]) (-x) one_ne_zero
      (neg_ne_zero.mpr hx) (by simpa only [sub_eq_add_neg] using hcomp)
      (by rw [actual_valuation_neg,vone]; omega)
    simpa only [←sub_eq_add_neg,actual_valuation_neg,vone,min_eq_left vx.le] using he
  intro hpt
  have hB : (17:ℚ_[p])*(b:ℚ_[p])≠0 := mul_ne_zero h17 hb0
  have ht : (C.theta:ℚ_[p])≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt C.theta_pos)
  have hd : (C.d:ℚ_[p])≠0 := Rat.cast_ne_zero.mpr C.d_ne
  have hf : ((17:ℚ_[p])*(b:ℚ_[p]))^2*(1-x)=
      (C.theta:ℚ_[p])*(C.d:ℚ_[p])^2 := by
    dsimp [x]
    exact_mod_cast C.second_class
  have hv := congrArg Padic.valuation hf
  rw [Padic.valuation_mul (pow_ne_zero 2 hB) hcomp,
    Padic.valuation_mul ht (pow_ne_zero 2 hd)] at hv
  simp only [Padic.valuation_pow] at hv
  rw [vc,Padic.valuation_natCast,support_valuation C.theta_squarefree Fact.out hpt] at hv
  omega

/-- The actual preparation at17 removes the only exceptional prime from
the reverse odd-support root theorem. -/
theorem beta_square_at_theta_support {b : ℚ} (C : Classes b)
    (hb : 0<b) (hsmall : b<17) (hden : IsSquare b.den)
    (h17 : 2≤padicValRat 17 b) {p : ℕ} [Fact p.Prime]
    (hp2 : p≠2) (hpt : p∣C.theta) :
    ∃ r : ℚ_[p], r≠0 ∧ r^2=(C.beta:ℚ_[p]) := by
  have hp17 : p≠17 := by
    intro he
    subst p
    apply theta_not_dvd_of_depth C hb hsmall (p:=17) _ hpt
    rw [show (17:ℚ)=((17:ℕ):ℚ) from rfl,padicValRat.self (by norm_num)]
    omega
  exact ActualPreparedPoleReverseSupport318.beta_square_at_theta_support
    C hb hsmall hden hp2 hp17 hpt

end ActualPreparedPoleSmallSupport318
