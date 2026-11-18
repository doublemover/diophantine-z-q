module
public import ActualPreparedPoleSupport318
public section
noncomputable section
namespace ActualPreparedPoleReverseSupport318
open ActualPreparedPoleSquarefreeClasses318 ActualPreparedPoleLocalSquares318
open ActualPreparedPoleSupport318 ActualTwoDescentPadicValuationPairs318

/-- Integer content of the unit-difference alternatives: an odd second
valuation must be positive when the first is nonnegative or even. -/
lemma odd_second_positive (a v : ℤ)
    (ha : 0≤a ∨ Even a) (hv : ¬Even v)
    (hpair : (a=v ∧ a≤0) ∨ (a=0 ∧ 0≤v) ∨ (0≤a ∧ v=0)) : 0<v := by
  have hv0 : v≠0 := by
    intro he
    apply hv
    rw [he]
    exact ⟨0,by simp⟩
  rcases hpair with h|h|h
  · rcases ha with ha|ha
    · omega
    · exact False.elim (hv (h.1 ▸ ha))
  · omega
  · omega

/-- Every odd theta-support prime other than17 gives an ACTUAL beta
square, using the SAME b and reduced square denominator. No symbol or
global rational-point hypothesis is substituted for this local proof. -/
theorem beta_square_at_theta_support {b : ℚ} (C : Classes b)
    (hb : 0<b) (hsmall : b<17) (hden : IsSquare b.den)
    {p : ℕ} [Fact p.Prime] (hp2 : p≠2) (hp17 : p≠17)
    (hpt : p∣C.theta) :
    ∃ r : ℚ_[p], r≠0 ∧ r^2=(C.beta:ℚ_[p]) := by
  letI : Fact (Nat.Prime 17) := ⟨by decide⟩
  let x : ℚ_[p] := (b:ℚ_[p])/17
  let y : ℚ_[p] := x-1
  have hb0 : (b:ℚ_[p])≠0 := Rat.cast_ne_zero.mpr (ne_of_gt hb)
  have h17 : (17:ℚ_[p])≠0 := by norm_num
  have hb17 : (b:ℚ_[p])≠17 := by exact_mod_cast (ne_of_lt hsmall)
  have hx : x≠0 := div_ne_zero hb0 h17
  have hy : y≠0 := by
    intro hz
    have hx1 : x=1 := sub_eq_zero.mp hz
    have he := (div_eq_iff h17).mp hx1
    exact hb17 (by simpa only [one_mul] using he)
  have hc : 1-x= -y := by dsimp [y]; ring
  have hcomp : 1-x≠0 := by rw [hc]; exact neg_ne_zero.mpr hy
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
  rw [Padic.valuation_natCast,support_valuation C.theta_squarefree Fact.out hpt,
    hc,actual_valuation_neg] at hv
  have hyodd : ¬Even y.valuation := by
    rintro ⟨k,hk⟩
    omega
  have hxcast : x=((b/17:ℚ):ℚ_[p]) := by simp [x]
  have hxval : x.valuation=padicValRat p b := by
    rw [hxcast,Padic.valuation_ratCast,
      padicValRat.div (ne_of_gt hb) (by norm_num : (17:ℚ)≠0),
      show (17:ℚ)=((17:ℕ):ℚ) from rfl,padicValRat.of_nat,
      padicValNat_primes hp17]
    simp
  have hdiff : x-y=1 := by dsimp [y]; ring
  have vone : (1:ℚ_[p]).valuation=0 := by
    have he := Padic.valuation_ratCast (p:=p) (1:ℚ)
    norm_num at he
    exact he
  have hpair := actual_unit_difference_pair x y hx hy
    (by rw [hdiff]; exact one_ne_zero) (by rw [hdiff,vone])
  have hpos : 0<y.valuation := odd_second_positive _ _
    (by rw [hxval]; exact nonnegative_or_even b hden Fact.out) hyodd hpair
  have hnorm : ‖y‖<1 := by
    have he := ActualTwoDescentCloseSquare318.actual_small_ratio y 1 hy one_ne_zero
      (by rw [vone]; exact hpos)
    simpa only [div_one] using he
  exact beta_at_near_seventeen hp2 C hnorm

end ActualPreparedPoleReverseSupport318
