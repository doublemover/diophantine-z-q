module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic
public section
namespace SqrtTwoInertPrime318

/-- At an inert prime, divisibility of the integral norm forces divisibility
of both coordinates. The nonsquare condition is exact; it is not an assumed
local-global existence principle. -/
theorem coordinates_divisible (p : ℕ) [Fact p.Prime]
    (hns : ¬ IsSquare (2 : ZMod p)) (x z : ℤ)
    (h : (p:ℤ) ∣ x^2-2*z^2) : (p:ℤ) ∣ x ∧ (p:ℤ) ∣ z := by
  have hm : (x:ZMod p)^2-2*(z:ZMod p)^2=0 := by
    have he := (ZMod.intCast_zmod_eq_zero_iff_dvd (x^2-2*z^2) p).mpr h
    push_cast at he
    exact he
  by_cases hz : (z:ZMod p)=0
  · have hxprod : (x:ZMod p)*(x:ZMod p)=0 := by
      simpa only [hz, pow_two, mul_zero, sub_zero] using hm
    have hx : (x:ZMod p)=0 := (mul_eq_zero.mp hxprod).elim id id
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp hx,
      (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hz⟩
  · have he : ((x:ZMod p)/(z:ZMod p))^2=2 := by
      rw [div_pow]
      apply (div_eq_iff (pow_ne_zero 2 hz)).2
      exact sub_eq_zero.mp hm
    exact (hns ⟨(x:ZMod p)/(z:ZMod p), by simpa only [pow_two] using he.symm⟩).elim

/-- The same exact descent produces a second prime factor in every norm
once one inert-prime factor occurs. Iterating this is the norm criterion's
necessary even-valuation direction, not its sufficiency direction. -/
theorem square_divides_norm (p : ℕ) [Fact p.Prime]
    (hns : ¬ IsSquare (2 : ZMod p)) (x z : ℤ)
    (h : (p:ℤ) ∣ x^2-2*z^2) : (p:ℤ)^2 ∣ x^2-2*z^2 := by
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := coordinates_divisible p hns x z h
  rw [ha,hb]
  exact ⟨a^2-2*b^2, by ring⟩

end SqrtTwoInertPrime318
