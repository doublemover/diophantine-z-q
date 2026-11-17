module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic
public section
namespace LegendreSharedPrimeResidue318

/-- When both binary coefficients have a displayed p-factor, with the first
residual coefficient a unit, primitive p-squared data construct the ratio
root needed at a shared prime.
Only the first residual coefficient must be a unit; the root may be zero if
the second is not. Applications to a Jacobi value1 must separately use its
nonvanishing, rather than silently treating IsSquare as a nonzero square. -/
theorem square_ratio_of_primitive_mod_square (p : ℕ) [Fact p.Prime]
    (a b x z w : ℤ) (ha : ¬(p:ℤ)∣a)
    (hcong : (p:ℤ)^2 ∣ z^2-(p:ℤ)*a*x^2-(p:ℤ)*b*w^2)
    (hprim : ¬((p:ℤ)∣x ∧ (p:ℤ)∣z ∧ (p:ℤ)∣w)) :
    IsSquare (-(b:ZMod p)/(a:ZMod p)) := by
  obtain ⟨e,he⟩ := hcong
  have hp : p.Prime := Fact.out
  have hp0 : (p:ℤ)≠0 := by exact_mod_cast hp.ne_zero
  have hzprod : (z:ZMod p)*(z:ZMod p)=0 := by
    have hh := congrArg (fun n : ℤ => (n:ZMod p)) he
    push_cast at hh
    simpa [pow_two] using hh
  have hz0 : (z:ZMod p)=0 := (mul_eq_zero.mp hzprod).elim id id
  have hzd : (p:ℤ)∣z := (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hz0
  obtain ⟨Z,hZ⟩ := hzd
  have hc : (p:ℤ)*((p:ℤ)*Z^2-a*x^2-b*w^2)=(p:ℤ)*((p:ℤ)*e) := by
    rw [hZ] at he
    linear_combination he
  have hc' := mul_left_cancel₀ hp0 hc
  have hrel : (a:ZMod p)*(x:ZMod p)^2+(b:ZMod p)*(w:ZMod p)^2=0 := by
    have hh := congrArg (fun n : ℤ => (n:ZMod p)) hc'
    push_cast at hh
    have hh' : -((a:ZMod p)*(x:ZMod p)^2)-(b:ZMod p)*(w:ZMod p)^2=0 := by
      simpa using hh
    linear_combination -hh'
  have ha0 : (a:ZMod p)≠0 := fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)
  have hw0 : (w:ZMod p)≠0 := by
    intro hw
    have hxp : (a:ZMod p)*(x:ZMod p)^2=0 := by simpa [hw] using hrel
    have hxprod : (x:ZMod p)*(x:ZMod p)=0 := by
      simpa only [pow_two] using (mul_eq_zero.mp hxp).resolve_left ha0
    have hx0 : (x:ZMod p)=0 := (mul_eq_zero.mp hxprod).elim id id
    exact hprim ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp hx0,
      ⟨Z,hZ⟩,(ZMod.intCast_zmod_eq_zero_iff_dvd w p).mp hw⟩
  have hs : ((x:ZMod p)/(w:ZMod p))^2= -(b:ZMod p)/(a:ZMod p) := by
    field_simp [ha0,hw0]
    <;> linear_combination hrel
  exact ⟨(x:ZMod p)/(w:ZMod p),by simpa only [pow_two] using hs.symm⟩

end LegendreSharedPrimeResidue318
