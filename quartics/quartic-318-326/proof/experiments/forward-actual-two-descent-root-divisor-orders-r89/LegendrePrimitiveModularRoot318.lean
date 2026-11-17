module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic
public section
namespace LegendrePrimitiveModularRoot318

/-- A primitive solution modulo p², when p divides the second coefficient
exactly once, constructs a modular square root of the first coefficient.
The first coefficient may also be divisible by p; p=2 is included. This
does not assume a global rational solution or a local-global principle. -/
theorem square_of_primitive_mod_square (p : ℕ) [Fact p.Prime]
    (a B x z w : ℤ) (hB : ¬(p:ℤ)∣B)
    (hcong : (p:ℤ)^2 ∣ z^2-a*x^2-((p:ℤ)*B)*w^2)
    (hprimitive : ¬((p:ℤ)∣x ∧ (p:ℤ)∣z ∧ (p:ℤ)∣w)) :
    IsSquare (a : ZMod p) := by
  obtain ⟨e,he⟩ := hcong
  have hp : p.Prime := Fact.out
  have hp0 : (p:ℤ)≠0 := by exact_mod_cast hp.ne_zero
  have hm : (z:ZMod p)^2-(a:ZMod p)*(x:ZMod p)^2=0 := by
    have hh := congrArg (fun n : ℤ => (n : ZMod p)) he
    push_cast at hh
    simpa using hh
  have hx0 : (x:ZMod p)≠0 := by
    intro hx
    have hxd : (p:ℤ)∣x := (ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp hx
    have hzprod : (z:ZMod p)*(z:ZMod p)=0 := by
      simpa only [hx,pow_two,mul_zero,sub_zero] using hm
    have hz : (z:ZMod p)=0 := (mul_eq_zero.mp hzprod).elim id id
    have hzd : (p:ℤ)∣z := (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hz
    obtain ⟨X,hX⟩ := hxd
    obtain ⟨Z,hZ⟩ := hzd
    have hc : (p:ℤ)*((p:ℤ)*(Z^2-a*X^2)-B*w^2)=(p:ℤ)*((p:ℤ)*e) := by
      rw [hX,hZ] at he
      linear_combination he
    have hc' := mul_left_cancel₀ hp0 hc
    have hh := congrArg (fun n : ℤ => (n : ZMod p)) hc'
    push_cast at hh
    have hprod : (B:ZMod p)*(w:ZMod p)^2=0 := by
      have hn : -((B:ZMod p)*(w:ZMod p)^2)=0 := by simpa using hh
      exact neg_eq_zero.mp hn
    have hB0 : (B:ZMod p)≠0 := fun h =>
      hB ((ZMod.intCast_zmod_eq_zero_iff_dvd B p).mp h)
    have hwprod : (w:ZMod p)*(w:ZMod p)=0 := by
      simpa only [pow_two] using (mul_eq_zero.mp hprod).resolve_left hB0
    have hw : (w:ZMod p)=0 := (mul_eq_zero.mp hwprod).elim id id
    exact hprimitive ⟨⟨X,hX⟩,⟨Z,hZ⟩,(ZMod.intCast_zmod_eq_zero_iff_dvd w p).mp hw⟩
  have hs : ((z:ZMod p)/(x:ZMod p))^2=(a:ZMod p) := by
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 hx0)).mpr
    exact sub_eq_zero.mp hm
  exact ⟨(z:ZMod p)/(x:ZMod p),by simpa only [pow_two] using hs.symm⟩

end LegendrePrimitiveModularRoot318
