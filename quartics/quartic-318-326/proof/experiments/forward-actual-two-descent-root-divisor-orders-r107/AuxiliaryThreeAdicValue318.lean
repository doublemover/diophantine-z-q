module
public import LegendrePadicPrimitiveResidues318
public import LegendreSharedPrimeResidue318
public section
namespace AuxiliaryThreeAdicValue318
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- An actual local shared-prime norm supplies the primitive residues used
by the integer ratio theorem. No integrality or chosen residue vector is
assumed. The modular square may be zero if b is a nonunit. -/
theorem shared_ratio_of_local_norm (p : ℕ) [Fact p.Prime]
    (a b : ℤ) (x z : ℚ_[p]) (ha : ¬(p:ℤ)∣a)
    (hsol : z^2-(((p:ℤ)*a:ℤ):ℚ_[p])*x^2=(((p:ℤ)*b:ℤ):ℚ_[p])) :
    IsSquare (-(b:ZMod p)/(a:ZMod p)) := by
  obtain ⟨X,Z,W,hcong,hprim⟩ := LegendrePadicPrimitiveResidues318.residues_of_local_solution
    p ((p:ℤ)*a) ((p:ℤ)*b) x z 1
    (by rintro ⟨_,_,h⟩; exact one_ne_zero h)
    (by simpa only [one_pow,mul_one,sub_eq_zero] using hsol)
  exact LegendreSharedPrimeResidue318.square_ratio_of_primitive_mod_square
    p a b X Z W ha (by simpa only [mul_assoc] using hcong) hprim

/-- The actual B-side at3 forces the selected unit value to be1 modulo3.
The nondivisibility of t is explicitly separate: it comes from the A-side
parity argument, not from this B-side equation. Primitive extraction is
after the transformation; its final denominator is not assumed to be1. -/
theorem selected_unit_mod_three (C t : ℤ)
    (hC : (C:ZMod 3)=1) (ht : ¬(3:ℤ)∣t)
    (T Y : ℚ_[3]) (hB : (C:ℚ_[3])*T^2-6*Y^2=(t:ℚ_[3])) :
    (t:ZMod 3)=1 := by
  have htwo : (2:ZMod 3)≠0 := by decide
  have ha : ¬(3:ℤ)∣2*C := by
    intro hd
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (2*C) 3).mpr hd
    have hh : (2:ZMod 3)=0 := by
      simpa only [Int.cast_mul,Int.cast_ofNat,hC,mul_one] using hz
    exact htwo hh
  have hlocal : (6*Y)^2-(((3:ℤ)*(2*C):ℤ):ℚ_[3])*T^2=
      (((3:ℤ)*(-2*t):ℤ):ℚ_[3]) := by
    push_cast
    linear_combination -6*hB
  have hs := shared_ratio_of_local_norm 3 (2*C) (-2*t) T (6*Y) ha hlocal
  have hratio : -((-2*t:ℤ):ZMod 3)/((2*C:ℤ):ZMod 3)=(t:ZMod 3) := by
    push_cast
    rw [hC]
    field_simp [htwo] <;> ring
  rw [hratio] at hs
  have ht0 : (t:ZMod 3)≠0 := fun h => ht ((ZMod.intCast_zmod_eq_zero_iff_dvd t 3).mp h)
  obtain ⟨r,hr⟩ := hs
  fin_cases r
  · exact False.elim (ht0 (hr.trans (by decide)))
  · exact hr.trans (by decide)
  · exact hr.trans (by decide)

end AuxiliaryThreeAdicValue318
