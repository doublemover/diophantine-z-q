module
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Tactic
public section
namespace LegendreCenteredRoot318

/-- A modular square root gives the centered integer and exact quotient used
in norm descent. This constructs the bound, rather than assuming it. -/
theorem centered_root (a b : ℤ) (hb : b≠0)
    (hroot : IsSquare (a : ZMod b.natAbs)) :
    ∃ t c : ℤ, t^2-a=b*c ∧ 2*|t|≤|b| := by
  letI : NeZero b.natAbs := ⟨Int.natAbs_ne_zero.mpr hb⟩
  obtain ⟨r,hr⟩ := hroot
  have hd : (b.natAbs:ℤ) ∣ r.valMinAbs^2-a := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ b.natAbs).mp
    simp only [Int.cast_sub,Int.cast_pow,ZMod.coe_valMinAbs,pow_two,←hr,sub_self]
  have hdb : b∣r.valMinAbs^2-a := by
    simpa only [Int.natCast_natAbs,abs_dvd] using hd
  obtain ⟨c,hc⟩ := hdb
  refine ⟨r.valMinAbs,c,hc,?_⟩
  have hn : 2*r.valMinAbs.natAbs≤b.natAbs := by
    have hh := r.natAbs_valMinAbs_le
    omega
  exact_mod_cast hn

end LegendreCenteredRoot318
