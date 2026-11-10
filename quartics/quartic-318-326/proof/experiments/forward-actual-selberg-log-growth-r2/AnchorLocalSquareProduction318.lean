module
public import PreparedAnchorLabels318
public section
noncomputable section
namespace AnchorLocalSquareProduction318
open ScalarLocalSquares318
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

lemma denominator_unit (p : ℕ) [Fact p.Prime] (r : ℚ)
    (hr : 0≤padicValRat p r) : ¬p∣r.den := by
  have hden : padicValNat p r.den=0 := by
    have hh := Rat.num_or_den_zero_padicVal r (Fact.out : p.Prime)
    rw [padicValRat_def] at hr
    omega
  rcases padicValNat.eq_zero_iff.mp hden with hp|hz|hu
  · exact False.elim ((Fact.out : p.Prime).ne_one hp)
  · exact False.elim (r.den_ne_zero hz)
  · exact hu

lemma unit_two_num_odd (r : ℚ) (hr : r≠0) (hv : padicValRat 2 r=0) : Odd r.num := by
  have hnum : padicValInt 2 r.num=0 := by
    have hh := Rat.num_or_den_zero_padicVal r (by decide : Nat.Prime 2)
    rw [padicValRat_def] at hv
    omega
  have hn : ¬(2:ℤ)∣r.num := by
    rcases padicValInt.eq_zero_iff.mp hnum with hp|hz|hu
    · norm_num at hp
    · exact False.elim ((Rat.num_ne_zero.mpr hr) hz)
    · exact hu
  rw [Int.dvd_iff_emod_eq_zero] at hn
  exact Int.odd_iff.mpr (by omega)

lemma odd_square_mod_eight (z : ℤ) (hz : Odd z) : z^2%8=1 := by
  have hz2 := Int.odd_iff.mp hz
  have hlo := Int.emod_nonneg z (by norm_num : (8:ℤ)≠0)
  have hhi := Int.emod_lt_of_pos z (by norm_num : (0:ℤ)<8)
  have hm : (z%8)%2=1 := by omega
  rw [show z^2%8=(z%8)^2%8 by simp [pow_two,Int.mul_emod]]
  interval_cases h : z%8 <;> norm_num at * <;> omega

/-- Clearing only the actual reduced denominator transports a Hensel square
back to the exact rational radicand, without replacing the ratio. -/
lemma rational_radicand_square (p : ℕ) [Fact p.Prime] (r : ℚ)
    (hs : IsSquare ((3*r.num^2-2*(r.den:ℤ)^2:ℤ):ℤ_[p])) :
    IsSquare ((3*r^2-2:ℚ):ℚ_[p]) := by
  have he : 3*r^2-2=((3*r.num^2-2*(r.den:ℤ)^2:ℤ):ℚ)/(r.den:ℚ)^2 := by
    have hd : (r.den:ℚ)≠0 := by exact_mod_cast r.den_ne_zero
    calc
      3*r^2-2 = 3*((r.num:ℚ)/(r.den:ℚ))^2-2 := by rw [Rat.num_div_den]
      _ = _ := by push_cast; field_simp [hd] <;> ring
  have hs' := rational_square_of_integral p (3*r.num^2-2*(r.den:ℤ)^2) hs
  change IsSquare ((Rat.castHom ℚ_[p]) (3*r^2-2))
  rw [he,map_div₀,map_pow]
  exact hs'.div ⟨((Rat.castHom ℚ_[p]) (r.den:ℚ)),by ring⟩

/-- The actual unit case at2: both reduced numerator and denominator are
odd, so the radicand is1mod8 and the derivative-sensitive Hensel test applies. -/
theorem at_two (r : ℚ) (hr : r≠0) (hv : padicValRat 2 r=0) :
    IsSquare ((3*r^2-2:ℚ):ℚ_[2]) := by
  have hn := unit_two_num_odd r hr hv
  have hdN := denominator_unit 2 r (by omega)
  have hdZ : ¬(2:ℤ)∣(r.den:ℤ) := by exact_mod_cast hdN
  rw [Int.dvd_iff_emod_eq_zero] at hdZ
  have hd : Odd (r.den:ℤ) := Int.odd_iff.mpr (by omega)
  have hm : (3*r.num^2-2*(r.den:ℤ)^2-1)%8=0 := by
    simp only [Int.sub_emod,Int.mul_emod,odd_square_mod_eight _ hn,
      odd_square_mod_eight _ hd]
    norm_num
  obtain ⟨k,hk⟩ := Int.dvd_iff_emod_eq_zero.mpr hm
  have he : 3*r.num^2-2*(r.den:ℤ)^2=1+8*k := by omega
  apply rational_radicand_square
  rw [he]
  exact square_two_shape k

/-- At3 every integral ratio works. Hensel is centered at the actual reduced
unit denominator, not at an unjustified chosen square root. -/
theorem at_three (r : ℚ) (hv : 0≤padicValRat 3 r) :
    IsSquare ((3*r^2-2:ℚ):ℚ_[3]) := by
  have hdN := denominator_unit 3 r hv
  have hcop : Nat.Coprime 3 r.den := (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr hdN
  have hden : ‖(r.den:ℤ_[3])‖=1 := PadicInt.norm_natCast_eq_one_iff.mpr hcop
  have htwo : ‖(2:ℤ_[3])‖=1 := PadicInt.norm_natCast_eq_one_iff.mpr (by decide)
  apply rational_radicand_square
  apply square_of_near_square 3 (r.den:ℤ_[3])
  have he : (r.den:ℤ_[3])^2-((3*r.num^2-2*(r.den:ℤ)^2:ℤ):ℤ_[3])=
      (3:ℤ_[3])*((r.den:ℤ_[3])^2-(r.num:ℤ_[3])^2) := by
    push_cast
    ring
  have hb := PadicInt.norm_le_one ((r.den:ℤ_[3])^2-(r.num:ℤ_[3])^2)
  rw [he,norm_mul,PadicInt.norm_p,norm_mul,htwo,hden]
  norm_num
  nlinarith

end AnchorLocalSquareProduction318
