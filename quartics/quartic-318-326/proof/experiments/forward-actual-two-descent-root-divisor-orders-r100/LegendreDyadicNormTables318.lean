module
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Tactic
public section
namespace LegendreDyadicNormTables318

/-- Primitivity and a coefficient2 mod4 force the homogenizing coordinate odd.
This is derived, not assumed in the norm tables. -/
theorem denominator_odd (a t x z w : ℤ) (ha : a%4=2)
    (hcong : 4∣z^2-a*x^2-t*w^2)
    (hprim : ¬(2∣x ∧ 2∣z ∧ 2∣w)) : Odd w := by
  apply Int.odd_iff.mpr
  by_contra hw
  have hw0 : w%2=0 := by omega
  have hm := Int.dvd_iff_emod_eq_zero.mp hcong
  norm_num [Int.sub_emod,Int.mul_emod,Int.sq_emod_four,ha,hw0] at hm
  have hx0 : x%2=0 := by omega
  have hz0 : z%2=0 := by omega
  exact hprim ⟨Int.dvd_iff_emod_eq_zero.mpr hx0,
    Int.dvd_iff_emod_eq_zero.mpr hz0,Int.dvd_iff_emod_eq_zero.mpr hw0⟩

/-- Complete square residues at the depth needed before dividing an even norm. -/
theorem square_mod_sixteen (x : ℤ) :
    x^2%16=0 ∨ x^2%16=1 ∨ x^2%16=4 ∨ x^2%16=9 := by
  have hlo := Int.emod_nonneg x (by norm_num : (16:ℤ)≠0)
  have hhi := Int.emod_lt_of_pos x (by norm_num : (0:ℤ)<16)
  rw [show x^2%16=(x%16)^2%16 by simp [pow_two,Int.mul_emod]]
  interval_cases hx : x%16 <;> norm_num [hx]

private theorem odd_square_eight (x : ℤ) (hx : Odd x) : x^2%8=1 := by
  have hh := Int.eight_dvd_sq_sub_one_of_odd hx
  rw [Int.dvd_iff_emod_eq_zero] at hh
  omega

/-- Unit norm classes: coefficient2 gives1 or7, coefficient6 gives1 or3 mod8. -/
theorem unit_norm_table (a t x z w : ℤ) (ha : a%8=2 ∨ a%8=6)
    (ht : Odd t) (hcong : 8∣z^2-a*x^2-t*w^2)
    (hprim : ¬(2∣x ∧ 2∣z ∧ 2∣w)) :
    t%8=1 ∨ t%8=(1-a)%8 := by
  have ha4 : a%4=2 := by omega
  have h4 : 4∣z^2-a*x^2-t*w^2 := dvd_trans (by norm_num : (4:ℤ)∣8) hcong
  have hw := denominator_odd a t x z w ha4 h4 hprim
  have hw2 := Int.odd_iff.mp hw
  have ht2 := Int.odd_iff.mp ht
  have hm4 := Int.dvd_iff_emod_eq_zero.mp h4
  norm_num [Int.sub_emod,Int.mul_emod,Int.sq_emod_four,ha4,hw2] at hm4
  have hz : Odd z := Int.odd_iff.mpr (by omega)
  have hz8 := odd_square_eight z hz
  have hw8 := odd_square_eight w hw
  have hx8 : x^2%8=0 ∨ x^2%8=1 ∨ x^2%8=4 := by
    have hh := square_mod_sixteen x
    omega
  have hm := Int.dvd_iff_emod_eq_zero.mp hcong
  rcases ha with ha | ha <;> rcases hx8 with hx8 | hx8 | hx8 <;>
    norm_num [Int.sub_emod,Int.mul_emod,ha,hx8,hz8,hw8] at hm ⊢ <;> omega

/-- Valuation-one classes are computed modulo16 BEFORE dividing by2:
coefficient2 gives odd part1 or7; coefficient6 gives odd part5 or7 mod8. -/
theorem even_norm_table (a v x z w : ℤ) (ha : a%16=2 ∨ a%16=6)
    (hv : Odd v) (hcong : 16∣z^2-a*x^2-(2*v)*w^2)
    (hprim : ¬(2∣x ∧ 2∣z ∧ 2∣w)) :
    v%8=7 ∨ v%8=a%16-1 := by
  have ha4 : a%4=2 := by omega
  have h4 : 4∣z^2-a*x^2-(2*v)*w^2 := dvd_trans (by norm_num : (4:ℤ)∣16) hcong
  have hw := denominator_odd a (2*v) x z w ha4 h4 hprim
  have hw2 := Int.odd_iff.mp hw
  have hv2 := Int.odd_iff.mp hv
  have hv4 : (2*v)%4=2 := by omega
  have hm4 := Int.dvd_iff_emod_eq_zero.mp h4
  norm_num [Int.sub_emod,Int.mul_emod,Int.sq_emod_four,ha4,hw2] at hm4
  have hz2 : z%2=0 := by omega
  have hx2 : x%2=1 := by omega
  have hx16 : x^2%16=1 ∨ x^2%16=9 := by
    have hh := square_mod_sixteen x
    have hh4 := Int.sq_emod_four x
    omega
  have hz16 : z^2%16=0 ∨ z^2%16=4 := by
    have hh := square_mod_sixteen z
    have hh4 := Int.sq_emod_four z
    omega
  have hw16 : w^2%16=1 ∨ w^2%16=9 := by
    have hh := square_mod_sixteen w
    have hh4 := Int.sq_emod_four w
    omega
  have hm := Int.dvd_iff_emod_eq_zero.mp hcong
  rcases ha with ha | ha <;> rcases hx16 with hx16 | hx16 <;>
    rcases hz16 with hz16 | hz16 <;> rcases hw16 with hw16 | hw16 <;>
    norm_num [Int.sub_emod,Int.mul_emod,ha,hx16,hz16,hw16] at hm ⊢ <;> omega

end LegendreDyadicNormTables318
