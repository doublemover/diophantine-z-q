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

private theorem square_eight (x : ℤ) : x^2%8=0 ∨ x^2%8=1 ∨ x^2%8=4 := by
  have hh := square_mod_sixteen x
  omega

private theorem odd_square_sixteen (x : ℤ) (hx : x%2=1) :
    x^2%16=1 ∨ x^2%16=9 := by
  have hh := square_mod_sixteen x
  have hh4 := Int.sq_emod_four x
  omega

private theorem even_square_sixteen (x : ℤ) (hx : x%2=0) :
    x^2%16=0 ∨ x^2%16=4 := by
  have hh := square_mod_sixteen x
  have hh4 := Int.sq_emod_four x
  omega

private theorem unit_numerator_odd (a t x z w : ℤ) (ha : a%4=2)
    (ht : Odd t) (hw : Odd w) (h4 : 4∣z^2-a*x^2-t*w^2) : Odd z := by
  have ht2 := Int.odd_iff.mp ht
  have hw2 := Int.odd_iff.mp hw
  have hm := Int.dvd_iff_emod_eq_zero.mp h4
  norm_num [Int.sub_emod,Int.mul_emod,Int.sq_emod_four,ha,hw2] at hm
  exact Int.odd_iff.mpr (by omega)

private theorem even_numerator_parity (a v x z w : ℤ) (ha : a%4=2)
    (hv : Odd v) (hw : Odd w) (h4 : 4∣z^2-a*x^2-(2*v)*w^2) :
    x%2=1 ∧ z%2=0 := by
  have hv2 := Int.odd_iff.mp hv
  have hw2 := Int.odd_iff.mp hw
  have hv4 : (2*v)%4=2 := by omega
  have hm := Int.dvd_iff_emod_eq_zero.mp h4
  norm_num [Int.sub_emod,Int.mul_emod,Int.sq_emod_four,ha,hw2] at hm
  omega

/-- Isolated finite residue arithmetic: no unrelated primitive/local facts
are carried into omega's context. Each branch is linear modular arithmetic. -/
private theorem unit_residue_table (A t r : ℤ)
    (ha : A=2 ∨ A=6) (hr : r=0 ∨ r=1 ∨ r=4)
    (hm : (1-A*r-t)%8=0) : t%8=1 ∨ t%8=(1-A)%8 := by
  rcases ha with rfl | rfl <;> rcases hr with rfl | rfl | rfl <;>
    norm_num at hm ⊢ <;> omega

private theorem even_residue_table (A v r s u : ℤ)
    (ha : A=2 ∨ A=6) (hr : r=1 ∨ r=9)
    (hs : s=0 ∨ s=4) (hu : u=1 ∨ u=9)
    (hm : (s-A*r-2*v*u)%16=0) : v%8=7 ∨ v%8=A-1 := by
  rcases ha with rfl | rfl <;> rcases hr with rfl | rfl <;>
    rcases hs with rfl | rfl <;> rcases hu with rfl | rfl <;>
    norm_num at hm ⊢ <;> omega

/-- Unit norm classes: coefficient2 gives1 or7, coefficient6 gives1 or3 mod8. -/
theorem unit_norm_table (a t x z w : ℤ) (ha : a%8=2 ∨ a%8=6)
    (ht : Odd t) (hcong : 8∣z^2-a*x^2-t*w^2)
    (hprim : ¬(2∣x ∧ 2∣z ∧ 2∣w)) :
    t%8=1 ∨ t%8=(1-a)%8 := by
  have ha4 : a%4=2 := by omega
  have h4 : 4∣z^2-a*x^2-t*w^2 := dvd_trans (by norm_num : (4:ℤ)∣8) hcong
  have hw := denominator_odd a t x z w ha4 h4 hprim
  have hz := unit_numerator_odd a t x z w ha4 ht hw h4
  have hz8 := odd_square_eight z hz
  have hw8 := odd_square_eight w hw
  have hm : (1-(a%8)*(x^2%8)-t)%8=0 := by
    have hh := Int.dvd_iff_emod_eq_zero.mp hcong
    simpa [Int.sub_emod,Int.mul_emod,hz8,hw8] using hh
  have hh := unit_residue_table (a%8) t (x^2%8) ha (square_eight x) hm
  simpa only [Int.sub_emod,Int.emod_emod] using hh

/-- Valuation-one classes are computed modulo16 BEFORE dividing by2:
coefficient2 gives odd part1 or7; coefficient6 gives odd part5 or7 mod8. -/
theorem even_norm_table (a v x z w : ℤ) (ha : a%16=2 ∨ a%16=6)
    (hv : Odd v) (hcong : 16∣z^2-a*x^2-(2*v)*w^2)
    (hprim : ¬(2∣x ∧ 2∣z ∧ 2∣w)) :
    v%8=7 ∨ v%8=a%16-1 := by
  have ha4 : a%4=2 := by omega
  have h4 : 4∣z^2-a*x^2-(2*v)*w^2 := dvd_trans (by norm_num : (4:ℤ)∣16) hcong
  have hw := denominator_odd a (2*v) x z w ha4 h4 hprim
  have hp := even_numerator_parity a v x z w ha4 hv hw h4
  have hx16 := odd_square_sixteen x hp.1
  have hz16 := even_square_sixteen z hp.2
  have hw16 := odd_square_sixteen w (Int.odd_iff.mp hw)
  have hm : ((z^2%16)-(a%16)*(x^2%16)-2*v*(w^2%16))%16=0 := by
    have hh := Int.dvd_iff_emod_eq_zero.mp hcong
    simpa [Int.sub_emod,Int.mul_emod] using hh
  exact even_residue_table (a%16) v (x^2%16) (z^2%16) (w^2%16)
    ha hx16 hz16 hw16 hm

end LegendreDyadicNormTables318
