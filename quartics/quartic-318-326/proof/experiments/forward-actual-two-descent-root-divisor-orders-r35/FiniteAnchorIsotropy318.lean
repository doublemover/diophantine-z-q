module
public import PreparedAnchorSource318
public import Mathlib.FieldTheory.Finite.Basic
public section
noncomputable section
namespace FiniteAnchorIsotropy318
open Polynomial
set_option maxHeartbeats 1000000

/-- The finite-field intersection argument applies at every prime at least5,
including primes in the eventual numerator or denominator of the target. -/
theorem residue_isotropy (p : ℕ) [Fact p.Prime] (hp : 5≤p) :
    ∃ x y : ZMod p, x^2+6*y^2=2 := by
  have hpprime : p.Prime := Fact.out
  have hp2 : ¬p∣2 := fun h => by have hh := Nat.le_of_dvd (by norm_num : 0<2) h; omega
  have hp3 : ¬p∣3 := fun h => by have hh := Nat.le_of_dvd (by norm_num : 0<3) h; omega
  have hp6 : ¬p∣6 := by
    intro h
    have h' : p∣2*3 := by simpa using h
    exact (hpprime.dvd_mul.mp h').elim hp2 hp3
  have h6 : (6:ZMod p)≠0 := by
    intro h
    apply hp6
    exact (ZMod.natCast_zmod_eq_zero_iff_dvd 6 p).mp h
  have hodd : p%2=1 := by
    rcases hpprime.eq_two_or_odd with he|he
    · omega
    · exact he
  let f : Polynomial (ZMod p) := X^2
  let g : Polynomial (ZMod p) := C 6*X^2-C 2
  have hf : degree f=2 := degree_X_pow 2
  have hg0 : degree (C (6:ZMod p)*X^2)=2 := by
    rw [degree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr h6),degree_X_pow]
  have hg : degree g=2 := by
    rw [g,degree_sub_C (by rw [hg0]; decide),hg0]
  obtain ⟨x,y,hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg (by simpa only [ZMod.card] using hodd)
  refine ⟨x,y,?_⟩
  simp only [f,g,eval_pow,eval_X,eval_C,eval_mul,eval_sub] at hxy
  linear_combination hxy

/-- The exact standard integer lifts retain the finite-field equation as a
single divisibility statement, ready for the actual p-adic Hensel step. -/
theorem integer_lifts (p : ℕ) [Fact p.Prime] (hp : 5≤p) :
    ∃ x y : ℤ, (p:ℤ)∣x^2+6*y^2-2 := by
  obtain ⟨x,y,hxy⟩ := residue_isotropy p hp
  refine ⟨(x.val:ℤ),(y.val:ℤ),?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  push_cast
  simpa only [ZMod.natCast_zmod_val] using sub_eq_zero.mpr hxy

end FiniteAnchorIsotropy318
