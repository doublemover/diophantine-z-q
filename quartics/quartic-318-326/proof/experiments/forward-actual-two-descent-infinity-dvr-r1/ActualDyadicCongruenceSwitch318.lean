module
public import ActualOriginalCoordinateBump318
public section
noncomputable section
namespace ActualDyadicCongruenceSwitch318
open QuadricCRTAssembly318 ActualOriginalCoordinateBump318
set_option maxHeartbeats 28000000

/-- Adding exactly one base modulus modulo twice that modulus swaps
the two possibilities for an original multiple of the base modulus. -/
lemma original_multiple_switch (m A B : ℤ) (hm : m≠0) (hA : m∣A)
    (hB : 2*m∣B-A-m) : (2*m∣B ↔ ¬2*m∣A) := by
  obtain ⟨a,ha⟩ := hA
  obtain ⟨b,hb⟩ := hB
  have hB' : B=m*(a+1+2*b) := by nlinarith [ha,hb]
  rw [ha,hB',mul_comm 2 m,mul_dvd_mul_iff_left hm,mul_dvd_mul_iff_left hm]
  rw [←ZMod.intCast_zmod_eq_zero_iff_dvd (a+1+2*b) 2,
    ←ZMod.intCast_zmod_eq_zero_iff_dvd a 2]
  norm_num only [Int.cast_add,Int.cast_mul,Int.cast_one,Int.cast_ofNat,ZMod.natCast_self,
    zero_mul,add_zero]
  generalize hz : (a:ZMod 2)=z
  fin_cases z <;> decide

/-- The original square-coordinate half-modulus toggle changes Q by
exactly ONE base modulus modulo the next modulus. The n>=3 restriction
is explicit through n=e+3; this is where the quadratic toggle error dies. -/
theorem actual_odd_coordinate_toggle (κ : ℤ) (e : ℕ) (i : Fin 4) (x : Coordinates ℤ)
    (hi : (coordinate x i:ZMod 2)=1) :
    (2*(2:ℤ)^(e+3))∣
      equation κ (bump i ((2:ℤ)^(e+2)) x)-equation κ x-(2:ℤ)^(e+3) := by
  have hd : (2:ℤ)∣coordinate x i-1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
    rw [Int.cast_sub,Int.cast_one,hi,sub_self]
  obtain ⟨u,hu⟩ := hd
  have hx : coordinate x i=1+2*u := by linarith
  rw [original_bump_equation,hx]
  have hs : (sign i:ℤ)=1 ∨ (sign i:ℤ)= -1 := by
    unfold sign
    split_ifs <;> simp
  rcases hs with hs|hs
  · refine ⟨u+(2:ℤ)^e,?_⟩
    rw [hs,pow_add (2:ℤ) e 2,pow_add (2:ℤ) e 3]
    norm_num only [pow_two,show (2:ℤ)^3=8 by norm_num]
    ring
  · refine ⟨-u-1-(2:ℤ)^e,?_⟩
    rw [hs,pow_add (2:ℤ) e 2,pow_add (2:ℤ) e 3]
    norm_num only [pow_two,show (2:ℤ)^3=8 by norm_num]
    ring

/-- Exact next-congruence switching for the SAME original Q and
same literal original coordinate; no substitute quadratic form. -/
theorem actual_integer_toggle_switch (κ : ℤ) (e : ℕ) (i : Fin 4) (x : Coordinates ℤ)
    (hx : (2:ℤ)^(e+3)∣equation κ x) (hi : (coordinate x i:ZMod 2)=1) :
    (2*(2:ℤ)^(e+3)∣equation κ (bump i ((2:ℤ)^(e+2)) x)) ↔
      ¬(2*(2:ℤ)^(e+3)∣equation κ x) :=
  original_multiple_switch _ _ _ (pow_ne_zero _ (by norm_num)) hx
    (actual_odd_coordinate_toggle κ e i x hi)

end ActualDyadicCongruenceSwitch318
