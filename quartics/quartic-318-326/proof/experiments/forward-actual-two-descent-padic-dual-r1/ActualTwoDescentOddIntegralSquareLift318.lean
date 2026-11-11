module
public import ActualTwoDescentFiniteOriginalCompatibility318
public section
noncomputable section
namespace ActualTwoDescentOddIntegralSquareLift318
set_option maxHeartbeats 16000000

open ActualTwoDescentHenselSquare318
variable {p : ℕ} [Fact p.Prime]

/-- An arbitrary signed integral unit square root modulo p lifts to the literal p-adic integer. -/
theorem actual_odd_integral_square_lift (hp2 : p ≠ 2) (A : ℤ) (z : ZMod p)
    (hz : z ≠ 0) (he : z^2=(A : ZMod p)) :
    ∃ r : ℚ_[p], r ≠ 0 ∧ r^2=(A : ℚ_[p]) := by
  have hx : Nat.Coprime p z.val := by
    apply Nat.Coprime.symm
    apply (ZMod.isUnit_iff_coprime z.val p).mp
    rw [ZMod.natCast_zmod_val]
    exact isUnit_iff_ne_zero.mpr hz
  have hdiv : (p : ℤ) ∣ (z.val : ℤ)^2-A := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    push_cast
    rw [ZMod.natCast_zmod_val,he,sub_self]
  have h2 : ‖(2 : ℤ_[p])‖=1 := PadicInt.norm_natCast_eq_one_iff.mpr
    ((Nat.coprime_primes Fact.out (by decide : Nat.Prime 2)).mpr hp2)
  have hxn : ‖(z.val : ℤ_[p])‖=1 := PadicInt.norm_natCast_eq_one_iff.mpr hx
  have hres : ‖(z.val : ℤ_[p])^2-(A : ℤ_[p])‖ < 1 := by
    have h := (PadicInt.norm_int_lt_one_iff_dvd ((z.val : ℤ)^2-A)).mpr hdiv
    simpa only [Int.cast_sub,Int.cast_pow,Int.cast_natCast] using h
  obtain ⟨r,hr⟩ := actual_hensel_square (A : ℤ_[p]) (z.val : ℤ_[p]) (by
    simpa only [norm_mul,h2,hxn,one_mul,one_pow] using hres)
  have hr' : (r : ℚ_[p])^2=(A : ℚ_[p]) := by exact_mod_cast hr
  have hA : A ≠ 0 := by
    intro h
    rw [h,Int.cast_zero] at he
    exact (pow_ne_zero _ hz) he
  refine ⟨(r : ℚ_[p]),?_,hr'⟩
  intro h
  have hzero : (A : ℚ_[p])=0 := by simpa only [h,zero_pow (by decide : (2 : ℕ) ≠ 0)] using hr'.symm
  exact hA (Int.cast_eq_zero.mp hzero)

/-- Equality of unit residue squareclasses gives an actual nonzero p-adic square multiplier. -/
theorem actual_unit_squareclass_lift (hp2 : p ≠ 2) (A B : ℤ)
    (hA : (A : ZMod p) ≠ 0) (hB : (B : ZMod p) ≠ 0)
    (H : ∃ s : ZMod p, s ≠ 0 ∧ (A : ZMod p)=(B : ZMod p)*s^2) :
    ∃ r : ℚ_[p], r ≠ 0 ∧ (A : ℚ_[p])=(B : ℚ_[p])*r^2 := by
  obtain ⟨s,hs,hS⟩ := H
  have he : ((B : ZMod p)*s)^2=((A*B : ℤ) : ZMod p) := by
    rw [Int.cast_mul,hS]
    ring
  obtain ⟨r,hr,hr2⟩ := actual_odd_integral_square_lift hp2 (A*B) ((B : ZMod p)*s)
    (mul_ne_zero hB hs) he
  have hBz : B ≠ 0 := by intro h; apply hB; rw [h,Int.cast_zero]
  have hBq : (B : ℚ_[p]) ≠ 0 := Int.cast_ne_zero.mpr hBz
  refine ⟨r/(B : ℚ_[p]),div_ne_zero hr hBq,?_⟩
  push_cast at hr2
  rw [div_pow,hr2]
  field_simp [hBq]
  <;> ring

end ActualTwoDescentOddIntegralSquareLift318
