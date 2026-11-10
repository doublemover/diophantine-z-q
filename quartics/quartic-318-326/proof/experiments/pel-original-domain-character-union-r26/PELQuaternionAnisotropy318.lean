module
public import PELQuaternionAlgebra318
public import Mathlib.Data.ZMod.Basic
public section
noncomputable section
namespace PELQuaternionAnisotropy318
open PELQuaternionAlgebra318
set_option maxHeartbeats 1000000

/-- Two successive residue computations at three apply to the literal
reduced norm of B=(-210,5), not the unrelated ternary anchor form. -/
theorem outer_residues : ∀ r i j k : ZMod 3,
    r^2+210*i^2-5*j^2-1050*k^2=0 → r=0 ∧ j=0 := by decide

theorem inner_residues : ∀ a i b k : ZMod 3,
    3*a^2+70*i^2-15*b^2-350*k^2=0 → i=0 ∧ k=0 := by decide

theorem coordinates_divisible_three (r i j k : ℤ)
    (h : r^2+210*i^2-5*j^2-1050*k^2=0) :
    (3:ℤ)∣r ∧ (3:ℤ)∣i ∧ (3:ℤ)∣j ∧ (3:ℤ)∣k := by
  have hm : (r:ZMod 3)^2+210*(i:ZMod 3)^2-5*(j:ZMod 3)^2-
      1050*(k:ZMod 3)^2=0 := by
    have hh := congrArg (fun z : ℤ => (z:ZMod 3)) h
    push_cast at hh
    exact hh
  obtain ⟨hr,hj⟩ := outer_residues _ _ _ _ hm
  obtain ⟨a,ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd r 3).mp hr
  obtain ⟨b,hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd j 3).mp hj
  have hn : 3*a^2+70*i^2-15*b^2-350*k^2=0 := by
    rw [ha,hb] at h
    nlinarith [h]
  have hnm : 3*(a:ZMod 3)^2+70*(i:ZMod 3)^2-15*(b:ZMod 3)^2-
      350*(k:ZMod 3)^2=0 := by
    have hh := congrArg (fun z : ℤ => (z:ZMod 3)) hn
    push_cast at hh
    exact hh
  obtain ⟨hi,hk⟩ := inner_residues _ _ _ _ hnm
  exact ⟨⟨a,ha⟩,(ZMod.intCast_zmod_eq_zero_iff_dvd i 3).mp hi,
    ⟨b,hb⟩,(ZMod.intCast_zmod_eq_zero_iff_dvd k 3).mp hk⟩

theorem integer_descent (n : ℕ) : ∀ r i j k : ℤ,
    r.natAbs+i.natAbs+j.natAbs+k.natAbs=n →
    r^2+210*i^2-5*j^2-1050*k^2=0 → r=0 ∧ i=0 ∧ j=0 ∧ k=0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro r i j k hn hq
    by_cases hz : n=0
    · have hr : r.natAbs=0 := by omega
      have hi : i.natAbs=0 := by omega
      have hj : j.natAbs=0 := by omega
      have hk : k.natAbs=0 := by omega
      exact ⟨Int.natAbs_eq_zero.mp hr,Int.natAbs_eq_zero.mp hi,
        Int.natAbs_eq_zero.mp hj,Int.natAbs_eq_zero.mp hk⟩
    obtain ⟨⟨a,ha⟩,⟨b,hb⟩,⟨c,hc⟩,⟨d,hd⟩⟩ :=
      coordinates_divisible_three r i j k hq
    rw [ha,hb,hc,hd] at hn hq ⊢
    have hs : a^2+210*b^2-5*c^2-1050*d^2=0 := by nlinarith [hq]
    have hn3 : 3*(a.natAbs+b.natAbs+c.natAbs+d.natAbs)=n := by
      simpa [Int.natAbs_mul,Nat.mul_add] using hn
    have hlt : a.natAbs+b.natAbs+c.natAbs+d.natAbs<n := by omega
    obtain ⟨ha0,hb0,hc0,hd0⟩ := ih _ hlt a b c d rfl hs
    simp [ha0,hb0,hc0,hd0]

/-- An actual well-founded descent, not a finite coefficient search. -/
theorem integer_anisotropic (r i j k : ℤ)
    (h : r^2+210*i^2-5*j^2-1050*k^2=0) : r=0 ∧ i=0 ∧ j=0 ∧ k=0 :=
  integer_descent _ r i j k rfl h

/-- Clearing all four actual rational denominators connects the integral
obstruction to the same quaternion carrier over Q. -/
theorem rational_anisotropic (r i j k : ℚ)
    (h : r^2+210*i^2-5*j^2-1050*k^2=0) : r=0 ∧ i=0 ∧ j=0 ∧ k=0 := by
  let R : ℤ := r.num*i.den*j.den*k.den
  let I : ℤ := i.num*r.den*j.den*k.den
  let J : ℤ := j.num*r.den*i.den*k.den
  let K : ℤ := k.num*r.den*i.den*j.den
  let D : ℚ := (r.den:ℚ)*(i.den:ℚ)*(j.den:ℚ)*(k.den:ℚ)
  have hr : (R:ℚ)=r*D := by
    dsimp [R,D]; push_cast; rw [← Rat.mul_den_eq_num r]; ring
  have hi : (I:ℚ)=i*D := by
    dsimp [I,D]; push_cast; rw [← Rat.mul_den_eq_num i]; ring
  have hj : (J:ℚ)=j*D := by
    dsimp [J,D]; push_cast; rw [← Rat.mul_den_eq_num j]; ring
  have hk : (K:ℚ)=k*D := by
    dsimp [K,D]; push_cast; rw [← Rat.mul_den_eq_num k]; ring
  have hscaled : (R:ℚ)^2+210*(I:ℚ)^2-5*(J:ℚ)^2-1050*(K:ℚ)^2=0 := by
    rw [hr,hi,hj,hk]
    linear_combination D^2*h
  have hint : R^2+210*I^2-5*J^2-1050*K^2=0 := by exact_mod_cast hscaled
  obtain ⟨hR,hI,hJ,hK⟩ := integer_anisotropic R I J K hint
  have hD : D≠0 := by dsimp [D]; positivity
  have hrD : r*D=0 := by rw [← hr,hR] <;> simp
  have hiD : i*D=0 := by rw [← hi,hI] <;> simp
  have hjD : j*D=0 := by rw [← hj,hJ] <;> simp
  have hkD : k*D=0 := by rw [← hk,hK] <;> simp
  exact ⟨(mul_eq_zero.mp hrD).resolve_right hD,(mul_eq_zero.mp hiD).resolve_right hD,
    (mul_eq_zero.mp hjD).resolve_right hD,(mul_eq_zero.mp hkD).resolve_right hD⟩

theorem reducedNorm_ne_zero (x : B) (hx : x≠0) : reducedNorm x≠0 := by
  intro h
  obtain ⟨hr,hi,hj,hk⟩ := rational_anisotropic x.re x.imI x.imJ x.imK h
  apply hx
  ext <;> assumption
end PELQuaternionAnisotropy318
