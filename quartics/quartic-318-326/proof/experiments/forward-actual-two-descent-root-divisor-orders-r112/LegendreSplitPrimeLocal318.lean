module
public import LegendreHomogeneousAffine318
public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.Data.ZMod.Basic
public section
noncomputable section
namespace LegendreSplitPrimeLocal318
open Polynomial

/-- A nonzero modular square at an odd prime lifts to an actual p-adic
square root. No p-adic local-solubility premise is supplied. -/
theorem sqrt_of_modular_square (p : ℕ) [Fact p.Prime] (hp2 : p≠2)
    (a : ℤ) (ha : ¬(p:ℤ)∣a) (hsq : IsSquare (a:ZMod p)) :
    ∃ s : ℚ_[p], s^2=(a:ℚ_[p]) := by
  obtain ⟨r,hr⟩ := hsq
  let R : ℤ := r.val
  have hRmod : (R:ZMod p)=r := by simp [R]
  have ha0 : (a:ZMod p)≠0 := fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)
  have hR : ¬(p:ℤ)∣R := by
    intro hd
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd R p).mpr hd
    rw [hRmod] at hz
    apply ha0
    simpa [hz] using hr
  have hdiv : (p:ℤ)∣R^2-a := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    push_cast
    rw [hRmod]
    simpa only [pow_two] using sub_eq_zero.mpr hr.symm
  have hunit (v : ℤ) (hv : ¬(p:ℤ)∣v) : ‖(v:ℤ_[p])‖=1 := by
    apply le_antisymm (PadicInt.norm_le_one _)
    exact le_of_not_gt (fun h => hv (PadicInt.norm_intCast_lt_one_iff.mp h))
  have hp : p.Prime := Fact.out
  have htwoN : ¬p∣2 := by
    intro hd
    exact hp2 ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd |>.resolve_left hp.ne_one)
  have htwoZ : ¬(p:ℤ)∣(2:ℤ) := by exact_mod_cast htwoN
  have htwo : ‖(2:ℤ_[p])‖=1 := by simpa using hunit 2 htwoZ
  have hRnorm := hunit R hR
  let F : Polynomial ℤ_[p] := C (1:ℤ_[p])*X^2-C (a:ℤ_[p])
  have heval : F.aeval (R:ℤ_[p])=((R^2-a:ℤ):ℤ_[p]) := by simp [F]
  have hderiv : F.derivative.aeval (R:ℤ_[p])=2*(R:ℤ_[p]) := by
    dsimp only [F]
    rw [derivative_sub,derivative_C,derivative_C_mul_X_sq]
    norm_num <;> ring
  have hder : ‖F.derivative.aeval (R:ℤ_[p])‖=1 := by
    rw [hderiv,norm_mul,htwo,hRnorm,mul_one]
  have hn : ‖F.aeval (R:ℤ_[p])‖<‖F.derivative.aeval (R:ℤ_[p])‖^2 := by
    rw [heval,hder,one_pow]
    exact PadicInt.norm_intCast_lt_one_iff.mpr hdiv
  obtain ⟨s,hs,_⟩ := hensels_lemma hn
  have he : s^2-(a:ℤ_[p])=0 := by simpa [F] using hs
  have heQ : (s:ℚ_[p])^2-(a:ℚ_[p])=0 :=
    congrArg (fun z : ℤ_[p] => (z:ℚ_[p])) he
  exact ⟨(s:ℚ_[p]),sub_eq_zero.mp heQ⟩

/-- Once reciprocity has supplied a nonzero modular square of a, the
new-prime place represents every b, including b divisible by p. This is
the missing split-prime branch, separate from the good-prime unit-b branch. -/
theorem represents_any (p : ℕ) [Fact p.Prime] (hp2 : p≠2)
    (a b : ℤ) (ha : ¬(p:ℤ)∣a) (hsq : IsSquare (a:ZMod p)) :
    ∃ x z : ℚ_[p], z^2-(a:ℚ_[p])*x^2=(b:ℚ_[p]) := by
  obtain ⟨s,hs⟩ := sqrt_of_modular_square p hp2 a ha hsq
  have haZ : a≠0 := fun h => ha (by simp [h])
  have haQ : (a:ℚ_[p])≠0 := by exact_mod_cast haZ
  have he : s^2-(a:ℚ_[p])*(1:ℚ_[p])^2-(b:ℚ_[p])*(0:ℚ_[p])^2=0 := by
    simp [hs]
  obtain ⟨z,x,hzx⟩ := LegendreHomogeneousAffine318.affine_of_homogeneous
    (a:ℚ_[p]) (b:ℚ_[p]) 1 s 0 haQ (by simp) he
  exact ⟨x,z,hzx⟩

end LegendreSplitPrimeLocal318
