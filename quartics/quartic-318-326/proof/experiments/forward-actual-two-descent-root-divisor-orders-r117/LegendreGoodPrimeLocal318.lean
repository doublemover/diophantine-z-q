module
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.Tactic
public section
noncomputable section
namespace LegendreGoodPrimeLocal318
open Polynomial

/-- At an odd prime a nondegenerate binary norm represents every residue. -/
theorem finite_norm (p : ℕ) [Fact p.Prime] (hp2 : p≠2)
    (a b : ℤ) (ha : ¬(p:ℤ)∣a) :
    ∃ x z : ZMod p, z^2-(a:ZMod p)*x^2=(b:ZMod p) := by
  have hp : p.Prime := Fact.out
  have hodd : p%2=1 := hp.eq_two_or_odd.resolve_left hp2
  have ha0 : (a:ZMod p)≠0 := fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)
  let f : Polynomial (ZMod p) := X^2
  let g : Polynomial (ZMod p) := C (-(a:ZMod p))*X^2-C (b:ZMod p)
  have hf : degree f=2 := degree_X_pow 2
  have hg0 : degree (C (-(a:ZMod p))*X^2)=2 := by
    rw [degree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr ha0)),degree_X_pow]
    norm_num
  have hg : degree g=2 := by
    dsimp only [g]
    rw [degree_sub_C (by rw [hg0]; decide),hg0]
  obtain ⟨z,x,hzx⟩ := FiniteField.exists_root_sum_quadratic hf hg
    (by simpa only [ZMod.card] using hodd)
  refine ⟨x,z,?_⟩
  simp only [f,g,eval_pow,eval_X,eval_C,eval_mul,eval_sub] at hzx
  linear_combination hzx

/-- Outside the primes of2ab, the actual p-adic binary norm represents b.
The finite-field solution is lifted by varying its homogenizing coordinate,
whose derivative is -2b, a unit. No local-solubility premise is supplied. -/
theorem represents_unit (p : ℕ) [Fact p.Prime] (hp2 : p≠2)
    (a b : ℤ) (ha : ¬(p:ℤ)∣a) (hb : ¬(p:ℤ)∣b) :
    ∃ x z : ℚ_[p], z^2-(a:ℚ_[p])*x^2=(b:ℚ_[p]) := by
  obtain ⟨x,z,hxz⟩ := finite_norm p hp2 a b ha
  let Xi : ℤ := x.val
  let Z : ℤ := z.val
  have hdiv : (p:ℤ)∣Z^2-a*Xi^2-b := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    dsimp only [Xi,Z]
    push_cast
    simpa only [ZMod.natCast_zmod_val] using sub_eq_zero.mpr hxz
  have hunit (v : ℤ) (hv : ¬(p:ℤ)∣v) : ‖(v:ℤ_[p])‖=1 := by
    apply le_antisymm (PadicInt.norm_le_one _)
    exact le_of_not_gt (fun h => hv (PadicInt.norm_intCast_lt_one_iff.mp h))
  have hp : p.Prime := Fact.out
  have hp2N : ¬p∣2 := by
    intro h
    exact hp2 ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp h |>.resolve_left hp.ne_one)
  have hp2Z : ¬(p:ℤ)∣(2:ℤ) := by exact_mod_cast hp2N
  have htwo : ‖(2:ℤ_[p])‖=1 := by simpa using hunit 2 hp2Z
  have hbunit := hunit b hb
  let F : Polynomial ℤ_[p] := C ((Z:ℤ_[p])^2-(a:ℤ_[p])*(Xi:ℤ_[p])^2)-C (b:ℤ_[p])*Polynomial.X^2
  have heval : F.aeval (1:ℤ_[p])=((Z^2-a*Xi^2-b:ℤ):ℤ_[p]) := by
    simp [F]
  have hderiv : F.derivative.aeval (1:ℤ_[p])= -(2*(b:ℤ_[p])) := by
    dsimp only [F]
    rw [derivative_sub,derivative_C,derivative_C_mul_X_sq]
    norm_num
    <;> ring
  have hder : ‖F.derivative.aeval (1:ℤ_[p])‖=1 := by
    rw [hderiv,norm_neg,norm_mul,htwo,hbunit,mul_one]
  have hnorm : ‖F.aeval (1:ℤ_[p])‖<‖F.derivative.aeval (1:ℤ_[p])‖^2 := by
    rw [heval,hder,one_pow]
    exact PadicInt.norm_intCast_lt_one_iff.mpr hdiv
  obtain ⟨w,hw,hclose,_⟩ := hensels_lemma hnorm
  have hw0 : w≠0 := by
    intro h
    rw [hder] at hclose
    simpa [h] using hclose
  have hc : (Z:ℤ_[p])^2-(a:ℤ_[p])*(Xi:ℤ_[p])^2-(b:ℤ_[p])*w^2=0 := by
    simpa [F] using hw
  have hwQ : (w:ℚ_[p])≠0 := fun h => hw0 (PadicInt.ext (by simpa using h))
  have hcQ : (Z:ℚ_[p])^2-(a:ℚ_[p])*(Xi:ℚ_[p])^2-(b:ℚ_[p])*(w:ℚ_[p])^2=0 :=
    congrArg (fun v : ℤ_[p] => (v:ℚ_[p])) hc
  refine ⟨(Xi:ℚ_[p])/(w:ℚ_[p]),(Z:ℚ_[p])/(w:ℚ_[p]),?_⟩
  calc
    _=((Z:ℚ_[p])^2-(a:ℚ_[p])*(Xi:ℚ_[p])^2)/(w:ℚ_[p])^2 := by ring
    _=(b:ℚ_[p]) := by rw [sub_eq_zero.mp hcQ]; simp [hwQ]

end LegendreGoodPrimeLocal318
