module
public import ActualTZReferenceFactorNearOne318
public section
noncomputable section
namespace ActualTZWheelZero318
open scoped BigOperators
open ActualTZReferenceFactorNearOne318 ActualTZRegulatedZetaAlgebra318

@[expose] def alpha (W : ℕ) : ℂ := (Nat.totient W:ℂ)/(W:ℂ)

theorem alpha_ne_zero (W : ℕ) (hW : 0<W) : alpha W≠0 := by
  have hN : Nat.totient W≠0 := (Nat.totient_pos.mpr hW).ne'
  have hW0 : W≠0 := hW.ne'
  exact div_ne_zero (by exact_mod_cast hN) (by exact_mod_cast hW0)

theorem atom_den_ne (p : ℕ) (hp : p.Prime) : 1-1/(p:ℂ)≠0 := by
  have hpR : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have h : (1:ℝ)-1/(p:ℝ)>0 := by
    apply sub_pos.mpr
    exact (div_lt_one (zero_lt_one.trans hpR)).2 hpR
  have H : (((1:ℝ)-1/(p:ℝ)):ℂ)≠0 := Complex.ofReal_ne_zero.mpr h.ne'
  simpa only [Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_div,Complex.ofReal_natCast] using H

theorem atom_zero (p : ℕ) (hp : p.Prime) : B p 0 0=1-1/(p:ℂ) := by
  simp only [B,oneSite,neg_zero,Complex.cpow_zero,mul_one]
  exact (div_eq_iff (atom_den_ne p hp)).2 rfl

/-- Exact Euler-φ identity, including the empty wheel W=1. No
averaging over residues is substituted for the fixed actual wheel. -/
theorem alpha_product (W : ℕ) (hW : 0<W) :
    alpha W=∏ p∈W.primeFactors,(1-1/(p:ℂ)) := by
  have hW0 : (W:ℂ)≠0 := by exact_mod_cast hW.ne'
  have H := congrArg (Rat.castHom ℂ) (Nat.totient_eq_mul_prod_factors W)
  simp only [map_mul,map_prod,Rat.coe_castHom,Rat.cast_natCast,Rat.cast_sub,
    Rat.cast_one,Rat.cast_inv] at H
  change (Nat.totient W:ℂ)/(W:ℂ)=_
  apply (div_eq_iff hW0).2
  simpa only [one_div,mul_comm] using H

variable {I : Type*} [Fintype I]

@[expose] def wheel (W : ℕ) (s t : I→ℂ) : ℂ :=
  ∏ p∈W.primeFactors,∏ i : I,B p (s i) (t i)

theorem wheel_zero (W : ℕ) (hW : 0<W) :
    wheel W (0 : I→ℂ) (0 : I→ℂ)=alpha W^Fintype.card I := by
  unfold wheel
  rw [Finset.prod_comm,←Finset.prod_const]
  apply Finset.prod_congr rfl
  intro i _
  rw [alpha_product W hW]
  apply Finset.prod_congr rfl
  intro p hp
  exact atom_zero p (Nat.mem_primeFactors.mp hp).1

end ActualTZWheelZero318
