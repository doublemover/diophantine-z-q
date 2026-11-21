module
public import CTRetainedDyadicTorsionClasses318
public import CTOriginalPadicValuationPairs318
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
public section

noncomputable section

namespace CTDyadicSourceTorsionImage318

open ActualTwoDescentPadicValuationPairs318 ActualTwoDescentLocalValuationTools318
open ActualTwoDescentSquareClassQuotient318 CTRetainedDyadicTorsionClasses318

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem valuation_add_fixed_unit (x b : ℚ_[2])
    (hx : x≠0) (hb : b≠0) (hv : x.valuation≠0) (hbu : b.valuation=0) :
    x+b≠0 ∧ (x+b).valuation=min x.valuation 0 := by
  have hne : x+b≠0 := by
    intro h
    have h' : x= -b := eq_neg_of_add_eq_zero_left h
    exact hv (by rw [h',actual_valuation_neg,hbu])
  exact ⟨hne,(actual_valuation_add_min x b hx hb hne (by rwa [hbu])).trans
    (congrArg (min x.valuation) hbu)⟩

private theorem selected_not_dvd_two (n : ℕ) (hr : (n:ZMod 12)=11) :
    ¬ 2∣n := by
  intro h
  have h12 : n%12=11 := by
    have h' := congrArg ZMod.val hr
    norm_num only [ZMod.val_natCast] at h'
    exact h'
  have h2 : n%2=1 := by
    rw [← Nat.mod_mod_of_dvd n (by decide : 2∣12),h12]
  exact (by decide : (1:ℕ)≠0) (h2.symm.trans (Nat.mod_eq_zero_of_dvd h))

/-- For the actual source cubic every nonzero abscissa has even valuation,
including nonzero torsion and negative-valuation points. No target data
or local Tate pairing is used. -/
theorem actual_source_even_valuation (n : ℕ) (hn : 0<n) (hr : (n:ZMod 12)=11)
    (x y : ℚ_[2]) (hx : x≠0) (hC : y^2=x*(x-n)*(x+3*n)) :
    x.valuation%2=0 := by
  by_cases hv : x.valuation=0
  · simp [hv]
  have hn0 : (n:ℚ_[2])≠0 := Nat.cast_ne_zero.mpr hn.ne'
  have hvn := actual_prime_unit_valuation (p:=2) n (selected_not_dvd_two n hr)
  have h3 : (3:ℚ_[2])≠0 := by norm_num
  have h3v : (3:ℚ_[2]).valuation=0 := by
    change ((3:ℕ):ℚ_[2]).valuation=0
    exact actual_prime_unit_valuation (p:=2) 3 (by decide)
  have hp3 : (3*(n:ℚ_[2])).valuation=0 := by rw [Padic.valuation_mul h3 hn0,h3v,hvn,add_zero]
  have hnm : (-(n:ℚ_[2])).valuation=0 := (actual_valuation_neg _).trans hvn
  obtain ⟨hL,hLv⟩ := valuation_add_fixed_unit x (-(n:ℚ_[2])) hx (neg_ne_zero.mpr hn0) hv hnm
  obtain ⟨hR,hRv⟩ := valuation_add_fixed_unit x (3*(n:ℚ_[2])) hx (mul_ne_zero h3 hn0) hv hp3
  rw [←sub_eq_add_neg] at hL hLv
  have hVal := congrArg Padic.valuation hC
  rw [Padic.valuation_pow,Padic.valuation_mul (mul_ne_zero hx hL) hR,
    Padic.valuation_mul hx hL,hLv,hRv] at hVal
  by_cases hX : x.valuation≤0
  · rw [min_eq_left hX] at hVal
    omega
  · rw [min_eq_right (by omega : 0 ≤ x.valuation)] at hVal
    omega

theorem actual_source_affine_class_is_torsion (n : ℕ) (hn : 0<n)
    (hr : (n:ZMod 12)=11) (x y : ℚ_[2]) (hx : x≠0)
    (hC : y^2=x*(x-n)*(x+3*n)) :
    ∃ i : Bool × Bool, classOf x hx=torsionClass n hr i :=
  even_valuation_class_is_torsion n hr x hx (actual_source_even_valuation n hn hr x y hx hC)

end CTDyadicSourceTorsionImage318

#print axioms CTDyadicSourceTorsionImage318.actual_source_affine_class_is_torsion
