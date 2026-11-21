module
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.LinearCombination
public import Lean.Elab.Tactic.Omega
public section

namespace OriginalCasselsRamifiedRootCriterion318

variable (p : ℕ) [Fact p.Prime]

/-- The literal normalized target polynomial has a root over the actual
residue field exactly at the split ramified primes. Nontrivial
cube roots correspond by t↦−t, with p=3 excluded. -/
theorem root_iff_residue_one (hp : 5≤p) :
    (∃ r : ZMod p, r^2-r+1=0) ↔ p%3=1 := by
  classical
  have hp3 : (3:ZMod p)≠0 := by
    intro h
    have d := (ZMod.natCast_eq_zero_iff 3 p).mp h
    have le := Nat.le_of_dvd (by decide : 0<3) d
    omega
  constructor
  · rintro ⟨r,hr⟩
    have hn : -r≠(0:ZMod p) := by
      intro h
      have hz := neg_eq_zero.mp h
      exact (one_ne_zero : (1:ZMod p)≠0) (by simpa only [hz,zero_pow (by decide : (2:ℕ)≠0),sub_zero,zero_add] using hr)
    have h1 : -r≠(1:ZMod p) := by
      intro h
      have he : r= -1 := by linear_combination -h
      rw [he] at hr
      exact hp3 (by linear_combination hr)
    have h3 : (-r)^3=1 := by linear_combination -(r+1)*hr
    let t : (ZMod p)ˣ := Units.mk0 (-r) hn
    have ht : t^3=1 := by
      apply Units.ext
      simpa only [Units.val_pow_eq_pow_val,Units.val_one,Units.val_mk0,t] using h3
    have ht1 : t≠1 := by
      intro h
      apply h1
      exact congrArg (fun u : (ZMod p)ˣ => (u:ZMod p)) h
    letI : Fact (Nat.Prime 3) := ⟨by decide⟩
    have hd : 3∣Fintype.card (ZMod p)ˣ := by
      rw [←orderOf_eq_prime ht ht1]
      exact orderOf_dvd_card
    rw [ZMod.card_units p] at hd
    omega
  · intro he
    let d := (p-1)/3
    have hp' : 0<d := by dsimp [d]; omega
    have hneq : ¬ p-1∣d := by
      intro hd
      have q := Nat.le_of_dvd hp' hd
      dsimp [d] at q
      omega
    have H : ¬∀ t : (ZMod p)ˣ, t^d=1 := by
      intro h
      apply hneq
      have hd := (FiniteField.forall_pow_eq_one_iff (K:=ZMod p) d).mp h
      rwa [ZMod.card p] at hd
    obtain ⟨t,ht⟩ := not_forall.mp H
    let u := t^d
    have hu : u^3=1 := by
      change (t^d)^3=1
      rw [←pow_mul,show d*3=p-1 by dsimp [d]; omega]
      exact ZMod.units_pow_card_sub_one_eq_one p t
    let a : ZMod p := (u:ZMod p)
    have h1 : a≠1 := by
      intro h
      apply ht
      apply Units.ext
      exact h
    have ha : a^3=1 := by
      have h := congrArg (fun v : (ZMod p)ˣ => (v:ZMod p)) hu
      simpa only [Units.val_pow_eq_pow_val,Units.val_one] using h
    have hf : (a-1)*(a^2+a+1)=0 := by linear_combination ha
    have hr := (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr h1)
    refine ⟨-a,?_⟩
    linear_combination hr

end OriginalCasselsRamifiedRootCriterion318

#print axioms OriginalCasselsRamifiedRootCriterion318.root_iff_residue_one
