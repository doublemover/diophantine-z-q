module
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega
public section

namespace OriginalCasselsNaturalPrimeValuation318

theorem selected_not_dvd_small (n : ℕ) (hr : (n:ZMod 12)=11) :
    ¬2∣n ∧ ¬3∣n := by
  have h12 := (ZMod.natCast_eq_natCast_iff' n 11 12).mp hr
  have h2 : n%2=1 := by rw [←Nat.mod_mod_of_dvd n (by decide : 2∣12),h12]
  have h3 : n%3=2 := by rw [←Nat.mod_mod_of_dvd n (by decide : 3∣12),h12]
  exact ⟨fun hd => (by decide : (1:ℕ)≠0) (h2.symm.trans ((Nat.dvd_iff_mod_eq_zero).mp hd)),
    fun hd => (by decide : (2:ℕ)≠0) (h3.symm.trans ((Nat.dvd_iff_mod_eq_zero).mp hd))⟩

theorem selected_primeFactors_ne_two_three {n p : ℕ} (hn : 0<n) (hr : (n:ZMod 12)=11)
    (hm : p∈n.primeFactors) : p≠2 ∧ p≠3 := by
  have hd : p∣n := ((Nat.mem_primeFactors_of_ne_zero hn.ne').mp hm).2
  obtain ⟨h2,h3⟩ := selected_not_dvd_small n hr
  exact ⟨fun he => h2 (he ▸ hd),fun he => h3 (he ▸ hd)⟩

theorem five_le_prime_of_ne_two_three {p : ℕ} (hp : p.Prime) (h2 : p≠2) (h3 : p≠3) :
    5≤p := by
  by_contra h
  have le := hp.two_le
  have e : p=4 := by omega
  exact (by decide : ¬Nat.Prime 4) (e ▸ hp)

/-- The literal selected squarefree parameter has valuation exactly one
at every prime in its support, with no local point or isogeny input. -/
theorem squarefree_support_valuation_one (n p : ℕ) [Fact p.Prime]
    (hn : 0<n) (hs : Squarefree n) (hm : p∈n.primeFactors) : (n:ℚ_[p]).valuation=1 := by
  have hd : p∣n := ((Nat.mem_primeFactors_of_ne_zero hn.ne').mp hm).2
  have hD : ¬p^2∣n := by
    simpa only [pow_two] using (Nat.squarefree_iff_prime_squarefree.mp hs p Fact.out)
  have h1 : 1≤padicValNat p n :=
    (padicValNat_dvd_iff_le hn.ne').mp (by simpa only [pow_one] using hd)
  have h2 : ¬2≤padicValNat p n := fun h => hD ((padicValNat_dvd_iff_le hn.ne').mpr h)
  have hval : padicValNat p n=1 := by omega
  rw [Padic.valuation_natCast,hval,Nat.cast_one]

theorem selected_ramified_four_n_valuation (n p : ℕ) [Fact p.Prime]
    (hn : 0<n) (hs : Squarefree n) (hp : 5≤p) (hm : p∈n.primeFactors) :
    ((4:ℚ_[p])*(n:ℚ_[p])).valuation=1 := by
  have h4 : ¬p∣4 := fun hd => (by omega : ¬p≤4) (Nat.le_of_dvd (by decide : 0<4) hd)
  have h4v : (4:ℚ_[p]).valuation=0 := by
    change ((4:ℕ):ℚ_[p]).valuation=0
    rw [Padic.valuation_natCast,padicValNat.eq_zero_of_not_dvd h4,Nat.cast_zero]
  rw [Padic.valuation_mul (by norm_num) (Nat.cast_ne_zero.mpr hn.ne'),h4v,
    squarefree_support_valuation_one n p hn hs hm,zero_add]

end OriginalCasselsNaturalPrimeValuation318

#print axioms OriginalCasselsNaturalPrimeValuation318.selected_ramified_four_n_valuation
