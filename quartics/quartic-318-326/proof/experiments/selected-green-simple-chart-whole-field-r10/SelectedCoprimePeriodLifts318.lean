module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public section
noncomputable section
open scoped BigOperators

namespace SelectedCoprimePeriodLifts318

private theorem prime_dvd_prod_iff (p : ℕ) (hp : p.Prime) (s : Finset ℕ)
    (hs : ∀ q ∈ s, Nat.Prime q) : p ∣ ∏ q ∈ s, q ↔ p ∈ s := by
  induction s using Finset.induction_on with
  | empty => simp [hp.not_dvd_one]
  | @insert q s hq ih =>
    have hqp : q.Prime := hs q (Finset.mem_insert_self _ _)
    have hsp : ∀ u ∈ s, Nat.Prime u := fun u hu =>
      hs u (Finset.mem_insert_of_mem hu)
    rw [Finset.prod_insert hq,hp.dvd_mul,ih hsp,Finset.mem_insert,
      Nat.prime_dvd_prime_iff_eq hp hqp]

/-- Lift a primitive residue pair to genuinely coprime integers, with
no assumption that either original residue is a unit. One simultaneous
prime product preserves primes already avoided by the second component
and removes every possible common prime of the chosen integer lifts. -/
theorem coprime_lifts (N : ℕ) [NeZero N] (x y : ZMod N)
    (hprim : N.gcd (x.val.gcd y.val) = 1) :
    ∃ a b : ℕ, (a : ZMod N) = x ∧ (b : ZMod N) = y ∧ a.Coprime b := by
  let a : ℕ := x.val+N
  have ha : a ≠ 0 := by
    have hn := NeZero.ne N
    dsimp [a]
    omega
  let s := a.primeFactors.filter (fun p => ¬p ∣ y.val)
  let t : ℕ := ∏ q ∈ s, q
  have hs : ∀ q ∈ s, Nat.Prime q := by
    intro q hq
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
  have hc : a.Coprime (y.val+N*t) := by
    by_contra h
    obtain ⟨p,hp,hpa,hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    have ht : p ∣ t ↔ p ∈ s := prime_dvd_prod_iff p hp s hs
    by_cases hy : p ∣ y.val
    · have hpn : ¬p ∣ N := by
        intro hn
        have hx : p ∣ x.val := by
          have he := Nat.dvd_sub hpa hn
          simpa [a] using he
        have hd := Nat.dvd_gcd hn (Nat.dvd_gcd hx hy)
        rw [hprim] at hd
        exact hp.not_dvd_one hd
      have hpt : ¬p ∣ t := by
        intro hd
        exact (Finset.mem_filter.mp (ht.mp hd)).2 hy
      have hd : p ∣ N*t := by
        have he := Nat.dvd_sub hpb hy
        simpa [Nat.add_comm y.val (N*t)] using he
      exact hp.not_dvd_mul hpn hpt hd
    · have hpt : p ∣ t :=
        ht.mpr (Finset.mem_filter.mpr ⟨hp.mem_primeFactors hpa ha,hy⟩)
      have hprod : p ∣ N*t := dvd_mul_of_dvd_right hpt N
      apply hy
      simpa using Nat.dvd_sub hpb hprod
  refine ⟨a,y.val+N*t,?_,?_,hc⟩
  · simp [a,Nat.cast_add,ZMod.natCast_self,ZMod.natCast_zmod_val]
  · simp [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,ZMod.natCast_zmod_val]

end SelectedCoprimePeriodLifts318

#print axioms SelectedCoprimePeriodLifts318.coprime_lifts
