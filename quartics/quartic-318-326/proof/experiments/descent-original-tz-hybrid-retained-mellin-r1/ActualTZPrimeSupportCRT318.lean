module
public import Mathlib
public section
noncomputable section
namespace ActualTZPrimeSupportCRT318
open scoped BigOperators Function

@[expose] def modulus (S : Finset ℕ) : ℕ := ∏ p∈S,p

theorem modulus_pos (S : Finset ℕ) (hp : ∀ p∈S,p.Prime) : 0<modulus S := by
  exact Finset.prod_pos fun p h => (hp p h).pos

theorem prod_dvd_iff (S : Finset ℕ) (hp : ∀ p∈S,p.Prime) (z : ℤ) :
    ((modulus S:ℕ):ℤ)∣z ↔ ∀ p∈S,(p:ℤ)∣z := by
  constructor
  · intro h p hS
    have hd : p∣modulus S := Finset.dvd_prod_of_mem (fun p : ℕ => p) hS
    exact (Int.natCast_dvd_natCast.mpr hd).trans h
  · intro h
    have hc : (S : Set ℕ).Pairwise (fun p q => IsCoprime (p:ℤ) (q:ℤ)) := by
      intro p hp' q hq' hne
      apply Int.isCoprime_iff_nat_coprime.mpr
      simpa only [Int.natAbs_natCast] using (Nat.coprime_primes (hp p hp') (hp q hq')).mpr hne
    simpa only [modulus,Nat.cast_prod] using Finset.prod_dvd_of_coprime hc h

theorem complete_modEq (S : Finset ℕ) (hp : ∀ p∈S,p.Prime) (x r : ℤ) :
    (∀ p∈S,Int.ModEq (p:ℤ) x r) ↔ Int.ModEq (modulus S:ℤ) x r := by
  simp only [Int.modEq_iff_dvd,prod_dvd_iff S hp]

/-- A CRT lift for the distinct primes in the literal support. The
empty support returns the sole modulus-one class. -/
theorem lift (S : Finset ℕ) (hp : ∀ p∈S,p.Prime) (z : ℕ→ℤ) :
    ∃ r : ℤ, ∀ p∈S,Int.ModEq (p:ℤ) r (z p) := by
  classical
  have hn : ∀ p∈S,p≠0 := fun p h => (hp p h).ne_zero
  have hc : Set.Pairwise (S : Set ℕ) (Nat.Coprime on (id : ℕ→ℕ)) := by
    intro p hp' q hq' hne
    exact (Nat.coprime_primes (hp p hp') (hp q hq')).mpr hne
  let f (p : ℕ) := (z p%(p:ℤ)).toNat
  let r := Nat.chineseRemainderOfFinset f id S hn hc
  refine ⟨(r.val:ℤ),?_⟩
  intro p h
  have H : Nat.ModEq p r.val (f p) := r.2 p h
  have he : ((r.val:ℤ)%(p:ℤ))=((f p:ℕ):ℤ)%(p:ℤ) := by
    rw [Int.ofNat_mod_ofNat,Int.ofNat_mod_ofNat]
    exact_mod_cast H
  have hE : ((f p:ℕ):ℤ)=z p%(p:ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast (hp p h).ne_zero))
  rw [hE,Int.emod_emod] at he
  exact he

end ActualTZPrimeSupportCRT318
