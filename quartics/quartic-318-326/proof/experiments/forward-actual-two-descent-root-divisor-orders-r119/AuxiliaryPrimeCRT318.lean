module
public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public section
namespace AuxiliaryPrimeCRT318
open scoped BigOperators

/-- Assemble finite unit residue conditions and construct a new prime in
that class. Coprimality of the assembled CRT class is proved from the local
unit conditions, not supplied separately. The actual local squareclasses
must still provide these residues and their unit proofs. -/
theorem prime_for_unit_residues {ι : Type*} (S : Finset ι)
    (a m : ι → ℕ) (hm : ∀ i∈S, m i≠0)
    (hpair : Set.Pairwise S (fun i j => (m i).Coprime (m j)))
    (hunit : ∀ i∈S, (a i).Coprime (m i)) (N : ℕ) :
    ∃ q : ℕ, N<q ∧ q.Prime ∧
      (∀ i∈S, Nat.ModEq (m i) q (a i)) ∧ q.Coprime (∏ i∈S, m i) := by
  let r := Nat.chineseRemainderOfFinset a m S hm hpair
  have hM : (∏ i∈S, m i)≠0 := Finset.prod_ne_zero_iff.mpr hm
  have hr : (r:ℕ).Coprime (∏ i∈S, m i) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro i hi
    change Nat.gcd (r:ℕ) (m i)=1
    rw [(r.property i hi).gcd_eq]
    exact hunit i hi
  obtain ⟨q,hN,hq,hqr⟩ := Nat.forall_exists_prime_gt_and_modEq N hM hr
  refine ⟨q,hN,hq,?_,?_⟩
  · intro i hi
    exact (hqr.of_dvd (Finset.dvd_prod_of_mem m hi)).trans (r.property i hi)
  · change Nat.gcd q (∏ i∈S, m i)=1
    rw [hqr.gcd_eq]
    exact hr

end AuxiliaryPrimeCRT318
