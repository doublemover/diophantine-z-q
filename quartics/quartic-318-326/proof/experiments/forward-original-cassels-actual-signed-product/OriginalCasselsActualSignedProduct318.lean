module
public import OriginalCasselsActualLocalSystem318
import all OriginalSelectedCasselsParity318
public section

noncomputable section

namespace OriginalCasselsActualSignedProduct318

open scoped BigOperators
open OriginalCasselsActualLocalSystem318 OriginalSelectedCasselsParity318
open OriginalCasselsNaturalPrimeValuation318 OriginalSelectedCasselsLocalArithmetic318

/-- Each local factor is the sign of the signed 2-adic valuation of
the literal positive rational quotient-cardinal/kernel-cardinal ratio.
For primes this uses the already-proved local kernel cardinal 2. -/
@[expose] def supportProduct {n : ℕ} {hn : 0<n} (L : LocalSystem n hn) : ℤ :=
  L.real.sign * L.finiteSign 2 * L.finiteSign 3 *
    (∏ p ∈ n.primeFactors, L.finiteSign p)

theorem selected_actual_support (n : ℕ) (hn : 0<n) (hs : Squarefree n)
    (hr : (n:ZMod 12)=11) :
    2 ∉ n.primeFactors ∧ 3 ∉ n.primeFactors ∧
      ∀ p : ℕ, p.Prime → p≠2 → p≠3 → p ∉ n.primeFactors →
        (actualLocalSystem n hn hr).finiteSign p=1 := by
  obtain ⟨h2,h3⟩ := selected_not_dvd_small n hr
  have hc := actualExactLocalCokernels n hn hs hr
  refine ⟨fun hm => h2 (Nat.dvd_of_mem_primeFactors hm),
    fun hm => h3 (Nat.dvd_of_mem_primeFactors hm),?_⟩
  intro p hp hp2 hp3 hpN
  rw [LocalSystem.finiteSign,dif_pos hp,hc.good_size p hp hp2 hp3 hpN,ratio_sign_two_two]

/-- Exact local cardinal product for the actual selected system, not an
epsilon sign and not a Cassels–Selmer dimension identity. -/
theorem selected_actual_product (n : ℕ) (hn : 0<n) (hs : Squarefree n)
    (hr : (n:ZMod 12)=11) : supportProduct (actualLocalSystem n hn hr) = -1 := by
  let L := actualLocalSystem n hn hr
  have hc : ExactLocalCokernels L := actualExactLocalCokernels n hn hs hr
  have h3n := (selected_not_dvd_small n hr).2
  have hp : (∏ p ∈ n.primeFactors, L.finiteSign p) =
      ∏ p ∈ n.primeFactors, residue3Sign (p:ZMod 3) := by
    apply Finset.prod_congr rfl
    intro p hm
    have hprime := Nat.prime_of_mem_primeFactors hm
    have hp3 : (p:ZMod 3)≠0 := by
      intro hz
      exact h3n (dvd_trans ((ZMod.natCast_eq_zero_iff p 3).mp hz) (Nat.dvd_of_mem_primeFactors hm))
    rw [LocalSystem.finiteSign,dif_pos hprime,hc.ramified_size p hm hprime]
    by_cases h : (p:ZMod 3)=1
    · simp [h,hp3,residue3Sign,ratio_sign_two_two]
    · simp [h,hp3,residue3Sign,ratio_sign_one_two]
  have h2' : L.finiteSign 2=1 := by
    rw [LocalSystem.finiteSign,dif_pos Nat.prime_two,hc.two_size,ratio_sign_two_two]
  have h3' : L.finiteSign 3= -1 := by
    rw [LocalSystem.finiteSign,dif_pos Nat.prime_three,hc.three_size,ratio_sign_one_two]
  change L.real.sign*L.finiteSign 2*L.finiteSign 3*
    (∏ p ∈ n.primeFactors,L.finiteSign p) = -1
  rw [L.real.sign_of_cokernel.1 hc.real_size,h2',h3',hp]
  exact selected_product n hs hr

end OriginalCasselsActualSignedProduct318

#print axioms OriginalCasselsActualSignedProduct318.selected_actual_support
#print axioms OriginalCasselsActualSignedProduct318.selected_actual_product
