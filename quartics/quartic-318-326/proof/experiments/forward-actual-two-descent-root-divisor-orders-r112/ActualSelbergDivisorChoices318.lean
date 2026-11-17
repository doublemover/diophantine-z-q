module
public import ActualTruncatedSelbergEuler318
public section
noncomputable section
namespace ActualSelbergDivisorChoices318
open scoped BigOperators
open ActualSieveMultiplicativeDensity318 ActualSievePrimeMoment318 ActualTruncatedSelbergEuler318
set_option maxHeartbeats 16000000
variable {J : Type*} [Fintype J] [DecidableEq J]

lemma prime_dvd_product_iff (κ : ℤ) (γ : J → ℤ) (N excluded p : ℕ) (hp : p.Prime) :
    p∣product κ γ N excluded ↔ p∈retained κ γ N excluded := by
  constructor
  · intro hd
    obtain ⟨i,_,hi⟩ := (hp.prime.dvd_finsetProd_iff _).mp hd
    have hpi := (retained_facts κ γ N excluded i.1 i.2).1.1
    have he : p=i.1 := (hpi.dvd_iff_eq hp.ne_one).mp hi
    simpa only [he] using i.2
  · intro hm
    exact Finset.dvd_prod_of_mem (fun i : PrimeIndex κ γ N excluded => i.1)
      (Finset.mem_univ (⟨p,hm⟩ : PrimeIndex κ γ N excluded))
lemma product_pos (κ : ℤ) (γ : J → ℤ) (N excluded : ℕ) : 0<product κ γ N excluded := by
  apply Finset.prod_pos
  intro i _
  exact (retained_facts κ γ N excluded i.1 i.2).1.1.pos
lemma product_squarefree (κ : ℤ) (γ : J → ℤ) (N excluded : ℕ) :
    Squarefree (product κ γ N excluded) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i _ j _ hij
    apply Nat.coprime_iff_isRelPrime.mp
    apply (Nat.coprime_primes
      (retained_facts κ γ N excluded i.1 i.2).1.1
      (retained_facts κ γ N excluded j.1 j.2).1.1).mpr
    exact fun h => hij (Subtype.ext h)
  · intro i _
    exact (retained_facts κ γ N excluded i.1 i.2).1.1.squarefree

lemma divisor_primeFactors (κ : ℤ) (γ : J → ℤ) (N excluded d : ℕ)
    (hd : d∣product κ γ N excluded) :
    d.primeFactors=(retained κ γ N excluded).filter (fun p => p∣d) := by
  have hd0 : d≠0 := by
    intro hz
    rw [hz,zero_dvd_iff] at hd
    exact (product_pos κ γ N excluded).ne' hd
  apply Finset.ext
  intro p
  rw [Nat.mem_primeFactors_of_ne_zero hd0,Finset.mem_filter]
  constructor
  · rintro ⟨hp,hpd⟩
    exact ⟨(prime_dvd_product_iff κ γ N excluded p hp).mp (hpd.trans hd),hpd⟩
  · rintro ⟨hp,hpd⟩
    exact ⟨(retained_facts κ γ N excluded p hp).1.1,hpd⟩

/-- Every actual divisor is reconstructed by its original prime bits.
Squarefreeness is constructed from the retained prime set, not assumed
for the integer d or inferred from its size. -/
lemma actual_divisor_reconstruction (κ : ℤ) (γ : J → ℤ) (N excluded d : ℕ)
    (hd : d∣product κ γ N excluded) :
    modulus κ γ N excluded (fun i => decide (i.1∣d))=d := by
  have hs : Squarefree d := Squarefree.squarefree_of_dvd hd (product_squarefree κ γ N excluded)
  calc
    _ = ∏ p∈(retained κ γ N excluded).filter (fun p => p∣d),p := by
      simp only [modulus,decide_eq_true_eq,Finset.prod_coe_sort,Finset.prod_filter]
    _ = ∏ p∈d.primeFactors,p := by rw [divisor_primeFactors κ γ N excluded d hd]
    _ = d := Nat.prod_primeFactors_of_squarefree hs

/-- Exact equivalence with the original retained-product divisor type.
This identifies the finite Euler choices with actual integers before
any cutoff or Selberg arithmetic-function value is consumed. -/
@[expose] def divisorEquiv (κ : ℤ) (γ : J → ℤ) (N excluded : ℕ) :
    (PrimeIndex κ γ N excluded → Bool) ≃ ↥(product κ γ N excluded).divisors where
  toFun f := ⟨modulus κ γ N excluded f,Nat.mem_divisors.mpr
    ⟨modulus_dvd κ γ N excluded f,(product_pos κ γ N excluded).ne'⟩⟩
  invFun d i := decide (i.1∣d.1)
  left_inv f := by
    apply modulus_injective κ γ N excluded
    exact actual_divisor_reconstruction κ γ N excluded _ (modulus_dvd κ γ N excluded f)
  right_inv d := Subtype.ext
    (actual_divisor_reconstruction κ γ N excluded d.1 (Nat.mem_divisors.mp d.2).1)

end ActualSelbergDivisorChoices318
