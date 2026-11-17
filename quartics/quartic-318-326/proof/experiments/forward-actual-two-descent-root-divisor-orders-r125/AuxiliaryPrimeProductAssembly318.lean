module
public import AuxiliaryJacobiProduct318
public import AuxiliarySignedReciprocity318
public section
namespace AuxiliaryPrimeProductAssembly318

/-- Equality at every prime divisor gives equality of the full Jacobi
product, including repeated prime factors. No squarefreeness is required. -/
theorem jacobi_eq_of_prime_divisors (a b : ℤ) (n : ℕ) (hn : n≠0)
    (h : ∀ p, p.Prime → p∣n → jacobiSym a p=jacobiSym b p) :
    jacobiSym a n=jacobiSym b n := by
  have hp : ∀ p∈n.primeFactorsList,p≠0 := fun p hm =>
    (Nat.prime_of_mem_primeFactorsList hm).ne_zero
  rw [←Nat.prod_primeFactorsList hn,jacobiSym.list_prod_right hp,
    jacobiSym.list_prod_right hp]
  congr 1
  apply List.map_congr_left
  intro p hm
  exact h p (Nat.prime_of_mem_primeFactorsList hm) (Nat.dvd_of_mem_primeFactorsList hm)

/-- Assemble the actual two collections of bad-prime character identities.
The local identities are still inputs here; the full Jacobi product is not.
The real-compatible sign is precisely the one in the checked reciprocity
calculation, including negative normalized C and empty prime collections. -/
theorem product_one_of_local_identities (P U q α : ℕ)
    (hP : Odd P) (hU : Odd U) (hcop : (U:ℤ).gcd P=1)
    (ε σ : ℤ) (hσ : σ=1 ∨ σ= -1)
    (hsign : (ε=1 ∧ (P*U)%4=1) ∨
      (ε= -1 ∧ (P*U)%4=3 ∧ σ= -1))
    (h2U : jacobiSym 2 U=1)
    (hselected : ∀ p, p.Prime → p∣P →
      jacobiSym (q:ℤ) p=jacobiSym (ε*σ*(U:ℤ)) p)
    (hunselected : ∀ p, p.Prime → p∣U →
      jacobiSym (q:ℤ) p=jacobiSym (-σ*(2:ℤ)^α*(P:ℤ)) p) :
    jacobiSym (q:ℤ) (P*U)=1 := by
  have hqP := jacobi_eq_of_prime_divisors (q:ℤ) (ε*σ*(U:ℤ)) P
    hP.pos.ne' hselected
  have hqU := jacobi_eq_of_prime_divisors (q:ℤ) (-σ*(2:ℤ)^α*(P:ℤ)) U
    hU.pos.ne' hunselected
  rw [jacobiSym.mul_left] at hqP
  simp only [jacobiSym.mul_left,jacobiSym.pow_left,h2U,one_pow,mul_one] at hqU
  rw [jacobiSym.mul_right' (q:ℤ) hP.pos.ne' hU.pos.ne',hqP,hqU]
  calc
    _=jacobiSym (ε*σ) P*jacobiSym (-σ) U*
        jacobiSym (U:ℤ) P*jacobiSym (P:ℤ) U := by ring
    _=1 := AuxiliaryJacobiProduct318.real_compatible_sign_product
      P U hP hU hcop ε σ hσ hsign

/-- New-prime compatibility from the local bad-prime identities, rather
than assuming the full product conclusion. The construction of q and the
actual local identities remain separate obligations. -/
theorem square_six_coefficient (C : ℤ) (P U q α : ℕ) [Fact q.Prime]
    (hC : C%24=1) (hN : C.natAbs=P*U) (hq : Odd q)
    (hP : Odd P) (hU : Odd U) (hcop : (U:ℤ).gcd P=1)
    (ε σ : ℤ) (hσ : σ=1 ∨ σ= -1)
    (hsign : (ε=1 ∧ (P*U)%4=1) ∨
      (ε= -1 ∧ (P*U)%4=3 ∧ σ= -1))
    (h2U : jacobiSym 2 U=1) (h6q : jacobiSym 6 q=1)
    (hselected : ∀ p, p.Prime → p∣P →
      jacobiSym (q:ℤ) p=jacobiSym (ε*σ*(U:ℤ)) p)
    (hunselected : ∀ p, p.Prime → p∣U →
      jacobiSym (q:ℤ) p=jacobiSym (-σ*(2:ℤ)^α*(P:ℤ)) p) :
    IsSquare ((6*C:ℤ):ZMod q) := by
  apply AuxiliarySignedReciprocity318.square_six_coefficient_of_product C q hC hq h6q
  rw [hN]
  exact product_one_of_local_identities P U q α hP hU hcop ε σ hσ hsign h2U
    hselected hunselected

end AuxiliaryPrimeProductAssembly318
