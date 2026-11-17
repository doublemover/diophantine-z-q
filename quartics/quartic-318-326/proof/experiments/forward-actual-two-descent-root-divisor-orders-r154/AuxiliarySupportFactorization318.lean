module
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Tactic
public section
namespace AuxiliarySupportFactorization318
open scoped BigOperators

private theorem binary_exponent_product (J : Finset ℕ) (α : ℕ → ℕ)
    (ha : ∀ p∈J,α p≤1) :
    (∏ p∈J,p^α p) = ∏ p∈J.filter (fun p => α p=1),p := by
  classical
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p hp
  have h := ha p hp
  rcases (show α p=0 ∨ α p=1 by omega) with h0 | h1
  · simp [h0]
  · simp [h1]

/-- The coefficient factor partition and selected support product are
constructed from primeFactors and the binary exponents. Neither the
factor identity nor coprimality is a supplied input. -/
theorem selected_factorization (N : ℕ) (hs : Squarefree N)
    (h2 : ¬2∣N) (h3 : ¬3∣N) (α : ℕ → ℕ)
    (ha : ∀ p∈N.primeFactors,α p≤1) (ha3 : α 3=0) :
    let J := N.primeFactors
    let F := J.filter (fun p => α p=1)
    let G := J.filter (fun p => α p≠1)
    let P := ∏ p∈F,p
    let U := ∏ p∈G,p
    N=P*U ∧ P.Coprime U ∧
      (∏ p∈insert 2 (insert 3 J),p^α p)=2^α 2*P := by
  classical
  dsimp only
  have h2J : 2∉N.primeFactors := by
    intro h
    exact h2 (Nat.mem_primeFactors.mp h).2.1
  have h3J : 3∉N.primeFactors := by
    intro h
    exact h3 (Nat.mem_primeFactors.mp h).2.1
  have hpart :
      (∏ p∈N.primeFactors.filter (fun p => α p=1),p) *
        (∏ p∈N.primeFactors.filter (fun p => α p≠1),p)=N := by
    rw [Finset.prod_filter_mul_prod_filter_not,
      Nat.prod_primeFactors_of_squarefree hs]
  refine ⟨hpart.symm,?_,?_⟩
  · exact Nat.coprime_of_squarefree_mul (hpart.symm ▸ hs)
  · rw [Finset.prod_insert (by simp [h2J]),Finset.prod_insert h3J,
      ha3,pow_zero,one_mul,binary_exponent_product _ α ha]

/-- Instantiate the partition at the actual signed squarefree coefficient.
The congruence C=1 modulo24 proves the required exclusion of2 and3;
the separate checked local norm argument supplies alpha(3)=0. -/
theorem actual_coefficient_factorization (C : ℤ) (hC : C%24=1)
    (hs : Squarefree C) (α : ℕ → ℕ)
    (ha : ∀ p∈C.natAbs.primeFactors,α p≤1) (ha3 : α 3=0) :
    let J := C.natAbs.primeFactors
    let P := ∏ p∈J.filter (fun p => α p=1),p
    let U := ∏ p∈J.filter (fun p => α p≠1),p
    C.natAbs=P*U ∧ P.Coprime U ∧
      (∏ p∈insert 2 (insert 3 J),p^α p)=2^α 2*P := by
  have h2 : ¬2∣C.natAbs := by
    intro h
    have hd : (2:ℤ)∣C := Int.natAbs_dvd_natAbs.mp (by simpa using h)
    have hz := Int.dvd_iff_emod_eq_zero.mp hd
    omega
  have h3 : ¬3∣C.natAbs := by
    intro h
    have hd : (3:ℤ)∣C := Int.natAbs_dvd_natAbs.mp (by simpa using h)
    have hz := Int.dvd_iff_emod_eq_zero.mp hd
    omega
  exact selected_factorization C.natAbs (Int.squarefree_natAbs.mpr hs)
    h2 h3 α ha ha3

end AuxiliarySupportFactorization318
