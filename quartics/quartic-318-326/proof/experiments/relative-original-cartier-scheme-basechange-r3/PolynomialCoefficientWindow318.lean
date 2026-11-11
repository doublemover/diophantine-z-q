module
public import FiniteLaurentVectorFiltration318
public import Mathlib.Algebra.Module.FinitePresentation
public section
noncomputable section
namespace PolynomialCoefficientWindow318
open LaurentPolynomial FiniteLaurentVectorFiltration318
open scoped BigOperators
set_option maxHeartbeats 750000
universe u
variable (R : Type u) [CommRing R] (r b : ℕ)

@[expose] def encode : (Fin r → Polynomial R) →ₗ[R] (Fin r → Fin (b+1) → R) where
  toFun p i j := (p i).coeff j.val
  map_add' p q := by ext i j; exact Polynomial.coeff_add _ _ _
  map_smul' a p := by ext i j; exact Polynomial.coeff_smul _ _ _

@[expose] def decode : (Fin r → Fin (b+1) → R) →ₗ[R] (Fin r → Polynomial R) where
  toFun w i := ∑ j : Fin (b+1), Polynomial.monomial j.val (w i j)
  map_add' w v := by
    ext i k
    simp only [Pi.add_apply,Polynomial.monomial_add,Finset.sum_add_distrib,Polynomial.coeff_add]
  map_smul' a w := by
    ext i k
    simp only [Pi.smul_apply,← Polynomial.smul_monomial,Finset.smul_sum,Polynomial.coeff_smul]

lemma coefficient_nat (p : Polynomial R) (n : ℕ) :
    (Polynomial.toLaurent p : LaurentPolynomial R).coeff (n : ℤ) = p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add,AddMonoidAlgebra.coeff_add,Polynomial.coeff_add] using congrArg₂ (·+·) hp hq
  | monomial m a =>
    rw [Polynomial.toLaurent_C_mul_T,← LaurentPolynomial.single_eq_C_mul_T]
    simp [Polynomial.coeff_monomial,AddMonoidAlgebra.coeff_single,Finsupp.single_apply,eq_comm]

/-- The original Laurent upper bound gives literal vanishing of all
higher POLYNOMIAL coefficients. No degree convention for zero is used. -/
lemma coefficients_vanish (p : Fin r → Polynomial R)
    (hp : (fun i => Polynomial.toLaurent (p i)) ∈
      (upper (b : ℤ) : Submodule R (V R (Fin r)))) :
    ∀ i : Fin r, ∀ n : ℕ, b < n → (p i).coeff n = 0 := by
  intro i n hn
  rw [← coefficient_nat R (p i) n]
  exact coeff_eq_zero hp i (n : ℤ) (by change ¬ (n : ℤ) ≤ (b : ℤ); omega)

/-- Exact finite coefficient truncation on every actually bounded
polynomial vector, including over nonreduced/noncoherent rings. -/
lemma decode_encode (p : Fin r → Polynomial R)
    (hp : (fun i => Polynomial.toLaurent (p i)) ∈
      (upper (b : ℤ) : Submodule R (V R (Fin r)))) :
    decode R r b (encode R r b p) = p := by
  ext i n
  change (∑ j : Fin (b+1), Polynomial.monomial j.val ((p i).coeff j.val)).coeff n = _
  rw [Polynomial.finset_sum_coeff]
  by_cases hn : n < b+1
  · rw [Finset.sum_eq_single (⟨n,hn⟩ : Fin (b+1))]
    · simp
    · intro j _ hj
      have hne : j.val ≠ n := by
        intro h
        apply hj
        exact Fin.ext h
      simp [Polynomial.coeff_monomial,hne]
    · simp
  · have hz := coefficients_vanish R r b p hp i n (by omega)
    rw [hz]
    apply Finset.sum_eq_zero
    intro j _
    have hne : j.val ≠ n := by have hj := j.isLt; omega
    simp [Polynomial.coeff_monomial,hne]
end PolynomialCoefficientWindow318
